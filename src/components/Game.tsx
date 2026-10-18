"use client"

import { useCallback, useEffect, useRef, useState } from "react"
import { Application, Assets, Container, Rectangle, Sprite, Texture, Ticker } from "pixi.js"

type GameState = "menu" | "playing" | "gameover"

type Pipe = {
  container: Container
  x: number
  gapOffset: number
  scored: boolean
}

type Box = {
  minX: number
  maxX: number
  minY: number
  maxY: number
}

type GameCallbacks = {
  onReady: () => void
  onScore: () => void
  onGameOver: () => void
}

const ASSETS = {
  bird: "/bird.png",
  pipe: "/pipe.png",
}

const RENDER = {
  backgroundAlpha: 0,
  maxResolution: 2,
}

const WORLD = {
  width: 6,
  height: 8,
  offsetY: -1.5,
  spawnMargin: 0.5,
}

const PHYSICS = {
  gravity: -9.8,
  jumpVelocity: 4,
  maxFrameDelta: 0.05,
}

const BIRD = {
  x: -2,
  width: 0.8,
  height: 0.62,
  tiltFactor: 0.15,
  minTilt: -0.5,
  maxTilt: 0.8,
}

const PIPE = {
  width: 0.65,
  height: 1.45,
  speed: 2,
  spawnInterval: 2,
  extensionHeight: 50,
  gapSize: 2.2,
  gapCenterY: 0.55,
  gapRandomRange: 1.4,
  bodySliceRatio: 0.2,
}

const PIPE_SPACING = PIPE.speed * PIPE.spawnInterval

const COLLISION_MARGIN = {
  x: 0.05,
  y: 0.05,
}

const SPRITE_ANCHOR = 0.5
const HALF_TURN = Math.PI
const MS_IN_SECOND = 1000
const JUMP_KEY = "Space"

const CANVAS_STYLE: Partial<CSSStyleDeclaration> = {
  display: "block",
  width: "100%",
  height: "100%",
  touchAction: "none",
}

const LABELS = {
  play: "Play",
  restart: "Restart",
  gameOver: "Game Over",
}

const ROOT_STYLE: React.CSSProperties = {
  width: "100%",
  height: "100dvh",
  position: "relative",
  zIndex: 0,
  touchAction: "none",
  overscrollBehavior: "none",
  userSelect: "none",
  WebkitUserSelect: "none",
}

const HOST_STYLE: React.CSSProperties = {
  position: "absolute",
  inset: 0,
}

const CENTERED_STYLE: React.CSSProperties = {
  position: "absolute",
  top: "50%",
  left: "50%",
  transform: "translate(-50%, -50%)",
}

const BUTTON_STYLE: React.CSSProperties = {
  ...CENTERED_STYLE,
  fontSize: "clamp(1.1rem, 5vw, 1.5rem)",
}

const GAME_OVER_TITLE_STYLE: React.CSSProperties = {
  fontSize: "clamp(1.5rem, 7vw, 2rem)",
}

const SCORE_STYLE: React.CSSProperties = {
  position: "absolute",
  top: "80px",
  left: "50%",
  transform: "translateX(-50%)",
  fontSize: "clamp(1.75rem, 8vw, 2.25rem)",
}

const ROOT_CLASS = "bg-[var(--light-blue)]"
const GAME_OVER_CLASS = "flex flex-col items-center gap-4 px-4 text-center"
const GAME_OVER_TITLE_CLASS = "font-bold text-white mb-24"
const SCORE_CLASS = "font-bold text-white pointer-events-none"
const BUTTON_CLASS =
  "bg-[#F8C82E] px-6 py-2 font-bold border-2 rounded-full shadow-[0_2px_0_0_#000] hover:shadow-[0_0px_0_0_#000] hover:translate-y-[2px] transition-all duration-150 ease-out cursor-pointer flex items-center gap-2"

const PLAY_ICON = {
  size: 20,
  viewBox: "0 0 43 54",
  path: "M0.5 51.861V1.50235C0.5 0.698763 1.39986 0.223396 2.06364 0.676329L41.6977 27.7208C42.3034 28.134 42.2731 29.037 41.6411 29.4087L2.00702 52.7229C1.34039 53.115 0.5 52.6344 0.5 51.861Z",
  color: "black",
}

const worldToScreenY = (y: number) => -y

const clamp = (value: number, min: number, max: number) => Math.min(max, Math.max(min, value))

const randomGapOffset = () => (Math.random() * 2 - 1) * PIPE.gapRandomRange

const getGapEdges = (gapOffset: number) => ({
  bottomEdgeY: PIPE.gapCenterY + gapOffset - PIPE.gapSize / 2,
  topEdgeY: PIPE.gapCenterY + gapOffset + PIPE.gapSize / 2,
})

const applyCollisionMargin = (box: Box): Box => ({
  minX: box.minX + COLLISION_MARGIN.x,
  maxX: box.maxX - COLLISION_MARGIN.x,
  minY: box.minY + COLLISION_MARGIN.y,
  maxY: box.maxY - COLLISION_MARGIN.y,
})

const boxesIntersect = (a: Box, b: Box) =>
  a.minX <= b.maxX && a.maxX >= b.minX && a.minY <= b.maxY && a.maxY >= b.minY

function createSprite(texture: Texture, width: number, height: number): Sprite {
  const sprite = new Sprite(texture)
  sprite.anchor.set(SPRITE_ANCHOR)
  sprite.width = width
  sprite.height = height
  return sprite
}

function createPipeBodyTexture(texture: Texture): Texture {
  const { x, y, width, height } = texture.frame
  const sliceHeight = height * PIPE.bodySliceRatio

  return new Texture({
    source: texture.source,
    frame: new Rectangle(x, y + height - sliceHeight, width, sliceHeight),
  })
}

class FlappyGame {
  private app = new Application()
  private world = new Container()
  private group = new Container()
  private pipeLayer = new Container()
  private bird!: Sprite
  private pipeTexture!: Texture
  private pipeBodyTexture!: Texture

  private pipes: Pipe[] = []
  private state: GameState = "menu"
  private view = { width: WORLD.width, height: WORLD.height }

  private birdY = 0
  private velocity = 0
  private tilt = 0
  private spawnTimer = 0

  private appInitialized = false
  private ready = false
  private destroyed = false

  private host: HTMLElement
  private callbacks: GameCallbacks

  constructor(host: HTMLElement, callbacks: GameCallbacks) {
    this.host = host
    this.callbacks = callbacks
    void this.init()
  }

  start() {
    if (!this.ready) return
    this.resetBird()
    this.startRound()
    this.state = "playing"
  }

  jump() {
    if (this.state !== "playing") return
    this.velocity = PHYSICS.jumpVelocity
  }

  destroy() {
    this.destroyed = true
    if (this.appInitialized) {
      this.app.destroy(true, { children: true })
    }
  }

  private get spawnX() {
    return this.view.width / 2 + WORLD.spawnMargin
  }

  private get despawnX() {
    return -this.view.width / 2 - WORLD.spawnMargin
  }

  private get floorY() {
    return -this.view.height / 2 - WORLD.offsetY
  }

  private async init() {
    await this.app.init({
      resizeTo: this.host,
      backgroundAlpha: RENDER.backgroundAlpha,
      antialias: true,
      autoDensity: true,
      resolution: Math.min(window.devicePixelRatio || 1, RENDER.maxResolution),
    })
    this.appInitialized = true

    if (this.destroyed) {
      this.app.destroy(true, { children: true })
      return
    }

    this.mountCanvas()

    const [birdTexture, pipeTexture] = await Promise.all([
      Assets.load<Texture>(ASSETS.bird),
      Assets.load<Texture>(ASSETS.pipe),
    ])
    if (this.destroyed) return

    this.pipeTexture = pipeTexture
    this.pipeBodyTexture = createPipeBodyTexture(pipeTexture)
    this.buildScene(birdTexture)
    this.layout()
    this.app.renderer.on("resize", this.layout)

    this.resetBird()
    this.startRound()

    this.app.ticker.add((ticker: Ticker) => {
      this.update(Math.min(ticker.deltaMS / MS_IN_SECOND, PHYSICS.maxFrameDelta))
    })

    this.ready = true
    this.callbacks.onReady()
  }

  private mountCanvas() {
    Object.assign(this.app.canvas.style, CANVAS_STYLE)
    this.host.appendChild(this.app.canvas)
  }

  private buildScene(birdTexture: Texture) {
    this.bird = createSprite(birdTexture, BIRD.width, BIRD.height)
    this.bird.x = BIRD.x

    this.group.addChild(this.pipeLayer, this.bird)
    this.world.addChild(this.group)
    this.app.stage.addChild(this.world)
  }

  private layout = () => {
    const { width, height } = this.app.screen
    const zoom = Math.min(width / WORLD.width, height / WORLD.height)

    this.view = { width: width / zoom, height: height / zoom }
    this.world.position.set(width / 2, height / 2)
    this.world.scale.set(zoom)
    this.group.position.set(0, worldToScreenY(WORLD.offsetY))
  }

  private resetBird() {
    this.birdY = 0
    this.velocity = 0
    this.tilt = 0
    this.renderBird()
  }

  private renderBird() {
    this.bird.y = worldToScreenY(this.birdY)
    this.bird.rotation = -this.tilt
  }

  private startRound() {
    this.clearPipes()

    const positions = this.getInitialPipePositions()
    const lastX = positions[positions.length - 1]
    const distanceToNextSpawn = PIPE_SPACING + lastX - this.spawnX

    this.spawnTimer = PIPE.spawnInterval - distanceToNextSpawn / PIPE.speed
    positions.forEach((x) => this.spawnPipe(x))
  }

  private getInitialPipePositions() {
    const positions: number[] = []
    for (let x = 0; x < this.spawnX; x += PIPE_SPACING) {
      positions.push(x)
    }
    return positions
  }

  private spawnPipe(x: number) {
    const gapOffset = randomGapOffset()
    const { bottomEdgeY, topEdgeY } = getGapEdges(gapOffset)

    const bottom = createSprite(this.pipeTexture, PIPE.width, PIPE.height)
    bottom.y = worldToScreenY(bottomEdgeY - PIPE.height / 2)

    const bottomBody = createSprite(this.pipeBodyTexture, PIPE.width, PIPE.extensionHeight)
    bottomBody.y = worldToScreenY(bottomEdgeY - PIPE.height - PIPE.extensionHeight / 2)

    const top = createSprite(this.pipeTexture, PIPE.width, PIPE.height)
    top.rotation = HALF_TURN
    top.y = worldToScreenY(topEdgeY + PIPE.height / 2)

    const topBody = createSprite(this.pipeBodyTexture, PIPE.width, PIPE.extensionHeight)
    topBody.rotation = HALF_TURN
    topBody.y = worldToScreenY(topEdgeY + PIPE.height + PIPE.extensionHeight / 2)

    const container = new Container()
    container.x = x
    container.addChild(bottomBody, bottom, topBody, top)
    this.pipeLayer.addChild(container)

    this.pipes.push({ container, x, gapOffset, scored: false })
  }

  private removePipe(index: number) {
    this.pipes[index].container.destroy({ children: true })
    this.pipes.splice(index, 1)
  }

  private clearPipes() {
    while (this.pipes.length > 0) {
      this.removePipe(this.pipes.length - 1)
    }
  }

  private update(delta: number) {
    if (this.state !== "playing") return

    this.updateBird(delta)
    this.updatePipes(delta)
    this.spawnPipesIfNeeded(delta)

    if (this.hasFallen() || this.hasCollided()) {
      this.finishGame()
    }
  }

  private updateBird(delta: number) {
    this.velocity += PHYSICS.gravity * delta
    this.birdY += this.velocity * delta
    this.tilt = clamp(this.velocity * BIRD.tiltFactor, BIRD.minTilt, BIRD.maxTilt)
    this.renderBird()
  }

  private updatePipes(delta: number) {
    for (let i = this.pipes.length - 1; i >= 0; i--) {
      const pipe = this.pipes[i]
      pipe.x -= PIPE.speed * delta
      pipe.container.x = pipe.x

      this.scoreIfPassed(pipe)

      if (pipe.x < this.despawnX) {
        this.removePipe(i)
      }
    }
  }

  private scoreIfPassed(pipe: Pipe) {
    if (pipe.scored || pipe.x > BIRD.x) return
    pipe.scored = true
    this.callbacks.onScore()
  }

  private spawnPipesIfNeeded(delta: number) {
    this.spawnTimer += delta
    if (this.spawnTimer < PIPE.spawnInterval) return

    this.spawnTimer -= PIPE.spawnInterval
    this.spawnPipe(this.spawnX - this.spawnTimer * PIPE.speed)
  }

  private hasFallen() {
    return this.birdY < this.floorY
  }

  private hasCollided() {
    const birdBox = this.getBirdBox()

    return this.pipes
      .filter((pipe) => this.isNearBird(pipe))
      .some((pipe) => this.getPipeBoxes(pipe).some((box) => boxesIntersect(birdBox, box)))
  }

  private isNearBird(pipe: Pipe) {
    return Math.abs(pipe.x - BIRD.x) <= PIPE.width + BIRD.width
  }

  private getBirdBox(): Box {
    const cos = Math.abs(Math.cos(this.tilt))
    const sin = Math.abs(Math.sin(this.tilt))
    const halfWidth = (cos * BIRD.width + sin * BIRD.height) / 2
    const halfHeight = (sin * BIRD.width + cos * BIRD.height) / 2

    return applyCollisionMargin({
      minX: BIRD.x - halfWidth,
      maxX: BIRD.x + halfWidth,
      minY: this.birdY - halfHeight,
      maxY: this.birdY + halfHeight,
    })
  }

  private getPipeBoxes(pipe: Pipe): Box[] {
    const { bottomEdgeY, topEdgeY } = getGapEdges(pipe.gapOffset)
    const minX = pipe.x - PIPE.width / 2
    const maxX = pipe.x + PIPE.width / 2

    return [
      applyCollisionMargin({
        minX,
        maxX,
        minY: bottomEdgeY - PIPE.height - PIPE.extensionHeight,
        maxY: bottomEdgeY,
      }),
      applyCollisionMargin({
        minX,
        maxX,
        minY: topEdgeY,
        maxY: topEdgeY + PIPE.height + PIPE.extensionHeight,
      }),
    ]
  }

  private finishGame() {
    this.state = "gameover"
    this.callbacks.onGameOver()
  }
}

function useFlappyGame() {
  const hostRef = useRef<HTMLDivElement>(null)
  const gameRef = useRef<FlappyGame | null>(null)
  const [gameState, setGameState] = useState<GameState>("menu")
  const [score, setScore] = useState(0)
  const [ready, setReady] = useState(false)

  useEffect(() => {
    if (!hostRef.current) return

    const game = new FlappyGame(hostRef.current, {
      onReady: () => setReady(true),
      onScore: () => setScore((current) => current + 1),
      onGameOver: () => setGameState("gameover"),
    })
    gameRef.current = game

    function handleKeyDown(event: KeyboardEvent) {
      if (event.code !== JUMP_KEY) return
      event.preventDefault()
      game.jump()
    }

    window.addEventListener("keydown", handleKeyDown)

    return () => {
      window.removeEventListener("keydown", handleKeyDown)
      game.destroy()
      gameRef.current = null
    }
  }, [])

  const start = useCallback(() => {
    setScore(0)
    setGameState("playing")
    gameRef.current?.start()
  }, [])

  const jump = useCallback(() => {
    gameRef.current?.jump()
  }, [])

  return { hostRef, gameState, score, ready, start, jump }
}

function PlayIcon() {
  return (
    <svg
      width={PLAY_ICON.size}
      height={PLAY_ICON.size}
      viewBox={PLAY_ICON.viewBox}
      fill="none"
      xmlns="http://www.w3.org/2000/svg"
    >
      <path d={PLAY_ICON.path} fill={PLAY_ICON.color} stroke={PLAY_ICON.color} />
    </svg>
  )
}

function ActionButton({ label, showIcon = false, onClick }: {
  label: string
  showIcon?: boolean
  onClick: () => void
}) {
  function handlePointerDown(event: React.PointerEvent) {
    event.stopPropagation()
    onClick()
  }

  return (
    <button onPointerDown={handlePointerDown} style={BUTTON_STYLE} className={BUTTON_CLASS}>
      {showIcon && <PlayIcon />}
      {label}
    </button>
  )
}

function GameOverScreen({ onRestart }: { onRestart: () => void }) {
  return (
    <div style={CENTERED_STYLE} className={GAME_OVER_CLASS}>
      <span style={GAME_OVER_TITLE_STYLE} className={GAME_OVER_TITLE_CLASS}>
        {LABELS.gameOver}
      </span>
      <ActionButton label={LABELS.restart} onClick={onRestart} />
    </div>
  )
}

function Game() {
  const { hostRef, gameState, score, ready, start, jump } = useFlappyGame()

  return (
    <div
      style={ROOT_STYLE}
      className={ROOT_CLASS}
      onPointerDown={jump}
      onContextMenu={(event) => event.preventDefault()}
    >
      <div ref={hostRef} style={HOST_STYLE} />

      {ready && gameState === "menu" && (
        <ActionButton label={LABELS.play} showIcon onClick={start} />
      )}

      {gameState === "gameover" && <GameOverScreen onRestart={start} />}

      {gameState === "playing" && (
        <div style={SCORE_STYLE} className={SCORE_CLASS}>
          {score}
        </div>
      )}
    </div>
  )
}

export default Game
