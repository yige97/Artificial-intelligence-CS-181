# multiAgents.py
# --------------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
# 
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).


from util import manhattanDistance
from game import Directions
import random, util

from game import Agent

class ReflexAgent(Agent):
    """
      A reflex agent chooses an action at each choice point by examining
      its alternatives via a state evaluation function.

      The code below is provided as a guide.  You are welcome to change
      it in any way you see fit, so long as you don't touch our method
      headers.
    """


    def getAction(self, gameState):
        """
        You do not need to change this method, but you're welcome to.

        getAction chooses among the best options according to the evaluation function.

        Just like in the previous project, getAction takes a GameState and returns
        some Directions.X for some X in the set {North, South, West, East, Stop}
        """
        # Collect legal moves and successor states
        legalMoves = gameState.getLegalActions()

        # Choose one of the best actions
        scores = [self.evaluationFunction(gameState, action) for action in legalMoves]
        bestScore = max(scores)
        bestIndices = [index for index in range(len(scores)) if scores[index] == bestScore]
        chosenIndex = random.choice(bestIndices) # Pick randomly among the best

        "Add more of your code here if you want to"

        return legalMoves[chosenIndex]

    def evaluationFunction(self, currentGameState, action):
        """
        Design a better evaluation function here.

        The evaluation function takes in the current and proposed successor
        GameStates (pacman.py) and returns a number, where higher numbers are better.

        The code below extracts some useful information from the state, like the
        remaining food (newFood) and Pacman position after moving (newPos).
        newScaredTimes holds the number of moves that each ghost will remain
        scared because of Pacman having eaten a power pellet.

        Print out these variables to see what you're getting, then combine them
        to create a masterful evaluation function.
        """
        # Useful information you can extract from a GameState (pacman.py)
        successorGameState = currentGameState.generatePacmanSuccessor(action)
        newPos = successorGameState.getPacmanPosition()
        newFood = successorGameState.getFood()
        newGhostStates = successorGameState.getGhostStates()
        newScaredTimes = [ghostState.scaredTimer for ghostState in newGhostStates]

        
        return successorGameState.getScore()

def scoreEvaluationFunction(currentGameState):
    """
      This default evaluation function just returns the score of the state.
      The score is the same one displayed in the Pacman GUI.

      This evaluation function is meant for use with adversarial search agents
      (not reflex agents).
    """
    return currentGameState.getScore()

class MultiAgentSearchAgent(Agent):
    """
      This class provides some common elements to all of your
      multi-agent searchers.  Any methods defined here will be available
      to the MinimaxPacmanAgent, AlphaBetaPacmanAgent & ExpectimaxPacmanAgent.

      You *do not* need to make any changes here, but you can if you want to
      add functionality to all your adversarial search agents.  Please do not
      remove anything, however.

      Note: this is an abstract class: one that should not be instantiated.  It's
      only partially specified, and designed to be extended.  Agent (game.py)
      is another abstract class.
    """

    def __init__(self, evalFn = 'scoreEvaluationFunction', depth = '2'):
        self.index = 0 # Pacman is always agent index 0
        self.evaluationFunction = util.lookup(evalFn, globals())
        self.depth = int(depth)

class MinimaxAgent(MultiAgentSearchAgent):
    """
      Your minimax agent (question 1)
    """

    def getAction(self, gameState):
        """
          Returns the minimax action from the current gameState using self.depth
          and self.evaluationFunction.

          Here are some method calls that might be useful when implementing minimax.

          gameState.getLegalActions(agentIndex):
            Returns a list of legal actions for an agent
            agentIndex=0 means Pacman, ghosts are >= 1

          gameState.generateSuccessor(agentIndex, action):
            Returns the successor game state after an agent takes an action

          gameState.getNumAgents():
            Returns the total number of agents in the game

          gameState.isWin():
            Returns whether or not the game state is a winning state

          gameState.isLose():
            Returns whether or not the game state is a losing state
        """
        "*** YOUR CODE HERE ***"
        def minimax(gameState, depth, agentIndex):
          if agentIndex == gameState.getNumAgents():
            return minimax(gameState, depth + 1, 0)

          if gameState.isWin() or gameState.isLose() or depth == self.depth or gameState.getLegalActions(agentIndex) == 0:
            return self.evaluationFunction(gameState)

          successors = []
          legalActions = gameState.getLegalActions(agentIndex)
          for action in legalActions:
            successors.append(minimax(gameState.generateSuccessor(agentIndex, action), depth, agentIndex + 1))
          
          if agentIndex == 0:
            return max(successors)
          else:
            return min(successors)

        actions = gameState.getLegalActions(0)
        return max(actions, key = lambda x: minimax(gameState.generateSuccessor(0, x), 0, 1))

class AlphaBetaAgent(MultiAgentSearchAgent):
    """
      Your minimax agent with alpha-beta pruning (question 2)
    """
    def maxiMize(self, gameState, depth, alpha, beta):
      if gameState.isWin() or gameState.isLose():
        return self.evaluationFunction(gameState)
      Val = float("-inf")
      actions = gameState.getLegalActions(0)
      bestAct = Directions.STOP
      for action in actions:
        successor = gameState.generateSuccessor(0, action)
        tempVal = self.miniMize(successor, depth, 1, alpha, beta)
        if tempVal > Val:
          Val = tempVal
          bestAct = action

        if Val > beta:
          return Val
        alpha = max(alpha, Val)

      if depth > 1:
        return Val

      return bestAct

    def miniMize(self, gameState, depth, agentIndex, alpha, beta):
      if gameState.isWin() or gameState.isLose():
        return self.evaluationFunction(gameState)
      Val = float("inf")
      actions = gameState.getLegalActions(agentIndex)
      for action in actions:
        successor = gameState.generateSuccessor(agentIndex, action)
        if agentIndex == gameState.getNumAgents() - 1:
          if depth == self.depth:
            tempVal = self.evaluationFunction(successor)
          else:
            tempVal = self.maxiMize(successor, depth + 1, alpha, beta)
        else:
          tempVal = self.miniMize(successor, depth, agentIndex + 1, alpha, beta)
        if tempVal < Val:
          Val = tempVal

        if Val < alpha:
          return Val
        beta = min(beta, Val)
      return Val

    def getAction(self, gameState):
        """
          Returns the minimax action using self.depth and self.evaluationFunction
        """
        Alpha = float("-inf")
        Beta  = float("inf")
        return self.maxiMize(gameState, 1, Alpha, Beta)
        

class ExpectimaxAgent(MultiAgentSearchAgent):
    """
      Your expectimax agent (question 3)
    """

    def getAction(self, gameState):
        """
          Returns the expectimax action using self.depth and self.evaluationFunction

          All ghosts should be modeled as choosing uniformly at random from their
          legal moves.
        """
        def expectimax(gameState, depth, agentIndex):
          if agentIndex == gameState.getNumAgents():
            return expectimax(gameState, depth + 1, 0)
          if gameState.isWin() or gameState.isLose() or depth == self.depth or gameState.getLegalActions(agentIndex) == 0:
            return self.evaluationFunction(gameState)
          
          successors = []
          legalActions = gameState.getLegalActions(agentIndex)
          for action in legalActions:
            successors.append(expectimax(gameState.generateSuccessor(agentIndex, action), depth, agentIndex + 1))

          if agentIndex  == 0:
            return max(successors)
          else:
            return sum(successors)/len(successors)

        actions = gameState.getLegalActions(0)
        return max(actions, key = lambda x: expectimax(gameState.generateSuccessor(0, x), 0, 1))
        

def betterEvaluationFunction(currentGameState):
    """
      Your extreme ghost-hunting, pellet-nabbing, food-gobbling, unstoppable
      evaluation function (question 4).

      DESCRIPTION: <write something here so we know what you did>
    """
    newPos = currentGameState.getPacmanPosition()
    newFood = currentGameState.getFood()
    newGhostStates = currentGameState.getGhostStates()
    newScaredTimes = [ghostState.scaredTimer for ghostState in newGhostStates]

    value = currentGameState.getScore()

    food_list = newFood.asList()
    food_list = sorted(food_list, key = lambda x: manhattanDistance(newPos, x))
    closestFood = 0
    if len(food_list) != 0:
      closestFood = manhattanDistance(newPos, food_list[0])

    nearestGhost = float("inf")
    ghostVal = 0
    for ghost in newGhostStates:
      ghostPos = ghost.getPosition()
      md = manhattanDistance(newPos, ghostPos)
      if md > 0:
        if ghost.scaredTimer == 0:
          ghostVal = ghostVal - 10.0 / md
        else:
          ghostVal = ghostVal + 100.0 / md

    if closestFood != 0:
      value = value + ghostVal + 10 / closestFood
    else:
      value = value + ghostVal

    return value


# Abbreviation
better = betterEvaluationFunction

