# logicPlan.py
# ------------
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


"""
In logicPlan.py, you will implement logic planning methods which are called by
Pacman agents (in logicAgents.py).
"""

import util
import sys
import logic
import game


pacman_str = 'P'
ghost_pos_str = 'G'
ghost_east_str = 'GE'
pacman_alive_str = 'PA'

class PlanningProblem:
    """
    This class outlines the structure of a planning problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the planning problem.
        """
        util.raiseNotDefined()

    def getGhostStartStates(self):
        """
        Returns a list containing the start state for each ghost.
        Only used in problems that use ghosts (FoodGhostPlanningProblem)
        """
        util.raiseNotDefined()
        
    def getGoalState(self):
        """
        Returns goal state for problem. Note only defined for problems that have
        a unique goal state such as PositionPlanningProblem
        """
        util.raiseNotDefined()

def tinyMazePlan(problem):
    """
    Returns a sequence of moves that solves tinyMaze.  For any other maze, the
    sequence of moves will be incorrect, so only use this for tinyMaze.
    """
    from game import Directions
    s = Directions.SOUTH
    w = Directions.WEST
    return  [s, s, w, s, w, w, s, w]

def sentence1():
    """Returns a logic.Expr instance that encodes that the following expressions are all true.
    
    A or B
    (not A) if and only if ((not B) or C)
    (not A) or (not B) or C
    """
    A = logic.Expr('A')
    B = logic.Expr('B')
    C = logic.Expr('C')
    First = A | B
    Second = ~A % (~B | C)
    Third = logic.disjoin(~A, ~B, C)
    return logic.conjoin(First, Second, Third)

def sentence2():
    """Returns a logic.Expr instance that encodes that the following expressions are all true.
    
    C if and only if (B or D)
    A implies ((not B) and (not D))
    (not (B and (not C))) implies A
    (not D) implies C
    """
    A = logic.Expr('A')
    B = logic.Expr('B')
    C = logic.Expr('C')
    D = logic.Expr('D')

    First = C % (B | D)
    Second = A >> (~B & ~D)
    Third = ~(B & ~C) >> A
    Fourth = ~D >> C

    return logic.conjoin(First, Second, Third, Fourth)

def sentence3():
    """Using the symbols WumpusAlive[1], WumpusAlive[0], WumpusBorn[0], and WumpusKilled[0],
    created using the logic.PropSymbolExpr constructor, return a logic.PropSymbolExpr
    instance that encodes the following English sentences (in this order):

    The Wumpus is alive at time 1 if and only if the Wumpus was alive at time 0 and it was
    not killed at time 0 or it was not alive and time 0 and it was born at time 0.

    The Wumpus cannot both be alive at time 0 and be born at time 0.

    The Wumpus is born at time 0.
    """
    A = logic.PropSymbolExpr("WumpusAlive[1]")
    B = logic.PropSymbolExpr("WumpusAlive[0]")
    C = logic.PropSymbolExpr("WumpusBorn[0]")
    D = logic.PropSymbolExpr("WumpusKilled[0]")

    state_alive = A % ((B & ~D) | (~B & C))
    state_cannot = ~(B & C)

    return logic.conjoin(state_alive, state_cannot, C)

def findModel(sentence):
    """Given a propositional logic sentence (i.e. a logic.Expr instance), returns a satisfying
    model if one exists. Otherwise, returns False.
    """
    cnf = logic.to_cnf(sentence)
    model = logic.pycoSAT(cnf)
    if str(model) == "False":
        return False
    return model


def atLeastOne(literals) :
    """
    Given a list of logic.Expr literals (i.e. in the form A or ~A), return a single 
    logic.Expr instance in CNF (conjunctive normal form) that represents the logic 
    that at least one of the literals in the list is true.
    >>> A = logic.PropSymbolExpr('A');
    >>> B = logic.PropSymbolExpr('B');
    >>> symbols = [A, B]
    >>> atleast1 = atLeastOne(symbols)
    >>> model1 = {A:False, B:False}
    >>> print logic.pl_true(atleast1,model1)
    False
    >>> model2 = {A:False, B:True}
    >>> print logic.pl_true(atleast1,model2)
    True
    >>> model3 = {A:True, B:True}
    >>> print logic.pl_true(atleast1,model2)
    True
    """
    return logic.disjoin(literals)


def atMostOne(literals) :
    """
    Given a list of logic.Expr literals, return a single logic.Expr instance in 
    CNF (conjunctive normal form) that represents the logic that at most one of 
    the expressions in the list is true.
    """
    conj_list = []
    for literal in literals:
        for pair_literal in literals:
            if literal != pair_literal:
                pair = logic.disjoin(~literal, ~pair_literal)
                conj_list.append(pair)

    return logic.conjoin(conj_list)


def exactlyOne(literals) :
    """
    Given a list of logic.Expr literals, return a single logic.Expr instance in 
    CNF (conjunctive normal form)that represents the logic that exactly one of 
    the expressions in the list is true.
    """
    conj_list = []
    for literal in literals:  # could set a variable to indicate if reach the result, to remove repetitive pair 
        for pair_literal in literals:
            if literal != pair_literal:
                pair = logic.disjoin(~literal, ~pair_literal)
                conj_list.append(pair)

    at_least_one = logic.disjoin(literals)
    conj_list.append(at_least_one)

    return logic.conjoin(conj_list)

def extractActionSequence(model, actions):
    """
    Convert a model in to an ordered list of actions.
    model: Propositional logic model stored as a dictionary with keys being
    the symbol strings and values being Boolean: True or False
    Example:
    >>> model = {"North[3]":True, "P[3,4,1]":True, "P[3,3,1]":False, "West[1]":True, "GhostScary":True, "West[3]":False, "South[2]":True, "East[1]":False}
    >>> actions = ['North', 'South', 'East', 'West']
    >>> plan = extractActionSequence(model, actions)
    >>> print plan
    ['West', 'South', 'North']
    """
    action_model = []
    list_of_keys = model.keys()
    for key in list_of_keys:
        if model[key] == True:
            msg = logic.PropSymbolExpr.parseExpr(key)  # msg is a tuple
            if msg[0] in actions:
                action_model.append(msg)
    action_model.sort(key=lambda time: int(time[1]))

    result = []
    for act in action_model:
        result.append(act[0])

    return result


def pacmanSuccessorStateAxioms(x, y, t, walls_grid):
    """
    Successor state axiom for state (x,y,t) (from t-1), given the board (as a 
    grid representing the wall locations).
    Current <==> (previous position at time t-1) & (took action to move to x, y)
    """
    curPosition = logic.PropSymbolExpr(pacman_str, x, y, t)

    neighbors = []

    if not walls_grid[x+1][y]:
        prevPosition = logic.PropSymbolExpr(pacman_str, x+1, y, t-1)
        action = logic.PropSymbolExpr('West', t-1)
        neighbors.append(logic.conjoin(prevPosition, action))

    if not walls_grid[x-1][y]:
        prevPosition = logic.PropSymbolExpr(pacman_str, x-1, y, t-1)
        action = logic.PropSymbolExpr('East', t-1)
        neighbors.append(logic.conjoin(prevPosition, action))

    if not walls_grid[x][y+1]:
        prevPosition = logic.PropSymbolExpr(pacman_str, x, y+1, t-1)
        action = logic.PropSymbolExpr('South', t-1)
        neighbors.append(logic.conjoin(prevPosition, action))

    if not walls_grid[x][y-1]:
        prevPosition = logic.PropSymbolExpr(pacman_str, x, y-1, t-1)
        action = logic.PropSymbolExpr('North', t-1)
        neighbors.append(logic.conjoin(prevPosition, action))

    return curPosition % logic.disjoin(neighbors)


def positionLogicPlan(problem):
    """
    Given an instance of a PositionPlanningProblem, return a list of actions that lead to the goal.
    Available actions are game.Directions.{NORTH,SOUTH,EAST,WEST}
    Note that STOP is not an available action.
    """
    walls = problem.walls
    width, height = problem.getWidth(), problem.getHeight()


    expression = []
    goal_state = problem.getGoalState()
    successors = []
    exclude = []
    
    for x in range(1, width+1):
        for y in range(1, height+1):
            if (x, y) == problem.getStartState():
                if len(expression) == 0:
                    expression.append(logic.PropSymbolExpr(pacman_str, x, y, 0))
                else:
                    state = expression.pop()
                    expression.append(logic.conjoin(state, logic.PropSymbolExpr(pacman_str, x, y, 0)))
            else:
                if len(expression) == 0:
                    expression.append(logic.Expr("~", logic.PropSymbolExpr(pacman_str, x, y, 0)))
                else:
                    state = expression.pop()
                    expression.append(logic.conjoin(state, logic.Expr("~", logic.PropSymbolExpr(pacman_str, x, y, 0))))

    for time in range(50):
        suc = []
        suc_t = []
        exclude_act = []

        if time == 0:
            goal = logic.conjoin(logic.PropSymbolExpr(pacman_str, goal_state[0], goal_state[1], time+1), pacmanSuccessorStateAxioms(goal_state[0], goal_state[1], time+1, walls))
            sol = findModel(logic.conjoin(expression[0], goal))
        else:
            goal = logic.conjoin(logic.PropSymbolExpr(pacman_str, goal_state[0], goal_state[1], time+1), pacmanSuccessorStateAxioms(goal_state[0], goal_state[1], time+1, walls))
            
            for x in range(1, width+1):
                for y in range(1, height+1):
                    if not walls[x][y]:
                        suc = suc + [pacmanSuccessorStateAxioms(x, y, time, walls)]

            suc_t = logic.conjoin(suc)
            if successors:
                success = logic.conjoin(suc_t, logic.conjoin(successors))
            else:
                success = suc_t

            for action in ['North', 'South', 'West', 'East']:
                exclude_act.append(logic.PropSymbolExpr(action, time-1))

            exclude.append(exactlyOne(exclude_act))
            exclude_state = logic.conjoin(exclude)

            sol = findModel(logic.conjoin(expression[0], goal, exclude_state, success))

        if sol:
            return extractActionSequence(sol, ['North', 'South', 'West', 'East'])

        if suc_t:
            successors.append(suc_t)

    return None



def foodLogicPlan(problem):
    """
    Given an instance of a FoodPlanningProblem, return a list of actions that help Pacman
    eat all of the food.
    Available actions are game.Directions.{NORTH,SOUTH,EAST,WEST}
    Note that STOP is not an available action.
    """
    walls = problem.walls
    width, height = problem.getWidth(), problem.getHeight()

    pac_init_location = problem.getStartState()[0]
    food_loc = problem.getStartState()[1].asList()

    expression = []
    successors = []
    exclude = []

    for x in range(1, width + 1) :
        for y in range(1, height + 1) :
            if (x, y) == pac_init_location:
                if len(expression) == 0:
                    expression.append(logic.PropSymbolExpr(pacman_str, x, y, 0))
                else:
                    state = expression.pop()
                    expression.append(logic.conjoin(state,logic.PropSymbolExpr(pacman_str, x, y, 0)))
            else:
                if len(expression) == 0:
                    expression.append(logic.Expr("~", logic.PropSymbolExpr(pacman_str, x, y, 0)))
                else:
                    state = expression.pop()
                    expression.append(logic.conjoin(state,logic.Expr("~", logic.PropSymbolExpr(pacman_str, x, y, 0))))

    for t in range(50):
        suc = []
        suc_t = []
        exclude_act = []

        if t == 0:
            food_eaten = []
            for food_part in food_loc:
                food_eaten.append(logic.PropSymbolExpr(pacman_str, food_part[0], food_part[1], 0))

            food_eaten = logic.conjoin(food_eaten)
            sol = findModel(logic.conjoin(expression[0], food_eaten))
        else:
            for x in range(1, width + 1):
                for y in range(1, height + 1):
                    if not walls[x][y]:
                        suc = suc + [pacmanSuccessorStateAxioms(x, y, t, walls)]

            suc_t = logic.conjoin(suc)

            if len(successors) == 0:
                success = suc_t
            else:
                success = logic.conjoin(suc_t, logic.conjoin(successors))

            for action in ['North', 'South', 'West', 'East']: #exclude axioms
                exclude_act.append(logic.PropSymbolExpr(action, t-1))

            exclude.append(exactlyOne(exclude_act))
            exclude_state = logic.conjoin(exclude)

            food_eaten = []
            for food_part in food_loc:
                food_parts = []
                for i in range(0, t+1):
                    food_parts.append(logic.PropSymbolExpr(pacman_str, food_part[0], food_part[1], i))

                food_parts = logic.disjoin(food_parts)
                food_eaten.append(food_parts)

            food_eaten = logic.conjoin(food_eaten)
            sol = findModel(logic.conjoin(expression[0], food_eaten, exclude_state, success))

        if sol:
            return extractActionSequence(sol, ['North', 'South', 'West', 'East'])
        if suc_t:
            successors.append(suc_t)

    return None


# Abbreviations
plp = positionLogicPlan
flp = foodLogicPlan

# Some for the logic module uses pretty deep recursion on long expressions
sys.setrecursionlimit(100000)
    