from typing import Dict, List, Optional  # used for type clarifications
from abc import ABC, abstractmethod


# base class for Constraints
class ConstraintBase(ABC):
    # constructor
    def __init__(self, variables) -> None:
        self.variables = variables  # list of variables

    # all derived classes must implement this abstract method
    @abstractmethod
    def satisfied(self, v: str, assignment: Dict[str, int]) -> bool:
        ...

    # return set of unassigned neighbors
    def check_unassigned_neighbors(self, v: str, assignment: Dict[str, int]):
        # using set so we don't double count neighbors
        unassigned_neighbors = set()
        for i in range(len(self.variables)):
            x = self.variables[i]
            # make sure x has not been assigned
            if (x != v) and (x not in assignment):
                unassigned_neighbors.add(x)

        return unassigned_neighbors

    # iterator for constraints, yields variables in constraint
    def __iter__(self):
        for i in range(len(self.variables)):
            yield self.variables[i]


# basic constraint class for cryptarithmetic csp
class Constraint(ConstraintBase):
    # constructor
    def __init__(self, variables: List[str]) -> None:
        super().__init__(variables)
        self.variables = variables  # variables participating in constraint
        self.x1 = self.variables[0]  # digit in first num
        self.x2 = self.variables[1]  # digit in second num
        self.y = self.variables[2]  # x1 + x2
        self.carryLeft = self.variables[3]  # carry on left side of equation
        self.carryRight = self.variables[4]  # carry on right side of equation

    # check if assignment satisfies all constraints
    def satisfied(self, v: str, assignment: Dict[str, int]) -> bool:
        # v isn't in this constraint
        if v not in self.variables:
            return True

        # check if left side of equation == to right side, only if all
        # assignments been complete for the participants
        if all(v in assignment for v in self.variables):
            left = assignment[self.x1] + assignment[self.x2] + assignment[self.carryLeft]
            right = assignment[self.y] + (10 * assignment[self.carryRight])
            return left == right

        return True  # this means there is currently no conflict


# special constraint for cryptarithmetic csp for duplicate letters
class DuplicateConstraint(ConstraintBase):
    # constructor
    def __init__(self, variables: List[str]) -> None:
        super().__init__(variables)
        self.variables = variables  # variables participating in constraint

    def satisfied(self, v: str, assignment: Dict[str, int]) -> bool:
        if len(assignment) == 0:
            return True  # neither have been assigned yet
        elif len(assignment) == len(self.variables):
            # both assigned to same value
            if len(set(assignment.values())) == 1:
                return True

            return False  # assigned to different values

        # a value was assigned; therefore need to assign to
        # duplicate neighbors
        for x in self.variables:
            if x != v:
                assignment[x] = assignment[v]

        return True


# special constraint for cryptarithmetic csp for uniqueness
class UniqueConstraint(ConstraintBase):
    # constructor
    def __init__(self, variables: List[str]) -> None:
        super().__init__(variables)
        self.variables = variables  # variables participating in constraint

    def satisfied(self, v: str, assignment: Dict[str, int]) -> bool:
        if v in self.variables:  # v is participating in this constraint
            # check if v's assignment violates uniqueness constraint
            for var in assignment:
                # make sure we only check against other variables
                # participating in the constraint
                if var != v and var in self.variables:
                    # constraint violated if two neighbors have same value
                    if assignment[v] == assignment[var]:
                        return False

        return True


class TotalSumConstraint(ConstraintBase):
    # constructor
    def __init__(self, variables: List[str]):
        super().__init__(variables)
        self.variables = variables

    def satisfied(self, v: str, assignment: Dict[str, int]) -> bool:
        # check if the total sum is valid
        if len(assignment) == len(self.variables):
            x1 = assignment[self.variables[0]]
            x2 = assignment[self.variables[1]]
            x3 = assignment[self.variables[2]]
            x4 = assignment[self.variables[3]]
            x5 = assignment[self.variables[4]]
            x6 = assignment[self.variables[5]]
            x7 = assignment[self.variables[6]]
            x8 = assignment[self.variables[7]]
            x9 = assignment[self.variables[8]]
            x10 = assignment[self.variables[9]]
            x11 = assignment[self.variables[10]]
            x12 = assignment[self.variables[11]]
            x13 = assignment[self.variables[12]]
            c0 = assignment[self.variables[13]]
            c1 = assignment[self.variables[14]]
            c2 = assignment[self.variables[15]]
            c3 = assignment[self.variables[16]]
            c4 = assignment[self.variables[17]]
            # check if the total sum is mathematically correct
            n1 = ((x1 + c3) * 1000) + ((x2 + c2) * 100) + ((x3 + c1) * 10) + x4
            n2 = (x5 * 1000) + (x6 * 100) + (x7 * 10) + x8
            total = (x9 * 10000) + ((x10 + c3) * 1000) + ((x11 + c2) * 100) + ((x12 + c1) * 10) + x13
            return n1 + n2 == total

        return True


# abstraction of cryptarithmetic CSP in the form of an object with some methods
class CSP:
    """ initialize a cryptarithmetic CSP with
        - a List containing the variables
        - a Dict containing a mapping of each variable to its domain
        - a Dict containing a mapping of each variable to a List of constraints

        methods for adding constraints, checking consistency, FORWARD CHECKING
        the backtracking algorithm is also implemented as a method below """

    # constructor
    def __init__(self, variables: List[str], domains: Dict[str, List[int]] = {}) -> None:
        self.variables: List[str] = variables  # set of variables
        self.domains: Dict[str, List[int]] = domains  # set of domains for each variable
        self.constraints: Dict[str, list] = {}

        # initialize empty set of constraints for each variable
        for v in self.variables:
            self.constraints[v] = []

    # set the domain of a variable
    def set_domain(self, v: str, new_domain: List[int]) -> None:
        self.domains[v] = new_domain

    # add a constraint (to all applicable participants)
    def add_constraint(self, constraint) -> None:
        for v in constraint.variables:  # for each v the constraint concerns
            self.constraints[v].append(constraint)  # map constraint to v

    # check if an assignment is consistent
    def consistent(self, v: str, assignment: Dict[str, int]) -> bool:
        for constraint in self.constraints[v]:
            if not constraint.satisfied(v, assignment):
                return False
        return True

    # FORWARD CHECKING, returns a bool and set of neighbors
    def inference(self, variable: str, value: int, assignment: Dict[str, int]):
        # using set to avoid double counting
        neighbors = set()
        for c in self.constraints[variable]:
            for neighbor in c:
                # carries are auxiliary; don't count
                if neighbor[0] != 'c':
                    neighbors.add(neighbor)

        # remove the assigned value from neighbors
        for neighbor in neighbors:
            if value in self.domains[neighbor]:
                self.domains[neighbor].remove(value)
                # if the neighbor has no domain values left and it has NOT been assigned
                if len(self.domains[neighbor]) == 0 and neighbor not in assignment:
                    # inferences are invalid
                    return False, set()

        return True, neighbors

    # backtracking algorithm, returns solution if found
    def backtracking_search(self, assignment: Dict[str, int] = {}) -> Optional[Dict[str, int]]:
        """ recursive backtracking search """

        # every variable has been assigned a value once the length
        # of assignment is equal to the amount of variables we have
        if len(assignment) == len(self.variables):
            return assignment

        # select unassigned variable by first generating a List of variables
        # in the CSP, but not yet in the assignment
        unassigned: List[str] = [v for v in self.variables if v not in assignment]

        # using minimum remaining values heuristic and degree heuristic
        candidate = unassigned[0]
        tied_variables = []  # using this for degree heuristic
        for i in range(1, len(unassigned)):
            if len(self.domains[unassigned[i]]) < len(self.domains[candidate]):
                candidate = unassigned[i]
                tied_variables = []
            elif len(self.domains[unassigned[i]]) == len(self.domains[candidate]):
                tied_variables.append(unassigned[i])

        # running degree heuristic if there was a tie
        if len(tied_variables) > 0:

            # checking how many unassigned neighbors candidate has
            c1 = self.constraints[candidate][0]
            unassigned_neighbors_v1 = c1.check_unassigned_neighbors(candidate, assignment)
            for i in range(1, len(self.constraints[candidate])):
                # don't add neighbors from TotalSumConstraint
                if not isinstance(self.constraints[candidate][i], TotalSumConstraint):
                    c = self.constraints[candidate][i].check_unassigned_neighbors(candidate, assignment)
                    unassigned_neighbors_v1 = unassigned_neighbors_v1.union(c)

            # comparing # of candidate's neighbors
            # to # of other unassigned variables who tied on the
            # minimum remaining values heuristic
            for v in tied_variables:
                unassigned_neighbors_v2 = self.constraints[v][0].check_unassigned_neighbors(v, assignment)

                for i in range(1, len(self.constraints[v])):
                    # don't add neighbors from TotalSumConstraint
                    if not isinstance(self.constraints[v][i], TotalSumConstraint):
                        c = self.constraints[v][i].check_unassigned_neighbors(v, assignment)
                        unassigned_neighbors_v2 = unassigned_neighbors_v2.union(c)

                if len(unassigned_neighbors_v2) > len(unassigned_neighbors_v1):
                    candidate = v

        # selecting a domain value to assign to v
        for value in self.domains[candidate]:
            partial_assign = assignment.copy()
            partial_assign[candidate] = value
            # if the assignment is consistent, recurse
            if self.consistent(candidate, partial_assign):

                # inferences performs forward checking
                # returns boolean to indicate successfulness
                inference_success, neighbors = self.inference(candidate, value, partial_assign)
                if inference_success:
                    result = self.backtracking_search(partial_assign)
                    # solution found, return the result
                    if result is not None:
                        return result

                # removing inferences
                for n in neighbors:
                    self.domains[n].append(value)
                    self.domains[n].sort()

        # returning failure; no solution found
        return None


# read in csp from input file and return csp object
def construct_csp(file) -> CSP:
    """ abstract the csp as
        - x, the set of variables
        - d, the set of domains for each x
        - c, the set of constraints

        returns x, d, c """

    open_file = open(file, 'r')
    lines = open_file.readlines()
    line1 = lines[0].strip()
    line2 = lines[1].strip()
    line3 = lines[2].strip()
    open_file.close()

    # loading in the variables
    x1, x2, x3, x4 = line1[0], line1[1], line1[2], line1[3]
    x5, x6, x7, x8 = line2[0], line2[1], line2[2], line2[3]
    x9, x10, x11, x12, x13 = line3[0], line3[1], line3[2], line3[3], line3[4]

    # variables
    variables = ['x1', 'x2', 'x3', 'x4', 'x5', 'x6', 'x7', 'x8', 'x9', 'x10', 'x11', 'x12', 'x13',
                 'c0', 'c1', 'c2', 'c3', 'c4']

    # list of the letters for use in constraint formulation
    letters = [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13]

    # domain of each variable (for any 4 + 4 cryptarithmetic csp)
    d = {'x1': [1, 2, 3, 4, 5, 6, 7, 8, 9],
         'x2': [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
         'x3': [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
         'x4': [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
         'x5': [1, 2, 3, 4, 5, 6, 7, 8, 9],
         'x6': [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
         'x7': [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
         'x8': [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
         'x9': [1],
         'x10': [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
         'x11': [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
         'x12': [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
         'x13': [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]}

    # initialize the csp
    csp = CSP(variables)

    # set domains for each variable
    for i in range(1, 14):
        v_ref = 'x' + str(i)
        csp.set_domain(v_ref, d[v_ref])

    csp.set_domain('c0', [0])
    csp.set_domain('c1', [0, 1])
    csp.set_domain('c2', [0, 1])
    csp.set_domain('c3', [0, 1])
    csp.set_domain('c4', [1])

    # set basic constraints for each variables
    csp.add_constraint(Constraint(['x4', 'x8', 'x13', 'c0', 'c1']))
    csp.add_constraint(Constraint(['x3', 'x7', 'x12', 'c1', 'c2']))
    csp.add_constraint(Constraint(['x2', 'x6', 'x11', 'c2', 'c3']))
    csp.add_constraint(Constraint(['x1', 'x5', 'x10', 'c3', 'c4']))

    # formulating and adding duplicate constraints
    for i in range(len(letters)):
        participants = ['x' + str(i + 1)]
        for j in range(i + 1, len(letters)):
            if letters[j] == letters[i]:
                participants.append('x' + str(j + 1))
        if len(participants) > 1:
            csp.add_constraint(DuplicateConstraint(participants.copy()))

        participants.clear()

    # mapping each letter to a variable
    var_letter_map = {x1: 'x1', x2: 'x2', x3: 'x3', x4: 'x4', x5: 'x5', x6: 'x6',
                      x7: 'x7', x8: 'x8', x9: 'x9', x10: 'x10', x11: 'x11',
                      x12: 'x12', x13: 'x13'}

    # adding uniqueness constraint
    set_of_unique_vars = set()
    for letter in letters:
        set_of_unique_vars.add(var_letter_map[letter])
    csp.add_constraint(UniqueConstraint(list(set_of_unique_vars)))

    # adding the TotalSumConstraint
    csp.add_constraint(TotalSumConstraint(variables))

    return csp


# write solution to output file
def output_solution_file(solution: Dict[str, int]) -> None:
    file_name = input("Enter output file name (with .txt): ")
    output_file = open(file_name, 'w')

    for i in range(1, 14):
        number = solution['x' + str(i)]
        print(number, sep='', end='', file=output_file)
        if i == 4 or i == 8:
            print('\n', sep='', end='', file=output_file)


def main():
    input_file = input("Enter the name of the input file (with .txt): ")
    csp = construct_csp(input_file)
    solution = csp.backtracking_search()
    if solution is not None:
        output_solution_file(solution)
    else:
        print("No solution")


main()
