#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.

'''This file will contain different constraint propagators to be used within
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method).
      bt_search NEEDS to know this in order to correctly restore these
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated
        constraints)
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no
    propagation at all. Just check fully instantiated constraints'''

    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with
       only one uninstantiated variable. Remember to keep
       track of all pruned variable,value pairs and return '''
    pruned = []
    if not newVar: # At the start
        for const in csp.get_all_cons():
            if const.get_n_unasgn() == 1:
                var = const.get_unasgn_vars()[0]
                var_dom = var.cur_domain()
                for val in var_dom:
                    if not const.has_support(var, val):
                        var.prune_value(val)
                        pruned.append((var, val))
                if len(var.cur_domain()) == 0: # DWO
                    return False, pruned
        return True, pruned
    else:
        for const in csp.get_cons_with_var(newVar):
            if const.get_n_unasgn() == 1:
                var = const.get_unasgn_vars()[0]
                var_dom = var.cur_domain()
                for val in var_dom:
                    if not const.has_support(var, val):
                        var.prune_value(val)
                        pruned.append((var, val))
                if len(var.cur_domain()) == 0: # DWO
                    return False, pruned
        return True, pruned

def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    pruned = []
    if not newVar:
        const_lst = csp.get_all_cons()
        if not gac(csp, const_lst, pruned):
            return False, pruned
        else:
            return True, pruned
    else:
        const_lst = csp.get_cons_with_var(newVar)
        if not gac(csp, const_lst, pruned):
            return False, pruned
        else:
            return True, pruned

def gac(csp, queue, pruned):
    '''queue is list of constraints that need GAC checking.
       pruned is list of pruned values (mutated within this function)'''
    while len(queue) != 0:
        const = queue.pop(0)
        for var in const.get_scope():
            for val in var.cur_domain():
                if not const.has_support(var, val):
                    var.prune_value(val)
                    pruned.append((var, val))
                    if len(var.cur_domain()) == 0: # DWO
                        queue.clear()
                        return False
                    else:
                        for c in csp.get_cons_with_var(var):
                            if c not in queue:
                                queue.append(c)
    return True
