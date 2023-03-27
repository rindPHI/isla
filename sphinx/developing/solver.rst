The "solver" Module
===================

.. note::
   This page is under construction.

The ISLaSolver Class
--------------------

.. autoclass:: isla.solver.ISLaSolver

Main Functions
^^^^^^^^^^^^^^

.. automethod:: isla.solver.ISLaSolver.solve

Below, we show the source code of :meth:`~isla.solver.ISLaSolver.solve()`. The code contains sufficient inline documentation. Essentially, it realizes a transition system between *Constrained Derivation Trees,* i.e., pairs of constraints and (potentially open) derivation trees. In the implementation, these structures are called *states.* The solver takes the state on top of a queue (a Fibonacci heap) and processes it with the first applicable "transition rule," called "elimination function" in the code. The function loops until at least one solution has been found, and only as long as there are still elements in the queue.

.. literalinclude:: ../../src/isla/solver.py
   :pyobject: ISLaSolver.solve
   :start-at: if self.timeout_seconds
   :dedent: 8

.. automethod:: isla.solver.ISLaSolver.check

.. automethod:: isla.solver.ISLaSolver.parse

.. automethod:: isla.solver.ISLaSolver.repair

.. automethod:: isla.solver.ISLaSolver.mutate
