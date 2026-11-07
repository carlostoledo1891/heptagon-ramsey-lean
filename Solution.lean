module

public import HeptagonRamsey.Heptagon.Statement

public section

/-!
# Proved solution

`HeptagonRamsey.Heptagon.graham_false'` is proved in `HeptagonRamsey/Heptagon/Transport.lean`
and `HeptagonRamsey.Heptagon.heptagon_counterexample` in `HeptagonRamsey/Heptagon/Statement.lean`,
on the module-system port of OpenAI's EuclideanRamsey and SphericalRamsey files (`OAI/`).
`Erdos174.IsRamsey` comes from `Transport.lean`; Comparator checks that it is identical to the
copy in `Challenge.lean`.
-/

#print axioms HeptagonRamsey.Heptagon.heptagon_counterexample
#print axioms HeptagonRamsey.Heptagon.graham_false'
