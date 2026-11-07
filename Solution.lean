module

public import HeptagonRamsey.Heptagon.Statement
public import HeptagonRamsey.Generic.Statement

public section

/-!
# Proved solution

`HeptagonRamsey.Heptagon.graham_false'` is proved in `HeptagonRamsey/Heptagon/Transport.lean`,
`HeptagonRamsey.Heptagon.heptagon_counterexample` in `HeptagonRamsey/Heptagon/Statement.lean`, and
`HeptagonRamsey.Generic.generic_seven_not_isRamsey` and `seven_circle_configuration_isRamsey` in
`HeptagonRamsey/Generic/Statement.lean`, all on the module-system port of OpenAI's EuclideanRamsey and SphericalRamsey files (`OAI/`).
`Erdos174.IsRamsey` comes from `Transport.lean`; Comparator checks that it is identical to the
copy in `Challenge.lean`.
-/

#print axioms HeptagonRamsey.Heptagon.heptagon_counterexample
#print axioms HeptagonRamsey.Heptagon.graham_false'
#print axioms HeptagonRamsey.Generic.generic_seven_not_isRamsey
#print axioms HeptagonRamsey.Generic.seven_circle_configuration_isRamsey
