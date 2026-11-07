
-- heptagon-ramsey-lean (2026-11-07): our library, appended to openai/math lean/lakefile.lean; nothing above this line is ours.
lean_lib HeptagonRamsey where
  roots := #[`HeptagonRamsey]
  globs := #[`HeptagonRamsey.+]
