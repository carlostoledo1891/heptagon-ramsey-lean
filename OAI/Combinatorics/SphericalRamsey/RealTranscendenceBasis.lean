/-
From openai/math (https://github.com/openai/math), commit
4eaee87548250b2682affda7d05d947c05554bae, lean/OAI/Combinatorics/SphericalRamsey/RealTranscendenceBasis.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`). No other line was
changed; see docs/PORT-LOG.md.
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

namespace OAI

noncomputable section
namespace GrahamSpherical

/-- The designated transcendental real is retained in the actual maximal
algebraically independent subset of the real field. -/
theorem exists_real_transcendenceBasis_containing (a : ℝ)
    (ha : Transcendental ℚ a) :
    ∃ B : Set ℝ, a ∈ B ∧ IsTranscendenceBasis ℚ (fun b : B => (b : ℝ)) := by
  have hs : AlgebraicIndepOn ℚ id ({a} : Set ℝ) := by
    exact (algebraicIndependent_singleton_iff
      (R := ℚ) (x := fun b : ({a} : Set ℝ) => (b : ℝ)) ⟨a, by simp⟩).2 ha
  obtain ⟨B, hsub, hB⟩ := exists_isTranscendenceBasis_superset hs
  exact ⟨B, hsub (by simp), hB⟩

end GrahamSpherical

end

end OAI
