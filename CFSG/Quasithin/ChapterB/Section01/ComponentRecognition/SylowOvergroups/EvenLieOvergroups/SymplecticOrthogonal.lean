module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.SymplecticOrthogonal.RankTwo

/-!
# Symplectic and orthogonal branches of the B.1.13 overgroup bound

This module proves the catalogue branches of symplectic and odd orthogonal
rank at most two, minus orthogonal rank two, and the actual commutator
carrier PSp₄(2)′. It applies each result to the literal component intersection
of B.1.13, preserving relative subnormality and the ambient centre factor.

The higher symplectic ranks, split orthogonal ranks, and remaining minus
ranks still require their proper-Sylow-overgroup geometry. The general odd
orthogonal comparison is exported by `LowRanks`; final family assembly must
discharge its symplectic premise. No result here asserts the full catalogue.

Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85), and GLS3 §2.6–2.7.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
variable {G : Type*} [Group G] [Finite G]

/-- The catalogue's exact symplectic parameter range through rank two. -/
theorem properSylowFittingBound_isPSp_rank_le_two {r a : ℕ}
    (ha : 0 < a) (hp : CFSG.KnownSimple.SymplecticParameters r (2 ^ a))
    (hr : r ≤ 2) (hm : ClassicalGroup.IsPSp G r (2 ^ a)) :
    ProperSylowFittingBound G := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hm
  apply properSylowFittingBound_of_equiv e
  have hr1 := hp.2.1
  rcases (show r = 1 ∨ r = 2 by omega) with he | he
  · subst r
    exact properSylowFittingBound_psp_one F a ha hF
  · subst r
    have ha' : 1 < a := by
      by_contra! hh
      have he : a = 1 := by omega
      exact hp.2.2.2 rfl (by simp [he])
    exact properSylowFittingBound_psp_two F a ha' hF

/-- The catalogue's odd orthogonal aliases through rank two. -/
theorem properSylowFittingBound_isPOmegaOdd_rank_le_two {r a : ℕ}
    (ha : 0 < a) (hp : CFSG.KnownSimple.OrthogonalOddParameters r (2 ^ a))
    (hr : r ≤ 2) (hm : ClassicalGroup.IsPOmegaOdd G r (2 ^ a)) :
    ProperSylowFittingBound G := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hm
  apply properSylowFittingBound_of_equiv e
  apply properSylowFittingBound_odd_of_psp F r a (by have := hp.2.1; omega) hF
  exact properSylowFittingBound_isPSp_rank_le_two ha hp hr
    ⟨F, hfield, hfinite, hF, ⟨MulEquiv.refl _⟩⟩

/-- All fields in the minus-four catalogue branch, including order two. -/
theorem properSylowFittingBound_isPOmegaMinus_two {a : ℕ}
    (ha : 0 < a) (hm : ClassicalGroup.IsPOmegaMinus G 2 (2 ^ a)) :
    ProperSylowFittingBound G := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hm
  exact properSylowFittingBound_of_equiv e (properSylowFittingBound_minus_two F a ha hF)

variable (K L : Subgroup G) (T : Sylow 2 G)
  (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
  (hkind : IsQuasisimple K ∨ Nat.card K = 3)
  (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)

include hL hLK hkind hK hKL

/-- Discharge the source proper-overgroup premise for symplectic ranks one and two. -/
theorem eq_component_of_isPSp_rank_le_two {r a : ℕ}
    (ha : 0 < a) (hp : CFSG.KnownSimple.SymplecticParameters r (2 ^ a))
    (hr : r ≤ 2) (hm : ClassicalGroup.IsPSp L r (2 ^ a)) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_isPSp_rank_le_two ha hp hr hm)

/-- Discharge the same premise for the literal odd orthogonal carriers. -/
theorem eq_component_of_isPOmegaOdd_rank_le_two {r a : ℕ}
    (ha : 0 < a) (hp : CFSG.KnownSimple.OrthogonalOddParameters r (2 ^ a))
    (hr : r ≤ 2) (hm : ClassicalGroup.IsPOmegaOdd L r (2 ^ a)) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_isPOmegaOdd_rank_le_two ha hp hr hm)

/-- Discharge the minus-four source branch through its quadratic-field PSL₂ model. -/
theorem eq_component_of_isPOmegaMinus_two {a : ℕ}
    (ha : 0 < a) (hm : ClassicalGroup.IsPOmegaMinus L 2 (2 ^ a)) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_isPOmegaMinus_two ha hm)

/-- Keep PSp₄(2)′ as the actual commutator of the specified projective group. -/
theorem eq_component_of_binary_symplectic_derived
    (e : L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_of_equiv e properSylowFittingBound_binary_symplectic_derived)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
