module

public import Theory.GroupTheory.PResidual.NormalizedGenerators
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The perfect residual of a pair of finite local groups

The ambient group may be infinite. Finite vertex groups sharing a Sylow
p-subgroup generate a normal p-perfect subgroup from their local residuals.
That subgroup is the ambient p-residual and is supplemented by the original
common Sylow. This applies to the universal completion of a cubic amalgam;
it does not replace that completion by an arbitrary finite quotient.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), Section 3,
proof of (3.2), printed pp.386--387.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ}

/-- A join of p-perfect subgroups is p-perfect, without ambient finiteness. -/
theorem isPPerfect_sup (A B : Subgroup G) (hA : IsPPerfect p A) (hB : IsPPerfect p B) :
    IsPPerfect p (A ⊔ B : Subgroup G) := by
  let H := A ⊔ B
  have ha : IsPPerfect p (A.subgroupOf H) := hA.of_surjective
    (subgroupOfEquivOfLe (show A ≤ H from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show A ≤ H from le_sup_left)).symm.surjective
  have hb : IsPPerfect p (B.subgroupOf H) := hB.of_surjective
    (subgroupOfEquivOfLe (show B ≤ H from le_sup_right)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show B ≤ H from le_sup_right)).symm.surjective
  have hs : A.subgroupOf H ⊔ B.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup (show A ≤ H from le_sup_left)
      (show B ≤ H from le_sup_right), subgroupOf_self]
  apply (pResidual_eq_top_iff p H).mp
  apply top_unique
  rw [← hs]
  exact sup_le (le_pResidual_of_isPPerfect _ ha) (le_pResidual_of_isPPerfect _ hb)

theorem isPPerfect_embedded_pResidual_of_finite (p : ℕ) (A : Subgroup G) [Finite A] :
    IsPPerfect p ((pResidual p A).map A.subtype) := by
  let e := (pResidual p A).equivMapOfInjective A.subtype A.subtype_injective
  exact (isPPerfect_pResidual (G := A) p).of_surjective e.toMonoidHom e.surjective

theorem embedded_pResidual_sup_of_common_sylow {p : ℕ} [Fact p.Prime]
    (A T : Subgroup G) [Finite A] (P : Sylow p A)
    (hP : (P : Subgroup A).map A.subtype = T) :
    (pResidual p A).map A.subtype ⊔ T = A := by
  have hh := congrArg (fun K : Subgroup A => K.map A.subtype)
    (pResidual_sup_sylow_eq_top P)
  simpa only [Subgroup.map_sup, hP, ← MonoidHom.range_eq_map, range_subtype] using hh

theorem pResidual_eq_sup_of_finite_sylow_pair {p : ℕ} [Fact p.Prime] (A B T : Subgroup G) [Finite A] [Finite B]
    (P : Sylow p A) (Q : Sylow p B)
    (hP : (P : Subgroup A).map A.subtype = T)
    (hQ : (Q : Subgroup B).map B.subtype = T)
    (hgen : A ⊔ B = ⊤) :
    pResidual p G = (pResidual p A).map A.subtype ⊔ (pResidual p B).map B.subtype := by
  have hnA := (pResidual p A).le_normalizer_map A.subtype
  have hnB := (pResidual p B).le_normalizer_map B.subtype
  simp only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hnA hnB
  have hTA : T ≤ A := hP ▸ map_subtype_le (P : Subgroup A)
  have hTB : T ≤ B := hQ ▸ map_subtype_le (Q : Subgroup B)
  apply pResidual_eq_sup_of_normalized_generators _ _ T
    (isPPerfect_embedded_pResidual_of_finite p A) (isPPerfect_embedded_pResidual_of_finite p B)
    (hP ▸ P.isPGroup'.map A.subtype) (hTA.trans hnA) (hTB.trans hnB)
  rw [← sup_idem T, sup_sup_sup_comm,
    embedded_pResidual_sup_of_common_sylow A T P hP, embedded_pResidual_sup_of_common_sylow B T Q hQ, hgen]
/-- The common Sylow supplements the residual even in an infinite completion. -/
theorem pResidual_sup_of_finite_sylow_pair {p : ℕ} [Fact p.Prime]
    (A B T : Subgroup G) [Finite A] [Finite B]
    (P : Sylow p A) (Q : Sylow p B)
    (hP : (P : Subgroup A).map A.subtype = T)
    (hQ : (Q : Subgroup B).map B.subtype = T) (hgen : A ⊔ B = ⊤) :
    pResidual p G ⊔ T = ⊤ := by
  rw [pResidual_eq_sup_of_finite_sylow_pair A B T P Q hP hQ hgen,
    ← sup_idem T, sup_sup_sup_comm,
    embedded_pResidual_sup_of_common_sylow A T P hP,
    embedded_pResidual_sup_of_common_sylow B T Q hQ, hgen]

/-- Local finiteness proves perfectness of the universal completion's residual. -/
theorem isPPerfect_pResidual_of_finite_sylow_pair {p : ℕ} [Fact p.Prime]
    (A B T : Subgroup G) [Finite A] [Finite B]
    (P : Sylow p A) (Q : Sylow p B)
    (hP : (P : Subgroup A).map A.subtype = T)
    (hQ : (Q : Subgroup B).map B.subtype = T) (hgen : A ⊔ B = ⊤) :
    IsPPerfect p (pResidual p G) := by
  rw [pResidual_eq_sup_of_finite_sylow_pair A B T P Q hP hQ hgen]
  exact isPPerfect_sup _ _ (isPPerfect_embedded_pResidual_of_finite p A)
    (isPPerfect_embedded_pResidual_of_finite p B)
end Subgroup
