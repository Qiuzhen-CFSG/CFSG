module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelCases
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAction
public import Mathlib.Algebra.CharP.CharAndCard
public import Theory.GroupTheory.SylowNormalizerCommutingFamily.SelfNormalizing

/-!
# Binary component normalizers and outer automorphisms

Every binary Lie alternative in the actual component catalogue has
self-normalizing Sylow two-subgroups. Triangular matrices prove the linear
cases; the genuine derived Sp₄ and G₂ carriers use the published binary
normalizer calculations. The PSL₂ branch cannot have exponent one.

Inner/graph coverage bounds the outer quotient of PSL₄(2) and PSL₅(2) by
two. The actual Sp₄(F)′–A₆ equivalence gives outer order four for a
two-element field. For G₂(2)′ the last outer-order calculation remains
conditional on surjectivity of full-group conjugation, the separate
binary automorphism theorem. The SL₃(2) outer bound is still required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
`refs/quasithin.pdf`, B.4.2 and B.5.6, printed pp.86,105, and the
proof of 15.3.49(k), p.1144. The imported G₂ computations retain the
ATLAS attribution in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.BinaryModels

/-- The binary linear outer quotient has at most two elements, hence has 3′ order. -/
theorem binary_linear_outer_three_free {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ 3 ∣ Nat.card (MulAut.Outer PSL(n, ZMod 2)) := by
  let D := BinaryLinear.OuterCyclic.LinearGroup n
  let q := QuotientGroup.mk' (MulAut.innerSubgroup D)
  let a := q (BinaryLinear.OuterCyclic.graphLinear n)
  have htwo : ∀ x : MulAut.Outer D, x = 1 ∨ x = a := by
    intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup D) x
    obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.inner_graph hn b
    have hi : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    rcases hg with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr (by change q (_ * _) = _; rw [map_mul, hi, mul_one])
  have hs : Function.Surjective (fun b : Bool => if b then a else 1) := by
    intro x
    rcases htwo x with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  let _ : Finite (MulAut.Outer D) := Finite.of_surjective _ hs
  have hc : Nat.card (MulAut.Outer D) ≤ 2 := by
    simpa using Nat.card_le_card_of_surjective _ hs
  have he := Nat.card_congr
    (MulAut.outerCongr (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < n))).toEquiv
  rw [he]
  intro h
  have hp : 0 < Nat.card (MulAut.Outer D) := Nat.card_pos
  have := Nat.le_of_dvd hp h
  omega

/-- Transport the order-four outer quotient of A₆ to the exact derived symplectic carrier. -/
theorem binary_symplectic_outer_three_free {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    ¬ 3 ∣ Nat.card (MulAut.Outer (commutator (Matrix.symplecticGroup (Fin 2) F))) := by
  rw [Nat.card_congr (MulAut.outerCongr
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hF)).toEquiv,
    AlternatingSix.ShadowLocal.outer_card]
  decide

open Theory.SpecificGroups.LinearSylowNormalizers

/-- Over a two-element field every invertible triangular diagonal entry is one. -/
theorem linear_borel_eq_unipotent_of_card_two {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) (n : ℕ) : borel n F = unipotent n F := by
  let _ := Fintype.ofFinite F
  let e := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  apply le_antisymm _ (unipotent_le_borel n F)
  intro g hg
  apply (mem_unipotent n F g).mpr
  refine ⟨hg, fun i => ?_⟩
  have hd := g.property
  rw [Matrix.det_of_isUpperTriangular ((mem_borel n F g).mp hg)] at hd
  have hp : (∏ j, g.val j j) ≠ 0 := by rw [hd]; exact one_ne_zero
  have hi := (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  apply e.injective
  rw [map_one]
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ (by simpa using hi)

/-- Conjugate the triangular calculation to an arbitrary Sylow subgroup. -/
theorem sl_sylow_self_normalizing_of_card_two {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) {n : ℕ} (hn : 0 < n)
    (S : Sylow 2 (Matrix.SpecialLinearGroup (Fin n) F)) :
    normalizer (S : Set (Matrix.SpecialLinearGroup (Fin n) F)) = S := by
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
    (by simpa only [Nat.card_eq_fintype_card, pow_one] using hF)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin n) F)
    (standardSylow n F hn) S
  have he : (unipotent n F).map (MulAut.conj g).toMonoidHom =
      (S : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)) := by
    have hs := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, coe_standardSylow] at hs
    rw [← hs]
    ext x
    rw [mem_map_equiv, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
    rfl
  rw [← Sylow.coe_coe, ← he, ← Subgroup.map_equiv_normalizer_eq,
    normalizer_unipotent, linear_borel_eq_unipotent_of_card_two hF]

/-- The genuine projective binary quotient retains Sylow self-normalization. -/
theorem binary_psl_sylow_self_normalizing {n : ℕ} (hn : 0 < n)
    (S : Sylow 2 PSL(n, ZMod 2)) : normalizer (S : Set PSL(n, ZMod 2)) = S :=
  Sylow.self_normalizing_of_surjective
    (BinaryLinear.OuterCyclic.projectiveEquivSL hn).symm.toMonoidHom
    (BinaryLinear.OuterCyclic.projectiveEquivSL hn).symm.surjective
    (sl_sylow_self_normalizing_of_card_two (by simp) hn) S

/-- The restricted G₂ Borel collapses over every two-element field. -/
theorem g2_sylow_self_normalizing_of_card_two {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) (S : Sylow 2 (commutator (Atlas.G2.Model F))) :
    normalizer (S : Set (commutator (Atlas.G2.Model F))) = S := by
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
    (by simpa only [Nat.card_eq_fintype_card, pow_one] using hF)
  let D := commutator (Atlas.G2.Model F)
  obtain ⟨P, hP⟩ := (Atlas.G2.LieParabolicSetup.sylow (F := F)).exists_subgroupOf_eq_of_normal D
  have hN : normalizer (P : Set D) = P := by
    change normalizer ((P : Subgroup D) : Set D) = _
    rw [hP, Atlas.G2.LieParabolicSetup.sylow_coe,
      Atlas.G2.DerivedNormalizerSolvable.normalizer_restricted_unipotent,
      Atlas.G2.LieParabolicSetup.borel_eq_unipotent_of_card_two hF]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D P S
  have he : (P : Subgroup D).map (MulAut.conj g).toMonoidHom = (S : Subgroup D) :=
    congrArg Sylow.toSubgroup hg
  rw [← Sylow.coe_coe, ← he, ← Subgroup.map_equiv_normalizer_eq]
  exact congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hN

/-- Full-group conjugation coverage makes the outer quotient a quotient of the order-two abelianization. -/
theorem binary_g2_outer_three_free_of_coverage
    (hcover : Function.Surjective Atlas.G2.LieAutomorphismExtensions.binaryConjugation) :
    ¬ 3 ∣ Nat.card (MulAut.Outer (commutator (Atlas.G2.Model (ZMod 2)))) := by
  let D := commutator (Atlas.G2.Model (ZMod 2))
  let f := MulAut.outerAction D
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup D) x
    obtain ⟨g, rfl⟩ := hcover a
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hc : Nat.card ((Atlas.G2.Model (ZMod 2)) ⧸ D) = 2 := by
    have hh := D.card_eq_card_quotient_mul_card_subgroup
    rw [Atlas.G2.LieAutomorphismExtensions.card_binaryFull,
      Atlas.G2.LieAutomorphismExtensions.card_binaryDerived] at hh
    omega
  intro h
  have hd := h.trans (card_dvd_of_surjective f hf)
  rw [hc] at hd
  exact (by decide : ¬ 3 ∣ 2) hd

open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner

/-- All binary alternatives, including both small derived groups, have self-normalizing Sylow two-subgroups. -/
theorem binary_model_self_normalizing {D : Type*} [Group D] [Finite D]
    (h : LieComponentModel D 1) (P : Sylow 2 D) : normalizer (P : Set D) = P := by
  cases h with
  | linear_two he F hF m => omega
  | linear_three he F hF m =>
      obtain ⟨f⟩ := m
      exact Sylow.self_normalizing_of_surjective f.symm.toMonoidHom f.symm.surjective
        (sl_sylow_self_normalizing_of_card_two (by simpa using hF) (by decide)) P
  | symplectic he F hF m =>
      obtain ⟨f⟩ := m
      exact Sylow.self_normalizing_of_surjective f.symm.toMonoidHom f.symm.surjective
        (Theory.SpecificGroups.SymplecticFour.derived_sylow_normalizer_eq_of_card_two
          (by simpa using hF)) P
  | g2 he F hF m =>
      obtain ⟨f⟩ := m
      exact Sylow.self_normalizing_of_surjective f.symm.toMonoidHom f.symm.surjective
        (g2_sylow_self_normalizing_of_card_two (by simpa using hF)) P
  | binary_linear he n hn m =>
      obtain ⟨f⟩ := m
      exact Sylow.self_normalizing_of_surjective f.symm.toMonoidHom f.symm.surjective
        (binary_psl_sylow_self_normalizing (by omega)) P

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.BinaryModels
