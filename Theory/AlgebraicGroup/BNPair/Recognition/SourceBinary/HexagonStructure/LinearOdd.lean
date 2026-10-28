module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.ReflectionPinning
public import Theory.SpecificGroups.SL2.TwoCore
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The odd reflection--unipotent product in the actual linear local group

The whole aligned SL₂ pinning constructs an involution u in the canonical
simple root for which the specified source reflection s satisfies (su)³=1.
Every nontrivial normal subgroup of the actual root-generated group contains
this product. For fields of order at least four this follows from simplicity
of the concrete PSL₂ model. At order two the group has order six and trivial
two-core, which gives the same conclusion without simplicity or perfectness.

These are the odd-product construction and local normal-subgroup argument
used by EffectiveSections, not assumptions about an unknown ambient group.
Source: Fong--Seitz I (5D)(b), printed pp.26--27. Only the whole local pinning
is used from GTwoSource; no later mixed-root equations are required.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates Theory.PSL2.SemilinearCoverage GTwoSource
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every nontrivial normal subgroup of binary SL₂ contains every cubic
    element. The order-six case is treated without simplicity. -/
theorem linear_normal_contains_cubic (N : Subgroup (SL2 F)) [N.Normal]
    (hne : N ≠ ⊥) (c : SL2 F) (hc : c^3 = 1) : c ∈ N := by
  by_cases hF : Nat.card F = 2
  · have hcard : Nat.card (SL2 F) = 6 := by
      rw [BenderSuzuki.External.huppert614_card_specialLinearGroup, hF]
      norm_num
    have hNdiv : Nat.card N ∣ 6 := hcard ▸ N.card_subgroup_dvd_card
    have hNne : Nat.card N ≠ 1 := fun h => hne (card_eq_one.mp h)
    have hNne2 : Nat.card N ≠ 2 := by
      intro h
      have htwo : IsPGroup 2 N := IsPGroup.of_card (n := 1) (by simpa using h)
      have hle : N ≤ pCore 2 (SL2 F) := le_sSup ⟨inferInstance,htwo⟩
      rw [Matrix.SL2.twoCore_eq_bot] at hle
      exact hne (bot_unique hle)
    have hNle := Nat.le_of_dvd (by decide : 0 < 6) hNdiv
    have hNc : Nat.card N = 3 ∨ Nat.card N = 6 := by
      interval_cases hk : Nat.card N <;> omega
    have hindex : N.index ∣ 2 := by
      have he := N.index_mul_card
      rw [hcard] at he
      rcases hNc with h3 | h6
      · rw [h3] at he
        have : N.index = 2 := by omega
        simp [this]
      · rw [h6] at he
        have : N.index = 1 := by omega
        simp [this]
    apply (QuotientGroup.eq_one_iff c).mp
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
    · exact (orderOf_dvd_natCard (QuotientGroup.mk' N c)).trans hindex
    · apply orderOf_dvd_of_pow_eq_one
      change (QuotientGroup.mk' N c)^3 = 1
      rw [←map_pow, hc, map_one]
  · have hlarge : 3 < Nat.card F := by
      let : Fintype F := Fintype.ofFinite F
      have hlo := Fintype.one_lt_card (α := F)
      have hdiv : 2 ∣ Nat.card F := by
        rw [Nat.card_eq_fintype_card]
        exact (CharP.cast_eq_zero_iff F 2 _).mp (FiniteField.cast_card_eq_zero F)
      rw [←Nat.card_eq_fintype_card] at hlo
      omega
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
    let : IsSimpleGroup (SL2 F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
    rw [(inferInstance : N.Normal).eq_bot_or_eq_top.resolve_left hne]
    trivial

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)

/-- The chosen unipotent involution in the same canonical simple root. -/
def oddPartner : rankOne Q split i := alignedPinning Q split i hV μ s (uni 1)

theorem oddPartner_mem_root : (oddPartner Q split i hV μ s : X ⧸ Q.D) ∈ simpleRoot Q split i := by
  rw [←alignedPinningHom_unip_map Q split i hV μ s]
  exact mem_map_of_mem _ ((mem_Unip_iff _).mpr ⟨1,rfl⟩)

theorem oddPartner_sq : (oddPartner Q split i hV μ s)^2 = 1 := by
  change (alignedPinning Q split i hV μ s (uni 1))^2 = 1
  rw [←map_pow]
  have hu : (uni (1 : F))^2 = 1 := by
    rw [pow_two, uni_mul_uni, CharTwo.add_self_eq_zero]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [uni]
  rw [hu, map_one]

theorem oddPartner_ne_one : oddPartner Q split i hV μ s ≠ 1 := by
  intro h
  have he := (alignedPinning Q split i hV μ s).injective (h.trans (map_one _).symm)
  have h01 := congrArg (fun a : SL2 F => a.val 0 1) he
  simp [uni] at h01

/-- This is the product of the specified source reflection and its chosen
    unipotent involution, not a detached model element. -/
def oddProduct : rankOne Q split i := ⟨s.val,s.mem_rankOne⟩ * oddPartner Q split i hV μ s

@[simp] theorem oddProduct_coe :
    (oddProduct Q split i hV μ s : X ⧸ Q.D) =
      (s.val : X ⧸ Q.D) * (oddPartner Q split i hV μ s : X ⧸ Q.D) := by rfl

theorem oddProduct_cube : (oddProduct Q split i hV μ s)^3 = 1 := by
  have hs : (⟨s.val,s.mem_rankOne⟩ : rankOne Q split i) =
      alignedPinning Q split i hV μ s (weyl F) := by
    apply Subtype.ext
    exact (alignedPinningHom_weyl Q split i hV μ s).symm
  rw [oddProduct, hs, oddPartner, ←map_mul, ←map_pow]
  have hc : (weyl F * uni 1)^3 = 1 := by
    apply Subtype.ext
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  rw [hc, map_one]

theorem oddProduct_order_coprime : Nat.Coprime (orderOf (oddProduct Q split i hV μ s)) 2 :=
  (by decide : Nat.Coprime 3 2).of_dvd_left
    (orderOf_dvd_of_pow_eq_one (oddProduct_cube Q split i hV μ s))

/-- The genuine local normal-subgroup step in (5D)(b), including q=2. -/
theorem linear_kernel_contains_oddProduct (T : Subgroup (rankOne Q split i)) [T.Normal]
    (hne : T ≠ ⊥) : oddProduct Q split i hV μ s ∈ T := by
  let e := alignedPinning Q split i hV μ s
  have hn : T.comap e.toMonoidHom ≠ ⊥ := by
    intro hz
    have he := congrArg (Subgroup.map e.toMonoidHom) hz
    rw [map_comap_eq_self_of_surjective e.surjective, Subgroup.map_bot] at he
    exact hne he
  have hc := linear_normal_contains_cubic (T.comap e.toMonoidHom) hn
    (e.symm (oddProduct Q split i hV μ s)) (by rw [←map_pow, oddProduct_cube, map_one])
  change e (e.symm (oddProduct Q split i hV μ s)) ∈ T at hc
  simpa only [MulEquiv.apply_symm_apply] using hc
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
