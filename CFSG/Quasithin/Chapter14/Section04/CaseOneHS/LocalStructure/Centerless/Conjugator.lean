module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Shifted
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The third point in the original HS flag

A common natural marking of the original flag supplies three basis points.
Lift the swaps (0,1) and (0,2) through the actual full L-action. The first
is the omitted-point conjugator; the second fixes the displaced point and
moves the original point outside the plane. Counting their elementary
joins proves both plane identities and generation of the seed.

This constructs the source conjugator without an extra geometric premise.
ResidualPair uses this geometry to construct the generating residual pair.
The faithful exclusion of Z(LT) ∩ U remains a step of the centerlessness argument.
Source: Aschbacher--Smith, setup of 14.3.28, printed pp.1001--1002.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem lift_basis_permutation [IsElementaryAbelian 2 V]
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (β : Additive V ≃ₗ[ZMod 2] Space 3) (b : Basis 2) (s : Equiv.Perm (Fin 3)) :
    ∃ x ∈ L, ∀ i : Fin 3,
      x⁻¹ * ((β.symm (b i)).toMul : G) * x = (β.symm (b (s i))).toMul := by
  let a := (naturalFlagActorEquiv β).symm (b.equiv b s)
  obtain ⟨x, hx, he⟩ := hfull a
  refine ⟨x⁻¹, L.inv_mem hx, ?_⟩
  intro i
  simp only [inv_inv]
  rw [he]
  congr 1
  apply Additive.ofMul.injective
  apply β.injective
  have hh := naturalFlagActorEquiv_intertwines β a (β.symm (b i)).toMul
  rw [show naturalFlagActorEquiv β a = b.equiv b s from
    (naturalFlagActorEquiv β).apply_symm_apply _, ofMul_toMul, β.apply_symm_apply,
    Module.Basis.equiv_apply] at hh
  simpa only [ofMul_toMul, β.apply_symm_apply] using hh.symm

omit [Finite G] in
private theorem basis_point_ne_one [IsElementaryAbelian 2 V]
    (β : Additive V ≃ₗ[ZMod 2] Space 3) (b : Basis 2) (i : Fin 3) :
    ((β.symm (b i)).toMul : G) ≠ 1 := by
  intro he
  have hv : (β.symm (b i)).toMul = 1 := Subtype.ext he
  have hz : β.symm (b i) = 0 := congrArg Additive.ofMul hv
  exact b.ne_zero i (β.symm.injective (hz.trans β.symm.map_zero.symm))

omit [Finite G] in
private theorem basis_point_in_cut [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V 3) (β : Additive V ≃ₗ[ZMod 2] Space 3) (b : Basis 2)
    (hc : ∀ i : Fin 2, F.naturalFlagSpace β (i.val + 1) = cutSpace b i)
    (i : Fin 2) (j : Fin 3) :
    ((β.symm (b j)).toMul : G) ∈ F.Vi (i.val + 1) ↔ j.val ≤ i.val := by
  rw [← F.mem_naturalFlagSpace β (i.val + 1), ofMul_toMul, β.apply_symm_apply,
    hc, basis_mem_cutSpace]

omit [Finite G] in
private theorem seed_normalizes_subgroup [IsMulCommutative V]
    (A : Subgroup G) (hA : A ≤ V) : V ≤ normalizer (A : Set G) := by
  have hVV : V ≤ centralizer (V : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  apply hVV.trans
  exact (centralizer_le hA).trans (Subgroup.centralizer_le_normalizer _)

/-- Construct the actual third-point conjugator from the original full L-action. -/
theorem source_shifted_conjugator (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) :
    ∃ g l : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ l ∈ L ∧
      l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      F.Vi 2 = F.Vi 1 ⊔ conjugate (F.Vi 1) g ∧
      V = F.Vi 2 ⊔ conjugate (F.Vi 1) l ∧
      conjugate (F.Vi 2) l = conjugate (F.Vi 1) g ⊔ conjugate (F.Vi 1) l := by
  classical
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  let β := h.naturalMarking.coordinates
  obtain ⟨b, _, hc⟩ := F.exists_naturalFlag_marking L chosen.normalizes h.full_L_action β
  let v : Fin 3 → G := fun i => (β.symm (b i)).toMul
  have hv (i : Fin 3) : v i ∈ V := (β.symm (b i)).toMul.property
  have hv1 (i : Fin 3) : v i ≠ 1 := basis_point_ne_one β b i
  have hv2 (i : Fin 3) : v i ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _ (hv i)
  have hp : F.Vi 1 = zpowers (v 0) := by
    symm
    apply eq_of_le_of_card_ge
      (zpowers_le.mpr ((basis_point_in_cut F β b hc 0 0).mpr (by decide)))
    rw [Nat.card_zpowers, orderOf_eq_prime_iff.mpr ⟨hv2 0, hv1 0⟩]
    simpa using (F.card 1 (by decide)).le
  have hv10 : v 1 ∉ F.Vi 1 := by
    exact fun hh => (by decide : ¬ (1 : Fin 3).val ≤ (0 : Fin 2).val)
      ((basis_point_in_cut F β b hc 0 1).mp hh)
  have hv12 : v 1 ∈ F.Vi 2 := (basis_point_in_cut F β b hc 1 1).mpr (by decide)
  have hv22 : v 2 ∉ F.Vi 2 := by
    exact fun hh => (by decide : ¬ (2 : Fin 3).val ≤ (1 : Fin 2).val)
      ((basis_point_in_cut F β b hc 1 2).mp hh)
  have hplane : F.Vi 2 = F.Vi 1 ⊔ zpowers (v 1) := by
    symm
    apply eq_of_le_of_card_ge (sup_le (F.monotone (by decide)) (zpowers_le.mpr hv12))
    rw [card_sup_zpowers_of_normalizing_involution _ _ (hv2 1) hv10
      (seed_normalizes_subgroup _ (F.le_seed 1) (hv 1))]
    norm_num [F.card 1 (by decide), F.card 2 (by decide)]
  have hspace : V = F.Vi 2 ⊔ zpowers (v 2) := by
    symm
    apply eq_of_le_of_card_ge (sup_le (F.le_seed 2) (zpowers_le.mpr (hv 2)))
    rw [card_sup_zpowers_of_normalizing_involution _ _ (hv2 2) hv22
      (seed_normalizes_subgroup _ (F.le_seed 2) (hv 2))]
    have hvcard : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    norm_num [hvcard, F.card 2 (by decide)]
  obtain ⟨g, hgL, hg⟩ := lift_basis_permutation h.full_L_action β b (Equiv.swap 0 1)
  obtain ⟨l, hlL, hl⟩ := lift_basis_permutation h.full_L_action β b (Equiv.swap 0 2)
  have hg0 : g⁻¹ * v 0 * g = v 1 := by simpa only [Equiv.swap_apply_left] using hg 0
  have hg1 : g⁻¹ * v 1 * g = v 0 := by simpa only [Equiv.swap_apply_right] using hg 1
  have hl0 : l⁻¹ * v 0 * l = v 2 := by simpa only [Equiv.swap_apply_left] using hl 0
  have hl1 : l⁻¹ * v 1 * l = v 1 := by simpa only [Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)] using hl 1
  have hgp : conjugate (F.Vi 1) g = zpowers (v 1) := by
    rw [hp, conjugate, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hg0]
  have hlp : conjugate (F.Vi 1) l = zpowers (v 2) := by
    rw [hp, conjugate, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hl0]
  have hgplane : conjugate (F.Vi 2) g = F.Vi 2 := by
    rw [hplane, hp]
    simp only [conjugate, Subgroup.map_sup, MonoidHom.map_zpowers, MulAut.conj_apply,
      MulEquiv.coe_toMonoidHom, inv_inv, hg0, hg1]
    exact sup_comm _ _
  have hgP : g ∈ F.P L := by
    refine ⟨mem_sup_left hgL, ?_⟩
    apply Subgroup.mem_iInf.mpr
    intro i
    apply Subgroup.mem_iInf.mpr
    intro hi
    have he : i = 2 := by omega
    subst i
    exact (conjugate_eq_iff _ _).mp hgplane
  have hgH : g ∉ F.H := by
    intro hh
    have he := (conjugate_eq_iff (F.Vi 1) g).mpr hh
    rw [hgp] at he
    exact hv10 (he ▸ mem_zpowers (v 1))
  have hlC : l ∈ centralizer (conjugate (F.Vi 1) g : Set G) := by
    rw [hgp, zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    have hh := congrArg (fun x : G => l * x) hl1
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh.symm
  refine ⟨g, l, hgL, hgP, hgH, hlL, hlC, ?_, ?_, ?_⟩
  · rw [hgp]; exact hplane
  · rw [hlp]; exact hspace
  · rw [hgp, hlp, hplane, hp]
    simp only [conjugate, Subgroup.map_sup, MonoidHom.map_zpowers, MulAut.conj_apply,
      MulEquiv.coe_toMonoidHom, inv_inv, hl0, hl1]
    exact sup_comm _ _

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
