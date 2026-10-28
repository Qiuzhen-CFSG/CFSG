module
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.ComponentBounds
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank.SourceBound
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.Representation.Quotient
public import Theory.Representation.SymplecticNormalActors.Inner
public import CFSG.Quasithin.ChapterG.Section10.CoefficientField.FixedSpace
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.SmallCodimension
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Excluding whole nonbinary symplectic components for a large actor

Natural-module recognition and relative Sylow normality put the original
actor in Sp4. A nonbinary coefficient scalar moves the marked point;
the G.10 geometry then bounds the fixed codimension by two. The natural
root bound contradicts the actor's half-degree inequality.

This extracts the general argument from Chapter14's larger-actor source,
for application to the original rank-three HS action as well.
Source: Aschbacher--Smith G.9.3(9), G.11.7, 14.3.24, pp.354,368,1000.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section11.LargeWhole
open Section09
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
    {v : V} {W : Submodule (ZMod 2) V} {X L H : Subgroup G}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X} {C : GroupClass}
open Section09.DefiningCharacteristic.SymplecticFourRecognition
open Theory.SpecificGroups.SymplecticFour
attribute [local instance] ZMod.algebra

/-- Natural recognition and the original Sylow normality exclude every
whole nonbinary symplectic component. -/
theorem not_nonbinary_symplectic
    (h : Section10.Hypothesis ρ B v W X X₀)
    (hS : NormalSylow ρ v X)
    (hlarge : finrank (ZMod 2) V ≤ 2 * finrank (ZMod 2) (Additive X))
    (h9 : ComponentHypothesis C ρ
      X L L
      (finrank (ZMod 2) (Additive X)))
    {n : ℕ} (hn : 2 ≤ n) (model : ClassicalGroup.IsPSp L 2 (2^n)) : False := by
  classical
  obtain ⟨k,_,_,hcard,⟨e₀⟩⟩ := model
  let : CharP k 2 := EvenProjective.charTwo_of_card hcard
  let a := (e₀.trans EvenProjective.equiv.symm).trans (EvenTwoRank.derivedEquiv hcard hn).symm
  let σ := (ρ.comp L.subtype).comp a.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff a.symm.toMonoidHom a.symm.surjective _).mpr h9.irreducible
  have hf : Function.Injective σ := h9.faithful.comp (L.subtype_injective.comp a.symm.injective)
  have hw := component_degree_window_of_automorphism_rank h9 a
    (EvenTwoRank.derived_automorphism_rank_le hcard hn)
  have hnat := quasiequivalent_of_comp_equiv a
    (Nonbinary.small_quasiequivalent hn hcard hf hw.2)
  have hd := finrank_of_quasiequivalent hcard hnat
  have hq : 2 < Nat.card k := by
    rw [hcard]
    simpa using Nat.pow_lt_pow_right (by decide : 1<2) (show 1<n by omega)
  obtain ⟨e,c,hc⟩ := hnat
  let ef := e.trans (derivedEquivFull_of_card_gt_two hq)
  let : L.Normal := h9.normal_H
  let τ : Representation (ZMod 2) G (Vector k) :=
    c.conjRingEquiv.toMonoidHom.comp ρ
  have ht (x : G) (w : Vector k) :
      τ x w = c (ρ x (c.symm w)) := rfl
  have hτ (l : L) (w : Vector k) : τ l w = symplecticNatural 2 (ef l) w := by
    rw [ht]
    change c ((ρ.comp L.subtype) l (c.symm w)) = _
    rw [hc,c.apply_symm_apply]
    simp only [ef,MulEquiv.trans_apply,derivedEquivFull_of_card_gt_two_apply]
    rfl
  have hfaith : Function.Injective τ := by
    intro x y he
    apply h.faithful
    apply LinearMap.ext
    intro w
    apply c.injective
    have hh := LinearMap.congr_fun he (c w)
    simpa only [ht,c.symm_apply_apply] using hh
  obtain ⟨S,_,hXS,hXn⟩ := hS
  have hXL := Representation.SymplecticNormalActors.natural_normal_actor_le
    τ hfaith L X ef hτ hn hcard S hXS hXn
  obtain ⟨z,hz,hz1⟩ : ∃ z : k, z ≠ 0 ∧ z ≠ 1 := by
    by_contra! hh
    have hb : Nat.card k ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective
      (fun z : k => (if z = 0 then (0 : Fin 2) else 1)) (by
        intro z w he
        by_cases hz : z=0 <;> by_cases hw : w=0
        · exact hz.trans hw.symm
        · simp [hz,hw] at he
        · simp [hz,hw] at he
        · exact (hh z hz).trans (hh w hw).symm)
    simp only [Nat.card_fin] at hb
    omega
  let J : V ≃ₗ[ZMod 2] V :=
    (c.trans ((LinearEquiv.smulOfNeZero k (Vector k) z hz).restrictScalars (ZMod 2))).trans c.symm
  have hJ (w : V) : c (J w) = z • c w := c.apply_symm_apply _
  have hcomm (x : X) (w : V) :
      ρ x (J w) = J (ρ x w) := by
    let l : L := ⟨x,hXL x.property⟩
    apply c.injective
    change c ((ρ.comp L.subtype) l (J w)) =
      c (J ((ρ.comp L.subtype) l w))
    rw [hc,hJ,hJ,hc]
    exact (symplecticDerivedNatural 2 (e l)).map_smul z (c w)
  have hjv : J v ≠ v := by
    intro he
    have hh : z • c v = (1 : k) • c v := by rw [←hJ,he,one_smul]
    exact hz1 (smul_left_injective k
      (fun hh => h.point_ne_zero (c.map_eq_zero_iff.mp hh)) hh)
  have hcod := h.fixedCodim_le_two_of_centralizing_moves_point J hcomm hjv
  let A := (X.subgroupOf L).map ef.toMonoidHom
  let : IsElementaryAbelian 2 (X.subgroupOf L) :=
    IsElementaryAbelian.subgroupOf hXL
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map ef.toMonoidHom
  have heq : fixedCodim ρ X =
      fixedCodim (SymplecticConjugatePair.binaryNatural (F := k)) A := by
    have hh := fixedCodim_map_equivariant (ρ.comp L.subtype)
      (SymplecticConjugatePair.binaryNatural (F := k)) ef.toMonoidHom c
      (fun l w => by
        have hh := hτ l (c w)
        rw [ht,c.symm_apply_apply] at hh
        exact hh) (X.subgroupOf L)
    rw [fixedCodim,fixedSpace_comp_map,map_subgroupOf_eq_of_le hXL] at hh
    exact hh
  have hAc : Nat.card A = Nat.card X := by
    rw [card_map_of_injective ef.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hXL).toEquiv
  have hr : rank A = finrank (ZMod 2) (Additive X) := by
    rw [rank,hAc,h9.card_actor,Nat.log_pow (by decide : 1<2)]
  have hane : A ≠ ⊥ := by
    intro he
    have hh := h9.actor_rank_pos
    rw [←hr,he,rank,Subgroup.card_bot] at hh
    norm_num at hh
  have hbound := SymplecticConjugatePair.NaturalBounds.natural_small_codim_rank_le
    hcard (by omega) ⟨hane,inferInstance⟩ (by rw [←heq]; omega)
  rw [hr] at hbound
  have hlarge := hlarge
  omega

end CFSG.Quasithin.ChapterG.Section11.LargeWhole
