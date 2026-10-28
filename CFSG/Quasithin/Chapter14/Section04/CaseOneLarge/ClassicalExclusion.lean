module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.RankOneExclusion
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.ComponentBounds
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank.SourceBound
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.Representation.Quotient
public import Theory.Representation.SymplecticNormalActors.Inner
public import CFSG.Quasithin.ChapterG.Section11.WholeG2
public import Theory.Representation.G2LargeActors
public import CFSG.Quasithin.ChapterG.Section10.CoefficientField.FixedSpace
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.SmallCodimension
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Nonbinary symplectic and G₂ components in the original large action

Natural recognition identifies the actual component modules. Relative Sylow
normality puts the elementary actor inside a symplectic component. A nonbinary
scalar then forces fixed codimension at most two, hence actor rank at most n.
The original G.9 inequality gives rank at least 2n-1, a contradiction for n ≥ 2.

For G₂ the original degree and automorphism-rank bounds make the actor large
enough to be coefficient-linear. The marked transvection geometry then forces
the coefficient field to be binary. Neither argument assumes a low-rank
witness or the stronger half-degree actor bound. Thus both G.11 fixed-point
clauses are covered, on the original flag and literal terminal quotient.

The symplectic coordinates adapt ChapterG.Section11.LargeWholeSymplectic;
the G₂ coefficient argument uses the same interface as
Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.
ComponentCatalogueMarkedWholeG2. The remaining component recognition and
multiplicity branches still belong to the large-case assembly.

Source: Aschbacher--Smith G.9.3(9--10), G.11.7 and 14.4.2,
printed pp.354,367--368,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ClassicalComponents
open ChapterG ChapterG.Section11 ChapterG.Section09
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
private theorem not_nonbinary_symplectic
    (h : Section10.Hypothesis ρ B v W X X₀)
    (hS : NormalSylow ρ v X)
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
  have hdegree := h9.degree_le
  omega


/-- The near-maximum actor is coefficient-linear in the natural G₂ module.
The marked geometry then forces the nonbinary field to be binary. -/
private theorem not_nonbinary_g2
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : ComponentHypothesis C ρ X L L (finrank (ZMod 2) (Additive X)))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e₀ : L ≃* Atlas.G2.Model k) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card k = 2^n) : False := by
  classical
  let := h9.normal_H
  let := h9.irreducible
  have hr := (Section09.DefiningCharacteristic.G2Recognition.actor_bound_of_model_rank h9 e₀
    (Atlas.G2.EvenTwoRank.source_automorphism_two_rank_le k hn hcard)).1
  obtain ⟨e,c,hc⟩ := WholeG2.natural_of_component h9 e₀ hn hcard
  have hd : finrank (ZMod 2) V = 6*n :=
    c.finrank_eq.trans (Section09.DefiningCharacteristic.G2Recognition.naturalBinary_degree k hcard)
  have hb := h9.degree_le
  have hactor : 2^(3*n-1) ≤ Nat.card X := by
    rw [h9.card_actor]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  let : SMul (ZMod 2) k := (ZMod.algebra k 2).toSMul
  let : Module k V := c.toAddEquiv.module k
  let : IsScalarTower (ZMod 2) k V :=
    IsScalarTower.of_algebraMap_smul (fun a w => by
      fin_cases a
      · change algebraMap (ZMod 2) k (0 : ZMod 2) • w = (0 : ZMod 2) • w
        simp only [map_zero,zero_smul]
      · change algebraMap (ZMod 2) k (1 : ZMod 2) • w = (1 : ZMod 2) • w
        simp only [map_one,one_smul])
  have hlin := Representation.G2LargeActors.coefficient_linear ρ L X h.faithful e hn hcard
    hactor (by
      intro l a w
      apply c.injective
      change c (ρ l (c.symm (a • c w))) = c (c.symm (a • c (ρ l w)))
      rw [c.apply_symm_apply]
      change c ((ρ.comp L.subtype) l (c.symm (a • c w))) = _
      rw [hc,c.apply_symm_apply]
      change Atlas.G2.Natural.action k (e l) (a • c w) = _
      rw [map_smul]
      have hh := hc l w
      exact congrArg (a • ·) hh.symm)
  have hq := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
    (QuotientGroup.mk'_surjective X₀)).trans (IsElementaryAbelian.rank_le_finrank (p := 2) X)
  have hW : 3 ≤ finrank (ZMod 2) W := by have := h.dimension; omega
  have hsmall := h.coefficient_card_le_two (K := k) hlin hW
  rw [hcard] at hsmall
  have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hn
  norm_num at hpow
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ClassicalComponents

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original terminal action has no normal irreducible nonbinary
symplectic component. No low-rank witness or enlarged actor bound is assumed. -/
theorem source_no_nonbinary_symplectic_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    {n : ℕ} (hn : 2 ≤ n) (model : ClassicalGroup.IsPSp C 2 (2^n)) : False := by
  obtain ⟨_,_,B,v,hyp,_,hfix⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v
      (F.terminalDot (F.X g)) :=
    ⟨_,hfix,source_terminal_actor_normal_in_sylow d earlier hq chosen structural alternatives
      F hne g hgP hgH⟩
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  exact ClassicalComponents.not_nonbinary_symplectic hyp hS h9 hn model

/-- Both fixed-point clauses exclude a normal irreducible nonbinary G₂
component of the original terminal action. -/
theorem source_no_nonbinary_g2_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    {n : ℕ} (hn : 2 ≤ n) (model : ClassificationModels.IsG2At C (2^n)) : False := by
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation (F.terminalDot (F.X g)) C C
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := {
    toSetup := ChapterG.Section11.setup hyp
    quotient := source_terminal_cover F d chosen
    component := hC
    noncentral := hm
    normal_H := inferInstance
    irreducible := hirr
    components := Or.inl rfl }
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact ClassicalComponents.not_nonbinary_g2 hyp h9 e hn hcard
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
