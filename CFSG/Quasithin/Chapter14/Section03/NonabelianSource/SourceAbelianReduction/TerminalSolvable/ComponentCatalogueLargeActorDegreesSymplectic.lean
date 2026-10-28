module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesWholePair
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
# Excluding the whole nonbinary symplectic action for the original larger actor

The original G.9 degree window recognizes the natural Sp₄(2ⁿ) action.
Normality in the actual Sylow forces the elementary actor into that component.
A nonbinary coefficient scalar moves the marked point, so the G.10
transvection geometry bounds the common fixed codimension by two. The natural
root-rank bound then contradicts the original larger-actor inequality.

The final theorems apply this exclusion to the numerical reduction and its
actual component consumer. Only the marked whole S₈ action remains open;
the successful degree-six alternative still identifies the full dotted G₂(2).
No strict D hypotheses or small-actor dimension equality are used.

Source: Aschbacher–Smith G.9.3(9), G.11.7 and 14.3.14,
printed pp.354,367–368,994 of refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterG.Section11 ChapterG.Section09
open ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
open Theory.SpecificGroups.SymplecticFour
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s
attribute [local instance] ZMod.algebra

/-- Natural recognition and the original Sylow normality exclude every
whole nonbinary symplectic component. -/
theorem not_whole_nonbinary_symplectic {L : Subgroup F.TerminalHdot}
    (h9 : ComponentHypothesis KnownSimple.IsKnownSimple F.terminalRepresentation
      (F.terminalDot (F.X g)) L L
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))
    {n : ℕ} (hn : 2 ≤ n) (model : ClassicalGroup.IsPSp L 2 (2^n)) : False := by
  classical
  obtain ⟨k,_,_,hcard,⟨e₀⟩⟩ := model
  let : CharP k 2 := EvenProjective.charTwo_of_card hcard
  let a := (e₀.trans EvenProjective.equiv.symm).trans (EvenTwoRank.derivedEquiv hcard hn).symm
  let σ := (F.terminalRepresentation.comp L.subtype).comp a.symm.toMonoidHom
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
  let τ : Representation (ZMod 2) F.TerminalHdot (Vector k) :=
    c.conjRingEquiv.toMonoidHom.comp F.terminalRepresentation
  have ht (x : F.TerminalHdot) (w : Vector k) :
      τ x w = c (F.terminalRepresentation x (c.symm w)) := rfl
  have hτ (l : L) (w : Vector k) : τ l w = symplecticNatural 2 (ef l) w := by
    rw [ht]
    change c ((F.terminalRepresentation.comp L.subtype) l (c.symm w)) = _
    rw [hc,c.apply_symm_apply]
    simp only [ef,MulEquiv.trans_apply,derivedEquivFull_of_card_gt_two_apply]
    rfl
  have hfaith : Function.Injective τ := by
    intro x y he
    apply s.hypothesis.faithful
    apply LinearMap.ext
    intro w
    apply c.injective
    have hh := LinearMap.congr_fun he (c w)
    simpa only [ht,c.symm_apply_apply] using hh
  obtain ⟨S,_,hXS,hXn⟩ := s.normal_sylow
  have hXL := Representation.SymplecticNormalActors.natural_normal_actor_le
    τ hfaith L (F.terminalDot (F.X g)) ef hτ hn hcard S hXS hXn
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
  let J : Additive F.Uhat ≃ₗ[ZMod 2] Additive F.Uhat :=
    (c.trans ((LinearEquiv.smulOfNeZero k (Vector k) z hz).restrictScalars (ZMod 2))).trans c.symm
  have hJ (w : Additive F.Uhat) : c (J w) = z • c w := c.apply_symm_apply _
  have hcomm (x : F.terminalDot (F.X g)) (w : Additive F.Uhat) :
      F.terminalRepresentation x (J w) = J (F.terminalRepresentation x w) := by
    let l : L := ⟨x,hXL x.property⟩
    apply c.injective
    change c ((F.terminalRepresentation.comp L.subtype) l (J w)) =
      c (J ((F.terminalRepresentation.comp L.subtype) l w))
    rw [hc,hJ,hJ,hc]
    exact (symplecticDerivedNatural 2 (e l)).map_smul z (c w)
  have hjv : J v ≠ v := by
    intro he
    have hh : z • c v = (1 : k) • c v := by rw [←hJ,he,one_smul]
    exact hz1 (smul_left_injective k
      (fun hh => s.hypothesis.point_ne_zero (c.map_eq_zero_iff.mp hh)) hh)
  have hcod := s.hypothesis.fixedCodim_le_two_of_centralizing_moves_point J hcomm hjv
  let A := ((F.terminalDot (F.X g)).subgroupOf L).map ef.toMonoidHom
  let : IsElementaryAbelian 2 ((F.terminalDot (F.X g)).subgroupOf L) :=
    IsElementaryAbelian.subgroupOf hXL
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map ef.toMonoidHom
  have heq : fixedCodim F.terminalRepresentation (F.terminalDot (F.X g)) =
      fixedCodim (SymplecticConjugatePair.binaryNatural (F := k)) A := by
    have hh := fixedCodim_map_equivariant (F.terminalRepresentation.comp L.subtype)
      (SymplecticConjugatePair.binaryNatural (F := k)) ef.toMonoidHom c
      (fun l w => by
        have hh := hτ l (c w)
        rw [ht,c.symm_apply_apply] at hh
        exact hh) ((F.terminalDot (F.X g)).subgroupOf L)
    rw [fixedCodim,fixedSpace_comp_map,map_subgroupOf_eq_of_le hXL] at hh
    exact hh
  have hAc : Nat.card A = Nat.card (F.terminalDot (F.X g)) := by
    rw [card_map_of_injective ef.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hXL).toEquiv
  have hr : rank A = finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
    rw [rank,hAc,h9.card_actor,Nat.log_pow (by decide : 1<2)]
  have hane : A ≠ ⊥ := by
    intro he
    have hh := s.two_le_actor
    rw [←hr,he,rank,Subgroup.card_bot] at hh
    norm_num at hh
  have hbound := SymplecticConjugatePair.NaturalBounds.natural_small_codim_rank_le
    hcard (by omega) ⟨hane,inferInstance⟩ (by rw [←heq]; omega)
  rw [hr] at hbound
  have hlarge := s.half_degree_le_actor
  omega

/-- All whole-component recognition branches are discharged. The exceptional
marked S₈ action is the sole remaining alternative to the source degrees. -/
theorem degree_cases_or_full_four :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) := by
  rcases s.degree_cases_or_full_four_or_symplectic with good | full | ⟨_,L,_,_,_,h9,hHL,_,n,hn,hm⟩
  · exact Or.inl good
  · exact Or.inr full
  · rw [hHL] at h9
    exact (s.not_whole_nonbinary_symplectic h9 hn hm).elim

/-- Apply the refined degree alternative to the original component consumer,
preserving the full dotted-group identification in degree six. -/
theorem component_or_full_four
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    ((∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
      (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
        Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
        F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
          pCore 2 (K.subgroupOf F.H))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) := by
  rcases s.degree_cases_or_full_four with hd | hr
  · exact Or.inl (source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis hd hfour hsix)
  · exact Or.inr hr

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
