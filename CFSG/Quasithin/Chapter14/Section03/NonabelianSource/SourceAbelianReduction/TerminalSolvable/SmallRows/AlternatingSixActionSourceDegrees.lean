module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionSourcePoint
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.SingleA5Kernel

/-!
# Terminal A₆ exclusion after the source numerical alternatives

A constituent of the normal A₆ component has dimension at least four. If
the whole space has dimension below eight, distinct conjugates cannot be
disjoint, so the constituent is ambient invariant and equals the whole space.
The existing irreducible recognition supplies the actual natural diagram
action in both larger-actor degrees. The same-component kernel bridge then
removes the radical premise from the source cubic-parabolic exclusion.

Only the independently owned larger-actor numerical alternatives remain;
`qt-e-14315-a6-diagram-source` retains their discharge and the final assembly.
Source: Aschbacher--Smith G.5.1, G.11.2 and14.3.14--15, pp.342,364--367,994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Below degree eight a normal terminal A₆ component acts irreducibly. -/
theorem ComponentLift.alternatingSix_irreducible_of_finrank_lt_eight
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2}
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hd : finrank (ZMod 2) (Additive F.Uhat) < 8) :
    IsIrreducible (F.terminalRepresentation.comp (F.terminalDot K).subtype) := by
  let := hK.alternatingSix_image_normal hG e6
  have hoL : componentOrbit (F.terminalDot K) ⊤ = F.terminalDot K :=
    le_antisymm
      (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl le_normalizer_of_normal)
      (le_componentOrbit _ _)
  have hi := hyp.irreducible_of_not_solvable hK.terminal_not_solvable
  obtain ⟨_,_,I,hI,hirr,_,hdis,_,hdim,_⟩ :=
    componentOrbit_selection F.terminalRepresentation hyp.faithful hi B hyp.alternating
      hyp.preserves hK.image_component (IsElementaryAbelian.isPGroup 2 (F.terminalDot (F.X g)))
  let R := invariantSubspace F.terminalRepresentation (componentOrbit (F.terminalDot K) ⊤)
    I hI.invariant
  let ee := (MulEquiv.subgroupCongr hoL).trans e6
  let σ := R.toRepresentation.comp ee.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff ee.symm.toMonoidHom ee.symm.surjective _).mpr hirr
  have hdeg := BinaryAlternatingSix.alternating_degrees σ
  change finrank (ZMod 2) I = 1 ∨ finrank (ZMod 2) I = 4 ∨
    finrank (ZMod 2) I = 16 at hdeg
  have hfour : 4 ≤ finrank (ZMod 2) I := by omega
  have hinv (a : F.TerminalHdot) : I.map (F.terminalRepresentation a) = I := by
    rcases hdis a with he | hdis
    · exact he
    · have hm := (LinearEquiv.ofBijective (F.terminalRepresentation a)
        (Representation.apply_bijective F.terminalRepresentation a)).finrank_map_eq I
      change finrank (ZMod 2) (I.map (F.terminalRepresentation a)) =
        finrank (ZMod 2) I at hm
      have hl := Submodule.finrank_add_finrank_le_of_disjoint hdis
      omega
  let J : Subrepresentation F.terminalRepresentation :=
    ⟨I, fun a w hw => hinv a ▸ Submodule.mem_map_of_mem hw⟩
  have htop : I = ⊤ := by
    rcases hi.eq_bot_or_eq_top J with hb | ht
    · have hbI : I = ⊥ := congrArg Subrepresentation.toSubmodule hb
      rw [hbI,finrank_bot] at hdim
      omega
    · exact congrArg Subrepresentation.toSubmodule ht
  subst I
  let eR : Representation.Equiv
      (invariantSubspace F.terminalRepresentation (componentOrbit (F.terminalDot K) ⊤)
        ⊤ hI.invariant).toRepresentation
      (F.terminalRepresentation.comp (componentOrbit (F.terminalDot K) ⊤).subtype) :=
    .mk Submodule.topEquiv (by intro a; apply LinearMap.ext; intro x; rfl)
  have hh := (RepEquiv.ofRepresentationEquiv eR.symm).irreducible_of_euqiv hirr
  exact (congrArg (fun A : Subgroup F.TerminalHdot =>
    IsIrreducible (F.terminalRepresentation.comp A.subtype)) hoL).mp hh

/-- All local A₆ obligations are discharged once the original numerical
alternatives are supplied: proper-point selection, actual coordinates, the
natural Sylow diagram action, and the radical/two-core comparison. The only
remaining source input is produced by `qt-e-14314-large-actor-degree-cases`;
this task retains the final unconditional assembly. -/
theorem source_terminal_a6_false_of_terminal_degrees
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (hne : ¬ IsMulCommutative F.U) (g : G)
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hdegrees :
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
        finrank (ZMod 2) (Additive F.Uhat) / 2 - 1) ∨
      finrank (ZMod 2) (Additive F.Uhat) = 4 ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3)) : False := by
  have hA : hK.AlternatingSixNaturalAction e6 := by
    rcases hdegrees with hsmall | hd | ⟨hd,_⟩
    · exact source_terminal_a6_natural_action_of_small_actor
        hG T hempty hM hu hmany hcard e F hnot hne g hgP hgH hK e6 hyp hsmall
    all_goals
      apply hK.alternatingSixNaturalAction_of_irreducible
        hG T hempty hM hu hmany hcard e F hne g hgP hgH e6
      exact hK.alternatingSix_irreducible_of_finrank_lt_eight hG e6 hyp (by omega)
  have hk := hK.radical_eq_twoCore_of_terminal_degrees
    (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e)
    hne hgP hgH hyp (Or.inr ⟨e6⟩) hdegrees
  exact source_terminal_a6_false_of_radical_and_action
    hG T hempty hM hu hmany hcard e hnot hK e6 hk hA

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
