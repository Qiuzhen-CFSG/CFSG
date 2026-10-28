module
public import CFSG.Quasithin.MainConverse.AlternatingSections.SixSubgroups
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.Representation.BinarySymplecticFourEmbedding
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActor

/-!
# Components on the original binary symplectic four-space

The actual G.10 hypothesis makes the terminal action faithful and symplectic.
A form isometry embeds it in Sp₄(2), and the concrete polar-action equivalence
then embeds each component in S₆. Perfectness puts that image in A₆. If it is
proper, the independently proved Dickson subgroup theorem in `SixSubgroups`
leaves a solvable group or A₅; nontrivial perfectness excludes solvability.
The full-image case gives A₆. No normality of the component is needed.

The final application discharges `hfour` in the published larger-actor
assembly. The degree alternatives and the A₆ exclusion remain its separate
inputs, as owned by their source branches.

Source: Aschbacher--Smith G.11.2(2), printed p.364, and 14.3.14(2)--14.3.15,
printed p.994. The subgroup calculation uses Huppert II.8.27 through
`MainConverse.AlternatingSections.SixSubgroups`, whose proof is independent
of the quasithin classification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative

private theorem perfect_sixLetter_image {Q : Type*} [Group Q]
    [Group.IsPerfect Q] [Nontrivial Q]
    (f : Q →* Equiv.Perm (Fin 6)) (hf : Function.Injective f) :
    Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (Q ≃* alternatingGroup (Fin 6)) := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hA : f.range ≤ alternatingGroup (Fin 6) := by
    rw [← commutator_eq_self (H := f.range)]
    exact (commutator_mono le_top le_top).trans
      (alternatingGroup.commutator_perm_eq (by norm_num)).le
  let H := f.range.subgroupOf (alternatingGroup (Fin 6))
  let e : Q ≃* H := (MonoidHom.ofInjective hf).trans
    (subgroupOfEquivOfLe hA).symm
  by_cases ht : H = ⊤
  · exact Or.inr ⟨e.trans ((MulEquiv.subgroupCongr ht).trans topEquiv)⟩
  rcases CFSG.Quasithin.MainConverse.alternatingSix_subgroup_solvable_or_altFive
      (MulEquiv.refl _) H ht with hs | ha
  · let := hs
    exact (Group.IsPerfect.not_isSolvable Q
      (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)).elim
  · exact Or.inl (ha.map (fun a => e.trans a))

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- Every ordinary component in the actual four-dimensional terminal action
is A₅ or A₆. In particular this applies to every component moved by the
original dotted actor, without assuming relative normality. -/
theorem terminal_component_smallImage_of_four
    (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 4)
    (D : Subgroup F.TerminalHdot) (hD : IsComponent F.TerminalHdot D) :
    SmallComponentImage D := by
  obtain ⟨_, j, hj, _⟩ := Representation.exists_binarySymplecticFour_embedding
    F.terminalRepresentation hyp.faithful hd B hyp.alternating hyp.nondegenerate hyp.preserves
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  let f : D →* Equiv.Perm (Fin 6) := e.toMonoidHom.comp (j.comp D.subtype)
  let := hD.2
  let : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hD.isCComponent.ne_bot
  exact perfect_sixLetter_image f (e.injective.comp (hj.comp D.subtype_injective))

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Apply the degree-four recognition to the literal larger-actor consumer.
Only the independently owned degree alternatives and A₆ exclusion remain. -/
theorem source_component_large_actor_of_degree_cases_with_four_recognition
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hn : ¬ Group.IsSolvable F.TerminalHdot)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hdegrees :
      (finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2))))
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    (∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
      ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
    (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
      Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
      F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
        pCore 2 (K.subgroupOf F.H)) := by
  exact source_component_large_actor_of_degree_cases
    hG T hempty hM hu hmany hcard e F hne g hgP hgH hn hyp hdegrees
    (fun hd D hD _ => terminal_component_smallImage_of_four F hyp hd D hD) hsix

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
