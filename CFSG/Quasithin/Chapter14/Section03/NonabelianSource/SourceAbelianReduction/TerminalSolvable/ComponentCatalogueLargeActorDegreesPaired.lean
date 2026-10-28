module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesNatural
public import CFSG.Quasithin.ChapterG.Section10.Components.ExchangedFaithfulPair
public import Theory.Representation.NormalComponentConstituents.ElementaryKernel
public import Theory.GroupTheory.GeneralizedFitting.ElementarySylowOrbit
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions

/-!
# Excluding the remaining natural exchanged action for a larger actor

The two actual exchanged constituents separate the normal component orbit.
Normality of the original elementary actor in its point Sylow makes the
Sylow intersection with the constituent kernel elementary. The noncentral
kernel then contains a conjugate component, so the original component and
its two-component orbit have elementary Sylow two-subgroups.

The literal natural S₆ constituent quotient maps this perfect orbit onto
A₆. Its elementary Sylow subgroups would therefore give elementary Sylow
subgroups in A₆, contradicting the concrete noncommuting involutions there.
Together with the preceding actor-rank sieve this excludes every natural
exchanged row for the original larger actor. The resulting numerical and
component alternatives retain only the marked full S₈ action and the
whole-component G.9 recognition branch. Neither remaining branch is asserted
excluded. The full dotted G₂(2) equivalence is preserved in degree six.

Source: Aschbacher--Smith G.10.15, printed p.362; G.11.6--7 and
14.3.13--14, printed pp.366--367,993--994. See also the full-linear-four
correction in `docs/quasithin-proof-basis.md`.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative

private theorem natural_six_quotient
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (H Y : Subgroup D) [H.Normal]
    [Group.IsPerfect H] (I : Submodule (ZMod 2) V) (hne : I ≠ ⊥)
    (hfix : fixedSpace ρ H = ⊥)
    (hH : H ≤ subspaceStabilizer ρ I) (hY : Y ≤ subspaceStabilizer ρ I)
    (hm : CFSG.Quasithin.ChapterG.Section06.HasModelOn
      (kerRepresentation (CFSG.Quasithin.ChapterG.Section09.constituentAction ρ H Y I hH hY))
      ⊤ ⊤ (BinaryPermutation.naturalRepresentation (Fin 6))) :
    ∃ f : H →* alternatingGroup (Fin 6), Function.Surjective f := by
  let P := H ⊔ Y
  let σ := CFSG.Quasithin.ChapterG.Section09.constituentAction ρ H Y I hH hY
  let q := QuotientGroup.mk' σ.ker
  let r := q.comp (inclusion (show H ≤ P from le_sup_left))
  have hrange : r.range = (H.subgroupOf P).map q := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨a,rfl⟩; exact a.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  let : r.range.Normal := hrange ▸ Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective _)
  obtain ⟨e,_,_⟩ := hm
  let d := Subgroup.topEquiv.symm.trans e
  let j := d.toMonoidHom.comp r
  have hjrange : j.range = r.range.map d.toMonoidHom := MonoidHom.range_comp _ _
  let : j.range.Normal := hjrange ▸ Subgroup.Normal.map inferInstance d.toMonoidHom d.surjective
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  have hjne : j.range ≠ ⊥ := by
    intro hz
    apply hne
    apply bot_unique
    rw [←hfix]
    intro u hu a
    have hj : j a = 1 := mem_bot.mp (hz ▸ (show j a ∈ j.range from ⟨a,rfl⟩))
    have hq : r a = 1 := d.injective (by
      change d (r a) = 1 at hj
      simpa only [map_one] using hj)
    have hσ : σ (inclusion (show H ≤ P from le_sup_left) a) = 1 :=
      (QuotientGroup.eq_one_iff _).mp hq
    exact congrArg (fun f : Module.End (ZMod 2) I => (f ⟨u,hu⟩ : V)) hσ
  let : Nontrivial j.range := j.range.nontrivial_iff_ne_bot.mpr hjne
  have hA : j.range = alternatingGroup (Fin 6) :=
    Equiv.Perm.eq_alternatingGroup_of_perfect_normal (by simp) j.range
  let eA := MulEquiv.subgroupCongr hA
  exact ⟨eA.toMonoidHom.comp j.rangeRestrict, eA.surjective.comp j.rangeRestrict_surjective⟩

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterG.Section11
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- The remaining natural S₆ constituent is impossible: its actual
alternating quotient contradicts the elementary Sylow condition forced by
its noncentral kernel. -/
theorem not_exchanged_natural_six
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I)
    (hv : v ∉ I)
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
        (componentOrbit L ⊤) (F.terminalDot (F.X g) ⊓ subspaceStabilizer F.terminalRepresentation I)
        I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin 6))) : False := by
  let ρ := F.terminalRepresentation
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  let X := F.terminalDot (F.X g)
  let R := invariantSubspace ρ H I hI.invariant
  obtain ⟨S,_,hXS,hnS⟩ := s.normal_sylow
  have hnX := (normal_subgroupOf_iff_le_normalizer hXS).mp hnS
  have hind := (Classical.choice s.classification_input.1).component_normalizer_index_le_two hL
  have hi : (normalizer (L : Set F.TerminalHdot)).index = 2 := by
    have hne : (normalizer (L : Set F.TerminalHdot)).index ≠ 1 := by
      intro h1
      have hnL : L.Normal := normalizer_eq_top_iff.mp (index_eq_one.mp h1)
      apply s.exchanged_natural_six_orbit_ne_component hL hm hI hgeo hmodel
      exact le_antisymm (iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl
        (by rw [normalizer_eq_top])) (le_componentOrbit L ⊤)
    have hp := (normalizer (L : Set F.TerminalHdot)).index_ne_zero_of_finite
    omega
  obtain ⟨x,_,hsep⟩ := s.hypothesis.exchanged_pair_separates s.nonsolvable hL hm S hnX hind hI hv
  let : IsElementaryAbelian 2 (((S : Subgroup F.TerminalHdot).subgroupOf H) ⊓
      R.toRepresentation.asGroupHom.ker : Subgroup H) :=
    ExchangedKernel.kernel_sylow_elementary ρ H X S hnX R x hsep
  have hE (P : Sylow 2 L) : IsElementaryAbelian 2 P :=
    ExchangedKernel.component_sylow_elementary_of_kernel hL S R.toRepresentation.asGroupHom.ker
      (s.exchanged_natural_six_noncentral_kernel hL hm hI hgeo hmodel) P
  have hEH := ExchangedOrbit.orbit_sylow_elementary hL hi hE
  obtain ⟨f,hf⟩ := natural_six_quotient ρ H (X ⊓ subspaceStabilizer ρ I) I
    (hI.isIrrPlus.ne_bot ρ)
    (fixedSpace_eq_bot_of_normal_faithful_irreducible ρ s.hypothesis.faithful
      (s.hypothesis.irreducible_of_not_solvable s.nonsolvable) H hL.componentOrbit_top_ne_bot)
    hI.invariant inf_le_right hmodel
  let P : Sylow 2 (alternatingGroup (Fin 6)) := Classical.choice inferInstance
  let : IsElementaryAbelian 2 P := ExchangedOrbit.elementary_sylow_image f hf hEH P
  exact alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute P
    (fun a b _ _ => show Commute a b from mul_comm a b) (MonoidHom.id _) Function.injective_id


/-- No natural symmetric exchanged constituent survives the original
larger-actor hypotheses. -/
theorem not_exchanged_natural
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I)
    (hv : v ∉ I)
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I)
    (n : ℕ) (hn : 5 ≤ n) (hnu : n ≤ 8)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
        (componentOrbit L ⊤) (F.terminalDot (F.X g) ⊓ subspaceStabilizer F.terminalRepresentation I)
        I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n))) : False := by
  obtain ⟨rfl,_⟩ := s.exchanged_natural_six hL hm hI hgeo n hn hnu hmodel
  exact s.not_exchanged_natural_six hL hm hI hv hgeo hmodel

/-- The only remaining exchanged action is the marked full S₈ model.
The other remainder is the genuine whole-component G.9 hypothesis. -/
theorem degree_cases_or_full_four_or_whole :
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
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
          ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L ∧
          ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
            F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
            (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) := by
  rcases s.degree_cases_or_full_four_or_noncentral_six with hd | hf | ⟨hd,L,hL,hm,ho,hw | hex⟩
  · exact Or.inl hd
  · exact Or.inr (Or.inl hf)
  · exact Or.inr (Or.inr ⟨hd,L,hL,hm,ho,hw⟩)
  · obtain ⟨I,hI,hv,hgeo,_,_,_,_,_,_,_,hmodel⟩ := hex
    exact (s.not_exchanged_natural_six hL hm hI hv hgeo hmodel).elim

/-- Apply the completed natural exclusions to the actual component consumer,
retaining the full dotted G₂(2) equivalence in its numerical input. -/
theorem component_or_full_four_or_whole
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
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ∃ L : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot L ∧
          ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B L ∧
          ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
            F.terminalRepresentation (F.terminalDot (F.X g)) L (componentOrbit L ⊤)
            (finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))) := by
  rcases s.degree_cases_or_full_four_or_whole with hd | hr
  · exact Or.inl (source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis hd hfour hsix)
  · exact Or.inr hr

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
