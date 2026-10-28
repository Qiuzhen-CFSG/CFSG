module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeCoverExclusion
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreeNonFF

/-!
# Non-FF action on the original terminal seed orbit

The original parabolic swap moves each marked linear-three seed. The
quadratic bound on its full normalizer orbit gives natural and dual
coordinates with the same component marking. The full linear normalizer
of that six-dimensional pair has no FF offender. Thus the faithful image
of K N_T(K) on this original orbit is non-FF.

The terminal exchanged-component application supplies every representation
premise from the original rank-two hypotheses. This is a non-FF statement
on the seed orbit; the ambient quotient alternatives and equality with the
full commutator support still require proof. Original14.6.18 remains hsolv,
with final discharge owned by qt-e-14625-source.
Source: Aschbacher--Smith B.5.1, F.9.18(7),14.6.22, printed pp.99,326,1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv


/-- The literal K N_T(K) action on a moved seed orbit is non-FF.
The orbit is taken inside the original U/Z, retaining its original action. -/
theorem source_l3_seed_orbit_not_ff
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation (actorImage H K)
      (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage H K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3))
    (hsmall : quadraticRatio (invariantSubspace a.representation (actorImage H K)
      (orbitSpan a.representation
        (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
      (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2) :
    let R := actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))
    let O := orbitSpan a.representation R I
    let hO := sup_le
      (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)
      (orbitSpan_invariant a.representation R I)
    ¬ IsFFModule (imageRepresentation
      (invariantSubspace a.representation (actorImage H K ⊔ R) O hO).toRepresentation) := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  let c := originalSection a
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  let R := actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))
  let q := QuotientGroup.mk' (pCore 2 H)
  have hR : actorImage H S = R := source_component_normalizer_image T H hH K hKH hK
  obtain ⟨⟨s,hs⟩,_⟩ := source_l3_seed_stabilizer_index
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK a hI b
  have hmove : orbitSpan a.representation R I ≠ I := by
    intro hh
    have hinv : R ≤ subspaceStabilizer a.representation I :=
      hh ▸ orbitSpan_invariant a.representation R I
    let v : H := ⟨s,hH.1.2 s.property.1⟩
    have hqv : q v ∈ R := hR ▸ (show q v ∈ actorImage H S from ⟨v,s.property,rfl⟩)
    apply hs
    exact (c.mem_normalizer_subspacePreimage_iff I v).mpr
      ((subspace_map_eq_iff a.representation I (q v)).mpr (hinv hqv))
  exact hI.orbit_image_not_ff_of_small a.representation b.groupEquiv
    b.linearEquiv b.intertwines hmove hsmall

/-- The original exchanged-component hypotheses produce a non-FF orbit,
with a faithful component action and its natural central-quotient marking. -/
theorem terminal_nonnormal_seed_orbit_not_ff
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))))
        (hI : IsIrrPlusWith a.representation (actorImage Mc K)
          (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
        (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
        (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)) ∧
      let R := actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))
      let O := orbitSpan a.representation R I
      let hKO := orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus
      let σ := (invariantSubspace a.representation (actorImage Mc K) O hKO).toRepresentation
      Function.Injective σ ∧ quadraticRatio σ ≤ 2 ∧
      ¬ IsFFModule (imageRepresentation
        (invariantSubspace a.representation (actorImage Mc K ⊔ R) O
          (sup_le hKO (orbitSpan_invariant a.representation R I))).toRepresentation) := by
  obtain ⟨hU,a,I,hI,⟨b⟩,hfaith,hsmall,_⟩ := terminal_nonnormal_full_component_action
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  exact ⟨hU,a,I,hI,⟨b⟩,hfaith,hsmall,source_l3_seed_orbit_not_ff
    hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK a hI b hsmall⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
