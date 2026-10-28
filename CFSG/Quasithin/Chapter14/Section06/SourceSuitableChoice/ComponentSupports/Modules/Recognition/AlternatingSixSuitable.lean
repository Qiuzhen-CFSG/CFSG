module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.SingleAlternatingSix
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.AlternatingSixCoverAction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.AlternatingSixGeometry

/-!
# One suitable original involution in the A₆ branch

The original hypotheses select a homogeneous seed whose natural quotient
has a genuine four- or five-dimensional central cover. Its exact support
normalizer has index two in T and local normalizer T. The I.2.3 lift gives
one original involution, and the separated-support argument proves all
U₀--U₃ for that same involution, with its exact quotient centralizer.

The residual identity remains an earlier source input; its conditional
catalogue is terminal_component_catalogue_of_mixed_size. Final mixed-size
instantiation belongs to qt-e-suitable-existence; original14.6.18 remains
hsolv, owned by qt-e-14625-source. Full paired-support exhaustion is a
separate14.6.22 obligation; this module proves the suitable-vector branch.

Source: Aschbacher--Smith14.6.22--24, printed pp.1038--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Subgroup.NormalSylowQuotientAction
open Chapter13.Section08.CriticalGeometry.Reorientation
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

/-- One original vector satisfies every suitability clause in the A₆
branch, including when the full central cover has dimension five. -/
theorem source_exists_on_normal_a6_seed
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hnK : (K.subgroupOf Mc).Normal) (hgen : K ⊔ (T : Subgroup G) = Mc)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))}
    (hI : IsIrrPlusWith a.representation (actorImage Mc K)
      (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.alternatingNatural 6)) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let W := (originalSection a).subspacePreimage I
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = (T : Subgroup G) ⊓ normalizer (W : Set G) ∧
      Suitable h Mc u := by
  let W := (originalSection a).subspacePreimage I
  let S := (T : Subgroup G) ⊓ normalizer (W : Set G)
  have d := source_normal_a6_seed_geometry hG T hempty hM hunique hmany hcard e hab hsolv
    K hKM hK hnK hgen a hI b
  obtain ⟨_,_,_,_,_,_,_,u,hu,hu2,hune,huf,hum⟩ := source_normal_a6_seed_fixed_moving
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hnK a hI b
  let : Group.IsPerfect (K.subgroupOf Mc) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKM).toMonoidHom) (subgroupOfEquivOfLe hKM).surjective
  obtain ⟨heq,hm,hp,hl⟩ := source_suitable_of_central_overlap
    hG T hempty hM hunique hmany hcard e hab Mc
      (terminal_outside hG T hempty hM hunique hmany hcard e)
      K W S d.fitting d.support_le d.point_le d.normalized
      d.sylow_le d.index d.local_normalizer d.separated u hu huf hum
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  refine ⟨u,hu,hu2,hune,heq,d.support_le hu,hl,?_,hm,hp,?_⟩
  · change (suitableQuotientCentralizer h u).relIndex (T : Subgroup G) = 2
    rw [show suitableQuotientCentralizer h u = S from heq]
    exact d.index
  · change Mc ⊓ normalizer (suitableQuotientCentralizer h u : Set G) = _
    rw [show suitableQuotientCentralizer h u = S from heq]
    exact d.local_normalizer

/-- The original single A₆ branch constructs its cover, literal support
geometry and one suitable involution, with no vector or geometry callback. -/
theorem terminal_single_a6_cover_suitable
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hr : (solvableResidual Mc).map Mc.subtype = K)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))))
        (hI : IsIrrPlusWith a.representation (actorImage Mc K)
          (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I),
        Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
          (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
          (ChapterB.QuasisimpleSource.alternatingNatural 6)) ∧
        (Module.finrank (ZMod 2) I = 4 ∨ Module.finrank (ZMod 2) I = 5) ∧
        let W := (originalSection a).subspacePreimage I
        let S := (T : Subgroup G) ⊓ normalizer (W : Set G)
        CentralOverlapGeometry T Mc (conjugateSpanBy (localModule T M) Mc) K W S ∧
        ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧
          suitableQuotientCentralizer (terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) u = S ∧
          Suitable (terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u := by
  obtain ⟨hU,a,I,hI,⟨b⟩,_,_,hdim⟩ := terminal_single_a6_natural_seed
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hr eK
  let := hU
  obtain ⟨hn,hgen⟩ := terminal_single_component_generated
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hr (Or.inr ⟨eK⟩)
  exact ⟨hU,a,I,hI,⟨b⟩,hdim,
    source_normal_a6_seed_geometry hG T hempty hM hunique hmany hcard e hab hsolv
      K hKM hK hn hgen a hI b,
    source_exists_on_normal_a6_seed hG T hempty hM hunique hmany hcard e hab hsolv
      K hKM hK hn hgen a hI b⟩


end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
