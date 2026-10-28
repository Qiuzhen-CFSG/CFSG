module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.FullOrbitNonFF
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreeNaturalNonFF
public import Theory.Representation.IrreducibleSectionPullback

/-!
# Excluding FF on component-detecting quotients of the original module

On an irreducible original subquotient, Clifford theory makes the component
restriction semisimple. The source quadratic actor recognizes every noncentral
component type as natural. The actual diagram automorphism moves a homogeneous
seed, so its natural-dual orbit is non-FF. Best-offender normalization and
residual self-centralization exclude FF on that entire irreducible action.

For an arbitrary quotient detecting the component, select a surviving
irreducible section and pull it through the original quotient map. Apply the
proved original-section recognition there, then transfer the exclusion back
using fixed-codimension inequalities. This constructs the quotient exclusion
needed by ResidualSupport without assuming faithfulness of that quotient or
discarding its kernel. Original14.6.18 remains hsolv, for qt-e-14625-source.

Source: Aschbacher--Smith B.1.5(4), B.5.1, F.9.18(6--7),14.6.22,
printed pp.71,99,326,1038.
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
universe u
variable {G : Type u} [Group G] [Finite G]
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


/-- Every faithful action whose component restriction is semisimple with
natural types is non-FF, under the original diagram-action hypotheses. -/
theorem source_l3_natural_types_not_ff
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) = H)
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) X)
    (hf : Function.Injective σ)
    [IsSemisimpleRepresentation (σ.comp (actorImage H K).subtype)]
    (hnatural : ChapterD.NaturalLinearThreeTypes σ (actorImage H K)) :
    ¬ IsFFModule σ := by
  let : Module.Finite (ZMod 2) X := Module.Finite.of_finite
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK
  let : IsQuasisimple (actorImage H K) := hD.2
  let P := actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))
  have hP : IsPGroup 2 P := (quotientSylow H T hH.1.2).isPGroup'.of_injective
    (inclusion (show P ≤ (quotientSylow H T hH.1.2 : Subgroup (H ⧸ pCore 2 H)) from inf_le_left))
    (inclusion_injective _)
  obtain ⟨I,hI⟩ := exists_isIrrPlusWith_of_faithful σ hf
    (actorImage H K) P hD.isCComponent.ne_bot inf_le_right hP
  obtain ⟨F,hF,⟨b₀⟩⟩ := hnatural I hI.isIrrPlus
  let c := ChapterB.QuasisimpleSource.ExtensionConsequences.degreeOneNaturalEquiv F hF 3
  let j : actorImage H K ≃* BinaryLinearThree.Group := b₀.groupEquiv.trans c.groupEquiv
  let l : I ≃ₗ[ZMod 2] BinaryLinearThree.Vector := b₀.linearEquiv.trans c.linearEquiv
  have he (k : actorImage H K) (v : I) :
      l ((invariantSubspace σ (actorImage H K) I hI.invariant).toRepresentation k v) =
        BinaryLinearThree.W (j k) (l v) :=
    (congrArg c.linearEquiv (b₀.intertwines k v)).trans (c.intertwines (b₀.groupEquiv k) _)
  have hz : center (actorImage H K) = ⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr j ⟨k,hk⟩).property
    change j k ∈ center BinaryLinearThree.Group at hh
    rw [show center BinaryLinearThree.Group = ⊥ from Matrix.PSL3Two.center_eq_bot,mem_bot] at hh
    exact j.injective (hh.trans j.map_one.symm)
  have hout : ∃ t : P, ¬ ∃ k : actorImage H K,
      (actorImage H K).normalizerMonoidHom ⟨t,hI.normalizes t.property⟩ = MulAut.conj k := by
    obtain ⟨s,hs⟩ := source_l3_component_outer_image
      hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK j
    let q := QuotientGroup.mk' (pCore 2 H)
    let sh : H := ⟨s,hH.1.2 s.property.1⟩
    have ht : q sh ∈ P := by
      dsimp only [P]
      rw [←source_component_normalizer_image T H hH K hKH hK]
      exact ⟨sh,s.property,rfl⟩
    refine ⟨⟨q sh,ht⟩,?_⟩
    rintro ⟨k,hk⟩
    apply hs
    refine ⟨k,fun x => ?_⟩
    exact congrArg Subtype.val (MulEquiv.congr_fun hk x)
  have hn := hI.orbit_image_not_ff_of_natural σ j l he
    (hI.isIrrPlus.inf_fixedSpace_eq_bot_of_semisimple σ) hout
  have hres : pResidual 2 (H ⧸ pCore 2 H) ≤
      componentOrbit (actorImage H K) (quotientSylow H T hH.1.2) := by
    rw [quotient_componentOrbit H K T hKH hH.1.2,
      ←source_component_orbit_eq_residual hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK hgen, GenerationOne.residual, actorImage_internal,
      map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
  apply not_ff_of_sylow_best_centralizes_orbit σ
    (quotientSylow H T hH.1.2) (actorImage H K) (pCore_quotient_pCore_eq_bot 2) hres
  intro A hAT hA
  exact hA.centralizes_of_nonFF_orbit σ hz hP hI
    (le_inf hAT (ChapterB.source_lemma_B_1_5_4 σ hf hA hD)) hn

/-- Every component-detecting irreducible subquotient of the original
terminal module is faithful and non-FF. Natural types are supplied by the
original F.9.18 actor and are not extra classification premises. -/
theorem source_nonnormal_irreducible_subquotient_not_ff
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) = H)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (A : Subgroup (H ⧸ pCore 2 H))
    (hAT : A ≤ actorImage H T) (hA : QuadraticMember a.representation A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    (U : Subrepresentation a.representation) (N : Subrepresentation U.toRepresentation)
    (hi : IsIrreducible N.quotientRepresentation)
    (hdetect : ¬ actorImage H K ≤ N.quotientRepresentation.ker) :
    Function.Injective N.quotientRepresentation ∧ ¬ IsFFModule N.quotientRepresentation := by
  let σ := N.quotientRepresentation
  let : Finite (U ⧸ N.toSubmodule) := Module.finite_of_finite (ZMod 2)
  let : IsIrreducible σ := hi
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK
  let : IsSemisimpleRepresentation (σ.comp (actorImage H K).subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
      (subnormal_restriction_semisimple σ (actorImage H K) hD.1)
  have hf := source_faithful_of_component_detected
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hgen σ hdetect
  exact ⟨hf,source_l3_natural_types_not_ff
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hgen σ hf
    (source_nonnormal_subquotient_all_natural
      hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn a A hAT hA hfaith U N hi)⟩

/-- A quotient on which the original component survives cannot be FF.
The detected section is pulled back through the literal quotient map before
applying the original natural-section recognition. -/
theorem source_nonnormal_quotient_not_ff
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) = H)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (A : Subgroup (H ⧸ pCore 2 H))
    (hAT : A ≤ actorImage H T) (hA : QuadraticMember a.representation A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    (W : Subrepresentation a.representation)
    (hdetect : ¬ actorImage H K ≤ W.quotientRepresentation.ker) :
    ¬ IsFFModule W.quotientRepresentation := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK
  let : IsQuasisimple (actorImage H K) := hD.2
  obtain ⟨U,N,hi,hd⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (actorImage H K) hdetect
  let τ := N.quotientRepresentation
  let q : a.representation.IntertwiningMap W.quotientRepresentation := {
    toLinearMap := W.toSubmodule.mkQ
    isIntertwining' := fun _ => rfl }
  have hs : QuadraticFourGroup.IsIrreducibleSection W.quotientRepresentation τ :=
    ⟨hi,U,N,⟨Representation.Equiv.refl _⟩⟩
  obtain ⟨_,U',N',⟨b⟩⟩ := hs.of_surjective_intertwining q W.toSubmodule.mkQ_surjective
  have hi' : IsIrreducible N'.quotientRepresentation :=
    (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv b)).mpr hi
  have hd' : ¬ actorImage H K ≤ N'.quotientRepresentation.ker :=
    fun hk => hd (hk.trans (QuadraticFourGroup.ker_le_of_equiv b))
  have hno := (source_nonnormal_irreducible_subquotient_not_ff
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hgen
    a A hAT hA hfaith U' N' hi' hd').2
  have hnτ : ¬ IsFFModule τ := by
    intro hh
    apply hno
    exact hh.map_equivariant τ N'.quotientRepresentation (MonoidHom.id _)
      Function.injective_id b.symm.toLinearEquiv (fun g v =>
        LinearMap.congr_fun (b.symm.isIntertwining' g) v)
  rintro ⟨B,hB,hbound⟩
  apply hnτ
  refine ⟨B,hB,?_⟩
  have hq := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N B
  have hu := fixedCodim_subrepresentation_le W.quotientRepresentation U B
  change fixedCodim N.quotientRepresentation B ≤ rank B
  omega

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
