module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeSections
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LiftedSeeds
public import CFSG.Quasithin.ChapterD.Section02.LinearThreeCentralTypes
public import Theory.Representation.BinaryOffender.LinearThreeCentralCover
public import Theory.Representation.BinaryConjugationSection.SubspaceSection

/-!
# Natural central covers on the original terminal component seeds

Section recognition now applies to every Irr⁺ member of the full original
U_H/Z, using occurrence and Clifford restriction. Its literal quotient by
component-fixed vectors is the natural binary three-space. Dual cohomology
bounds the retained fixed kernel by one dimension, so the original seed is
three- or four-dimensional; no splitting is inferred.

The terminal application constructs a homogeneous seed, its actual subgroup
preimage W inside [U,K], and coordinates on W/Z using the unchanged original
action. It also proves the exact support normalizer and central-overlap
separation under N_T(K). This does not yet identify the seed orbit with the
entire component support or exclude the four-dimensional central cover.
Those steps, the FF exclusion and suitable-vector assembly remain with
qt-e-suitable-component-supports. Original 14.6.18 remains explicit, with
final discharge by qt-e-14625-source.

Source: Aschbacher--Smith F.9.18(3,5,7), pp.325--326, I.1.5--6, p.408,
and the natural-cover and support arguments in 14.6.22--24, pp.1038--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
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

/-- Every original noncentral Irr⁺ seed has a natural central quotient and
a retained fixed kernel of dimension at most one. -/
theorem source_nonnormal_irrPlus_cover
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (A : Subgroup (H ⧸ pCore 2 H))
    (hAT : A ≤ actorImage H T) (hA : QuadraticMember a.representation A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlus a.representation (actorImage H K) I) :
    Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage H K) I hI.choose)
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)) ∧
      Module.finrank (ZMod 2) ((fixedSpace a.representation (actorImage H K)).comap I.subtype) ≤ 1 ∧
      Module.finrank (ZMod 2) I =
        3 + Module.finrank (ZMod 2) ((fixedSpace a.representation (actorImage H K)).comap I.subtype) ∧
      (Module.finrank (ZMod 2) I = 3 ∨ Module.finrank (ZMod 2) I = 4) := by
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  let : IsQuasisimple (actorImage H K) := hD.2
  obtain ⟨b⟩ := ChapterD.central_constituent_linear_three_of_sections
    a.representation (actorImage H K) hD.1
    (fun U N hi => source_nonnormal_subquotient_all_natural
      hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn
      a A hAT hA hfaith U N hi) hI
  exact ⟨⟨b⟩, hI.finrank_of_linear_three_central_quotient a.representation (actorImage H K)
    b.groupEquiv b.linearEquiv b.intertwines⟩

/-- Component seeds lift to actual supports inside [U,K]. Distinct
conjugates under the component normalizer overlap only in K-fixed elements. -/
theorem source_component_seed_geometry
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlus a.representation (actorImage H K) I) :
    let c := originalSection a
    let W := c.subspacePreimage I
    centralInvolutions T ≤ W ∧ W ≤ ⁅conjugateSpanBy (localModule T M) H,K⁆ ∧
      K ≤ normalizer (W : Set G) ∧
      (∀ h : H, (h:G) ∈ normalizer (W : Set G) ↔
        I.map (a.representation (QuotientGroup.mk' (pCore 2 H) h)) = I) ∧
      ∀ t ∈ (T : Subgroup G), t ∈ normalizer (K : Set G) → t ∉ normalizer (W : Set G) →
        W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (K : Set G) ∧
        K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G) := by
  let c := originalSection a
  have hi := originalSection_irrPlus a K hI
  have hz := (source_component_support_placement hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK).1
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  have h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  have hZK : centralInvolutions T ≤ centralizer (K : Set G) :=
    (le_centralizer_iff.mp h.H_centralizes).trans (centralizer_le hKH)
  refine ⟨c.kernel_le_subspacePreimage I,c.irrPlus_preimage_le_commutator K hKH hz hi,
    c.subspacePreimage_normalized K hKH I hi.choose,
    fun h => c.mem_normalizer_subspacePreimage_iff I h,?_⟩
  intro t ht htk htw
  exact c.irrPlus_preimage_separated K hKH hZK hi
    ⟨t⁻¹,hH.1.2 ((T : Subgroup G).inv_mem ht)⟩
    ((normalizer (K : Set G)).inv_mem htk)
    (fun hh => htw ((normalizer (c.subspacePreimage I : Set G)).inv_mem_iff.mp hh))

/-- The lifted support has coordinates on the literal quotient W/Z,
with exactly the original component action and original coordinate map. -/
theorem source_component_seed_coordinates
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlus a.representation (actorImage H K) I) :
    let c := originalSection a
    let hi := originalSection_irrPlus a K hI
    ∃ d : BinaryConjugationSection K (c.subspacePreimage I) (centralInvolutions T)
        (BinaryConjugationSection.subspaceAction K hKH I hi.choose),
      ∀ w : c.subspacePreimage I, (d.coordinates w).toAdd.val =
        (c.coordinates ⟨w,c.subspacePreimage_le I w.property⟩).toAdd := by
  let c := originalSection a
  let hi := originalSection_irrPlus a K hI
  have hWK : c.subspacePreimage I ≤ K :=
    (source_component_seed_geometry hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK a hI).2.1.trans
        ((source_component_support_placement hG T hempty hM hunique hmany hcard e hab hsolv
          H hH K hKH hK).2.1.trans (inf_le_right.trans (pCoreIn_le 2 K)))
  exact ⟨c.subspaceSection K hKH I hi.choose hWK,
    c.subspaceSection_coordinates K hKH I hi.choose hWK⟩

/-- At H=Mc, the source supplies every actor and seed premise, producing
a marked natural central cover and its literal original support geometry. -/
theorem terminal_nonnormal_central_natural_support
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
      Module.finrank (ZMod 2) ((fixedSpace a.representation (actorImage Mc K)).comap I.subtype) ≤ 1 ∧
      Module.finrank (ZMod 2) I =
        3 + Module.finrank (ZMod 2) ((fixedSpace a.representation (actorImage Mc K)).comap I.subtype) ∧
      (Module.finrank (ZMod 2) I = 3 ∨ Module.finrank (ZMod 2) I = 4) ∧
      let c := originalSection a
      let W := c.subspacePreimage I
      (∃ d : BinaryConjugationSection K W (centralInvolutions T)
          (BinaryConjugationSection.subspaceAction K hKM I
            (originalSection_irrPlus a K hI.isIrrPlus).choose),
        ∀ w : W, (d.coordinates w).toAdd.val =
          (c.coordinates ⟨w,c.subspacePreimage_le I w.property⟩).toAdd) ∧
      centralInvolutions T ≤ W ∧ W ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆ ∧
        K ≤ normalizer (W : Set G) ∧
        (∀ h : Mc, (h:G) ∈ normalizer (W : Set G) ↔
          I.map (a.representation (QuotientGroup.mk' (pCore 2 Mc) h)) = I) ∧
        ∀ t ∈ (T : Subgroup G), t ∈ normalizer (K : Set G) → t ∉ normalizer (W : Set G) →
          W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (K : Set G) ∧
          K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hU,a,B,_,hB,_,_,hA,hfaith,_⟩ := terminal_nonnormal_component_span_inputs
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  have hD := source_quotient_component
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK
  let : IsQuasisimple (actorImage Mc K) := hD.2
  let S : Subgroup (Mc ⧸ pCore 2 Mc) := actorImage Mc T ⊓ normalizer
    (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))
  have hp : IsPGroup 2 S := (quotientSylow Mc T hout.1.2).isPGroup'.of_injective
    (inclusion (show S ≤ (quotientSylow Mc T hout.1.2 : Subgroup (Mc ⧸ pCore 2 Mc)) from inf_le_left))
    (inclusion_injective _)
  obtain ⟨I,hI⟩ := exists_isIrrPlusWith_of_faithful a.representation a.faithful
    (actorImage Mc K) (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc)))
    hD.isCComponent.ne_bot inf_le_right hp
  obtain ⟨hmark,hker,hdim,halt⟩ := source_nonnormal_irrPlus_cover
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK hn a
    (B.map (QuotientGroup.mk' (pCore 2 Mc)))
    (source_internal_actor_le_sylow T hout.1.2 B hB) hA hfaith hI.isIrrPlus
  exact ⟨hU,a,I,hI,hmark,hker,hdim,halt,source_component_seed_coordinates
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hI.isIrrPlus,
    source_component_seed_geometry
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hI.isIrrPlus⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
