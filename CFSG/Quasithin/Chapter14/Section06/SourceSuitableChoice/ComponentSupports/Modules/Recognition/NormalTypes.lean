module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.NormalPairSections
public import CFSG.Quasithin.ChapterD.Section02.LinearThreeSeedTypes
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Natural types and exclusion of the distinct normal component pair

For a relatively normal binary linear-three component, NormalSeeds constructs
a literal natural seed whose Mc-conjugates exhaust [U,K]. Embed its quotient
into the original U/Z using the unchanged coordinate kernel. The intrinsic
component quotient is identified with its actual image in Mc/O₂(Mc), so the
normal-seed theorem applies to every original irreducible subquotient.

Applying this separately to the two distinct normal components discharges both
natural-type hypotheses in NormalPairSections. That consumer constructs all
four natural/dual sections, their full supports, intersections, cross-actions
and separation and applies the literal paired-component contradiction. Neither
component is replaced by an exchanged conjugate.

Thus the distinct normal pair in14.6.21(3) is impossible. With the previously
proved exchanged exclusion, the actual component catalogue suffices for
H∞ = K. Catalogue completion still requires the normal PSL₂(4) exclusion;
the A₆ marking and same-vector suitable construction remain with
qt-e-suitable-component-supports. Original14.6.18 is the explicit hsolv input,
owned by qt-e-14625-source, and final14.6.24 assembly remains with
qt-e-suitable-existence.
Source: Aschbacher--Smith14.6.21--24, printed pp.1037--1041.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
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



/-- All noncentral types on every original irreducible section are natural
for a relatively normal binary linear-three component. -/
theorem terminal_normal_l3_subquotient_all_natural
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : (K.subgroupOf Mc).Normal)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    (R : Subrepresentation a.representation) (N : Subrepresentation R.toRepresentation)
    (hi : IsIrreducible N.quotientRepresentation) :
    ChapterD.NaturalLinearThreeTypes N.quotientRepresentation (actorImage Mc K) := by
  obtain ⟨j,A,B,⟨d⟩,_,hA,_,_,_,_,_,_,hexhaust⟩ := terminal_normal_l3_natural_sections_span
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn eK
  let U := conjugateSpanBy (localModule T M) Mc
  let D := actorImage Mc K
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let c := originalSection a
  have hAU : A ≤ U := hA.trans
    (le_normalizer_iff_commutator_le_left.mp (hKM.trans a.normalizes))
  obtain ⟨f,hfi,hcoord,hcov,hrange⟩ := c.exists_coordinate_embedding d hKM hAU
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  let ec : (K ⧸ pCore 2 K) ≃* D :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKM)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKM))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  let r : K →* D := (q.subgroupMap (K.subgroupOf Mc)).comp
    (subgroupOfEquivOfLe hKM).symm.toMonoidHom
  have hr (k : K) : ec ((QuotientGroup.mk' (pCore 2 K)) k) = r k := rfl
  have hrs : Function.Surjective r :=
    (q.subgroupMap_surjective (K.subgroupOf Mc)).comp (subgroupOfEquivOfLe hKM).symm.surjective
  let b := ec.symm.trans j
  have hb (k : K) : b (r k) = j ((QuotientGroup.mk' (pCore 2 K)) k) := by
    rw [←hr]
    exact congrArg j (ec.symm_apply_apply _)
  let l : Representation.IntertwiningMap (BinaryLinearThree.W.comp b.toMonoidHom)
      (a.representation.comp D.subtype) := {
    toLinearMap := f
    isIntertwining' k := by
      apply LinearMap.ext
      intro v
      obtain ⟨k,rfl⟩ := hrs k
      change f (BinaryLinearThree.W (b (r k)) v) = a.representation (r k).val (f v)
      rw [hb]
      exact (hcov k v).symm }
  let S := l.range
  let z : Representation.Equiv (BinaryLinearThree.W.comp b.toMonoidHom) S.toRepresentation :=
    .mk (LinearEquiv.ofInjective f hfi) (by
      intro k
      apply LinearMap.ext
      intro v
      exact Subtype.ext (l.isIntertwining _ _ k v))
  let : D.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
    Mc (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK
  let : IsQuasisimple D := hD.2
  have hgen : Coinvariants.ker (a.representation.comp D.subtype) ≤
      ⨆ g : Mc ⧸ pCore 2 Mc, S.toSubmodule.map (a.representation g) := by
    have hmoved : Coinvariants.ker (a.representation.comp D.subtype) = c.imageSpace ⁅U,K⁆ := by
      rw [commutator_comm U K,c.imageSpace_commutator K U hKM le_rfl,c.imageSpace_self,
        subspaceCommutator_comp_map,subspaceCommutator_top_eq_coinvariants]
      rfl
    rw [hmoved,hexhaust,c.imageSpace_conjugateSpan A hAU]
    apply iSup_le
    intro g
    rw [←hrange]
    exact le_iSup (fun x : Mc ⧸ pCore 2 Mc => S.toSubmodule.map (a.representation x)) (q g)
  exact ChapterD.subquotient_natural_types_of_normal_seed_orbit
    a.representation D S b z.symm hgen R N hi

/-- The distinct normal-pair branch is excluded on the original module.
Both natural-type families and all four full marked sections are constructed. -/
theorem terminal_normal_pair_impossible
    (K C : Subgroup G) (hKM : K ≤ Mc) (hCM : C ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent) (hC : (C.subgroupOf Mc).IsCComponent)
    (hne : K ≠ C) (hnK : (K.subgroupOf Mc).Normal) (hnC : (C.subgroupOf Mc).Normal)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (eC : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group)
    (hr : ((solvableResidual Mc).map Mc.subtype : Set G) = (K : Set G) * (C : Set G)) : False := by
  obtain ⟨hU,a,_⟩ := source_rankTwo_bounded_placed_action
    hG T hempty hM hunique hmany hcard e hab Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e)
  let := hU
  exact terminal_normal_pair_impossible_of_natural_types
    hG T hempty hM hunique hmany hcard e hab hsolv K C hKM hCM hK hC hne hnK hnC eK eC hr a
    (fun S L hi => ⟨terminal_normal_l3_subquotient_all_natural
        hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hnK eK a S L hi,
      terminal_normal_l3_subquotient_all_natural
        hG T hempty hM hunique hmany hcard e hab hsolv C hCM hC hnC eC a S L hi⟩)

/-- Both pair alternatives have been excluded. Once the actual quotient
catalogue is supplied, every original component is the whole solvable residual. -/
theorem terminal_residual_eq_component_of_models
    (hm : ∀ K : Subgroup G, K ≤ Mc → (K.subgroupOf Mc).IsCComponent → ComponentQuotientModels K)
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    (solvableResidual Mc).map Mc.subtype = K := by
  obtain ⟨_,_,hc⟩ := terminal_alternatives_of_component_models
    hG T hempty hM hunique hmany hcard e hab hsolv hm K hKM hK
  rcases hc with ⟨hr,_⟩ | ⟨_,t,ht,hnt,_⟩ | ⟨⟨eK⟩,C,hCM,hC,hne,hnK,hnC,⟨eC⟩,hr⟩
  · exact hr
  · have hn := terminal_component_normal hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK
    exact (hnt (((normal_subgroupOf_iff_le_normalizer hKM).mp hn)
      ((terminal_outside hG T hempty hM hunique hmany hcard e).1.2 ht))).elim
  · exact (terminal_normal_pair_impossible hG T hempty hM hunique hmany hcard e hab hsolv
      K C hKM hCM hK hC hne.symm hnK hnC eK eC hr).elim

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
