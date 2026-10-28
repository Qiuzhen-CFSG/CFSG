module
public import Theory.Representation.BinaryTensorThree.Recognition
public import CFSG.Quasithin.ChapterD.Section02.LinearThreeSimpleTypes
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.TensorConstituents

/-!
# Single-factor constituents of the original terminal module

Every simple constituent for the full normal component pair, inside an
irreducible ambient subquotient of the original U/Z, is trivial on one factor.
If both factors move it, their simple types are natural by the source quadratic
classification. Two nonzero natural constituent maps reconstruct the actual
nine-dimensional tensor. The checked tensor exclusion then gives a contradiction
with the original actor budget and the diagram automorphism.

The terminal theorem constructs the product coordinates from the source
exchanged-component geometry. The first coordinate is literal inclusion of K*,
and the second is conjugation by the same original quotient actor. It supplies
the placed actor and all natural-type and tensor-marking inputs itself.

This is a constituent statement. Lifting it to the selected supports in the
possibly nonsemisimple original module, proving their invariance under the whole
Mc intersect N_G(K), and completing the normal-component and same-vector suitable
branches remain with qt-e-suitable-component-supports. Original14.6.18 remains
hsolv, with its final discharge owned by qt-e-14625-source.
Source: Aschbacher--Smith D.3.7, F.9.18(5),14.6.22,
printed pp.197--199,325--326,1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
universe u v
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

/-- An original irreducible component-orbit constituent cannot be moved by both actual component coordinates. -/
theorem source_nonnormal_constituent_single_factor
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (A : Subgroup (H ⧸ pCore 2 H))
    (hAT : A ≤ actorImage H T) (hA : QuadraticMember a.representation A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    (S : Subrepresentation a.representation) (L : Subrepresentation S.toRepresentation)
    (hL : IsIrreducible L.quotientRepresentation)
    (U : Subrepresentation (L.quotientRepresentation.comp
      (actorImage H (conjugateSpanBy K (T : Subgroup G))).subtype))
    (hU : IsIrreducible U.toRepresentation)
    (p : actorImage H (conjugateSpanBy K (T : Subgroup G)) ≃*
      (actorImage H K × actorImage H K)) (t : H ⧸ pCore 2 H)
    (hleft : ∀ k : actorImage H K, (p.symm (k,1)).val = k.val)
    (hright : ∀ k : actorImage H K, (p.symm (1,k)).val = t*k.val*t⁻¹) :
    let ρ := U.toRepresentation.comp p.symm.toMonoidHom
    ρ.comp (MonoidHom.inl (actorImage H K) (actorImage H K)) = 1 ∨
      ρ.comp (MonoidHom.inr (actorImage H K) (actorImage H K)) = 1 := by
  let D := actorImage H K
  let N := actorImage H (conjugateSpanBy K (T : Subgroup G))
  let σ := L.quotientRepresentation
  let ρ : Representation (ZMod 2) (D × D) U.toSubmodule :=
    U.toRepresentation.comp p.symm.toMonoidHom
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) :=
    Module.Finite.of_finite
  let : Module.Finite (ZMod 2) (S ⧸ L.toSubmodule) := inferInstance
  let : IsQuasisimple D := (source_quotient_component
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK).2
  let : IsIrreducible U.toRepresentation := hU
  let : IsIrreducible ρ :=
    (irreducible_comp_surjective_iff p.symm.toMonoidHom p.symm.surjective U.toRepresentation).mpr hU
  have htypes := source_nonnormal_subquotient_all_natural
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn a A hAT hA hfaith S L hL
  change ρ.comp (MonoidHom.inl D D) = 1 ∨ ρ.comp (MonoidHom.inr D D) = 1
  by_cases hl : ρ.comp (MonoidHom.inl D D) = 1
  · exact Or.inl hl
  right
  by_contra hr
  obtain ⟨b,⟨c⟩⟩ := BinaryTensorThree.exists_marking_of_moving_natural_types ρ hl hr
    (ChapterD.natural_linear_three_of_nested_conjugate σ D N htypes U
      (p.symm.toMonoidHom.comp (MonoidHom.inl D D)) 1
      (fun k => by
        change (p.symm (k,1)).val = 1*k.val*1⁻¹
        rw [one_mul,inv_one,mul_one]
        exact hleft k))
    (ChapterD.natural_linear_three_of_nested_conjugate σ D N htypes U
      (p.symm.toMonoidHom.comp (MonoidHom.inr D D)) t hright)
  let c' : U.toRepresentation.Equiv
      (BinaryTensorThree.baseRepresentation.comp (p.trans b).toMonoidHom) :=
    Representation.Equiv.mk c.toLinearEquiv (by
      intro n
      have hc := c.isIntertwining' (p n)
      simpa only [ρ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,p.symm_apply_apply,
        MulEquiv.trans_apply] using hc)
  have hbudget : fixedCodim σ A ≤ 2 * rank A := by
    change fixedCodim L.quotientRepresentation A ≤ 2 * rank A
    have hS := fixedCodim_subrepresentation_le a.representation S A
    have hL' := fixedCodim_quotient_add_subrepresentation_le S.toRepresentation L A
    have hh : fixedCodim a.representation A ≤ 2 * rank A := hA.2.2
    omega
  exact source_no_tensor_constituent
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
    σ A hA.1 hfaith hbudget U (p.trans b) c'

/-- Construct the marked product on the original quotient component orbit, retaining both literal embeddings. -/
theorem source_nonnormal_component_product_coordinates
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) :
    ∃ (p : actorImage H (conjugateSpanBy K (T : Subgroup G)) ≃*
      (actorImage H K × actorImage H K)) (t : H ⧸ pCore 2 H),
      t ∈ actorImage H T ∧
      (∀ k : actorImage H K, (p.symm (k,1)).val = k.val) ∧
      (∀ k : actorImage H K, (p.symm (1,k)).val = t*k.val*t⁻¹) := by
  obtain ⟨_,geo⟩ := source_nonnormal_quotient_geometry
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn
  obtain ⟨t,ht,hnt⟩ := geo.moved
  obtain ⟨hs,hd,hc,hr,_⟩ := geo.pair t ht hnt
  obtain ⟨m⟩ := RepresentationReduction.SourceRestrictions.Cases.Exchanged.productMarking_of_disjoint
    (le_normalizer_componentOrbit (actorImage H K) (actorImage H T) ht) hs hd hc hr
  let q := MulEquiv.subgroupCongr (quotient_componentOrbit H K T hKH hH.1.2)
  let p := q.symm.trans m.product.symm
  refine ⟨p,t⁻¹,(actorImage H T).inv_mem ht,?_,?_⟩
  · intro k
    exact m.first k
  · intro k
    change (m.product (1,k)).val = t⁻¹*k.val*(t⁻¹)⁻¹
    rw [inv_inv]
    exact m.second k

/-- The original terminal action has only single-factor constituents; the product marking and all representation inputs are constructed. -/
theorem terminal_nonnormal_constituents_single_factor
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
        (B : Subgroup Mc),
        B ≤ (((sourceResidual M Mc ⊔ (T : Subgroup G)) ⊓ Mc).pCoreIn 2).subgroupOf Mc ∧
        QuadraticMember a.representation (B.map (QuotientGroup.mk' (pCore 2 Mc))) ∧
        ∃ (p : actorImage Mc (conjugateSpanBy K (T : Subgroup G)) ≃*
          (actorImage Mc K × actorImage Mc K)) (t : Mc ⧸ pCore 2 Mc),
          t ∈ actorImage Mc T ∧
          (∀ k : actorImage Mc K, (p.symm (k,1)).val = k.val) ∧
          (∀ k : actorImage Mc K, (p.symm (1,k)).val = t*k.val*t⁻¹) ∧
          BinaryTensorThree.HasSingleFactorConstituents a.representation
            (actorImage Mc (conjugateSpanBy K (T : Subgroup G))) (actorImage Mc K) p := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hU,a,B,I,hB,_,_,hA,hfaith,_⟩ := terminal_nonnormal_component_span_inputs
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  obtain ⟨p,t,ht,hleft,hright⟩ := source_nonnormal_component_product_coordinates
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK hn
  refine ⟨hU,a,B,hB,hA,p,t,ht,hleft,hright,?_⟩
  intro S L hL U hU
  exact source_nonnormal_constituent_single_factor
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK hn a
    (B.map (QuotientGroup.mk' (pCore 2 Mc)))
    (source_internal_actor_le_sylow T hout.1.2 B hB) hA hfaith
    S L hL U hU p t hleft hright

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
