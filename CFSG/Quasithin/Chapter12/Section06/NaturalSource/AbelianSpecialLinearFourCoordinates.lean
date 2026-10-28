module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSpecialLinearFourAction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NativeSelection
public import Theory.Representation.SL3FourNaturalDual.HomogeneousOrbit
/-!
# Natural-plus-dual coordinates on the original SL₃(4) section

The original edge-core quadratic actor lies in T-star and is faithful on
K-star. Native constituent recognition selects a T-star-homogeneous natural
central section. Scalar movement lifts its coordinates to the constituent
itself; the proved saturation makes its T-star orbit the entire U_H/V₁.
The actual graph actor in T moves it to a disjoint constituent. Full SL₃(4)
automorphism coverage shows that these two translates exhaust the orbit,
so their two embeddings give equivariant natural-plus-dual coordinates.

The module is the literal U_H/V₁, the component map is its original inclusion
in H/O₂(H), and the scalar center is retained. All original earlier geometry
remains explicit. The final source exclusion is a separate application.
Source: Aschbacher–Smith 12.6.32, printed p.837, using B.4.5 and F.9.18(3–4,7).
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)


open Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule
open Representation.SL3FourNaturalDual
variable (hn : (K.subgroupOf H).Normal)
  (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4)
  [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)]
  (a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁)


variable (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hn hm hgen in
/-- A natural constituent homogeneous under the actual original Sylow image. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_constituent :
    ∃ I : Submodule (ZMod 2) (Additive ((D.fullSetup hZ T z).UH H ⧸
        ((D.fullSetup hZ T z).V₁).subgroupOf ((D.fullSetup hZ T z).UH H))),
      ∃ _hI : Homogeneous.IsIrrPlusWith a.representation (actorImage H K) (actorImage H T) I,
      ∃ e : actorImage H K ≃* SL, ∃ _n : NaturalCentralSection a.representation (actorImage H K) e I,
        Homogeneous.orbitSpan a.representation (actorImage H T) I = ⊤ ∧
        let ι : T →* H := inclusion (fun _x hx => hH.1.2 (Or.inr hx))
        ∃ t : T, ∃ c : Matrix.GeneralLinearGroup (Fin 3) F,
          (∀ g : SL, (e.symm g).val * (QuotientGroup.mk' (pCore 2 H)) (ι t) =
            (QuotientGroup.mk' (pCore 2 H)) (ι t) *
              (e.symm (Matrix.PSL3.OuterSolvable.linearConjSL F c
                (Matrix.SpecialLinearGroup.inverseTranspose g))).val) ∧
          Disjoint I (I.map (a.representation ((QuotientGroup.mk' (pCore 2 H)) (ι t)))) := by
  let B := actorImage H K
  let : B.Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  let _ : IsQuasisimple B :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  have hTH : (T : Subgroup G) ≤ H := fun _x hx => hH.1.2 (Or.inr hx)
  obtain ⟨eK,_,_,_⟩ := S.original_abelian_normal_specialLinearFour_graph_model
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hm
  obtain ⟨x,hx,hfree⟩ := S.original_abelian_normal_specialLinearFour_scalar_generator
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm a
  obtain ⟨_,hU,b,A,_,hAT,hEA,hquad,hcod,hfaith,_⟩ :=
    S.original_abelian_component_span_actors D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen
  have heq := a.representation_eq b
  rw [←heq] at hquad hcod
  rw [conjugateSpan_eq_of_normal H K T hKH hTH hn] at hfaith
  obtain ⟨I,hI,_,e,⟨n⟩⟩ := NaturalRecognition.Native.quadratic_natural_constituent
    a.representation B eK (S.original_star_sqtk D hZ z hz hH) a.faithful x hx hfree
    (A.map (QuotientGroup.mk' (pCore 2 H))) (actorImage H T)
    (T.isPGroup'.comap_subtype.map _) hAT hEA hquad hcod hfaith
  obtain ⟨_,hg⟩ := S.original_abelian_normal_specialLinearFour_reduction
    D hZ z hz hTV hTz hbound hTI hns hH hKH hgen hn hm
  have hsup : B ⊔ actorImage H T = ⊤ := by
    unfold B actorImage
    rw [←Subgroup.map_sup,←subgroupOf_sup hKH hTH,hg,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let O := Homogeneous.orbitSubrepresentation a.representation hI.normalizes hI.isIrrPlus hsup
  have hfull : Homogeneous.orbitSpan a.representation (actorImage H T) I = ⊤ :=
    S.original_abelian_normal_specialLinearFour_saturation
      D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm a hgen O
      (Homogeneous.orbitSpan_ne_bot a.representation hI.isIrrPlus)
      (Homogeneous.orbitSpan_full_commutator a.representation hI.normalizes hI.isIrrPlus)
  obtain ⟨t,c,ht⟩ := S.original_abelian_normal_specialLinearFour_graph_relation
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn e
  let ι : T →* H := inclusion hTH
  let ts := (QuotientGroup.mk' (pCore 2 H)) (ι t)
  have hmoved := graph_moves_natural_section a.representation
    (B.subtype.comp e.symm.toMonoidHom) ts I (n.lift hI.isIrrPlus.choose_spec.1) c
    (n.lift_symm_equivariant hI.isIrrPlus.choose_spec.1) ht
  refine ⟨I,hI,e,n,hfull,t,c,ht,?_⟩
  exact ((hI.isIrrPlus.eq_or_disjoint_conjugate_of_normal_restriction a.representation
    (S.original_abelian_normal_specialLinearFour_irreducible
      D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm a hgen) B ts).resolve_left hmoved).symm

include hz hTV hTz hbound hTI hns hH hKH hK hn hm hgen in
/-- The full original quotient module, with the literal component inclusion,
 is the natural-plus-dual SL₃(4) module. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_coordinates :
    ∃ (e : actorImage H K ≃* SL)
      (E : Additive ((D.fullSetup hZ T z).UH H ⧸
        ((D.fullSetup hZ T z).V₁).subgroupOf ((D.fullSetup hZ T z).UH H)) ≃ₗ[ZMod 2]
          Representation.SL3FourNaturalDual.V),
      ∀ (k : actorImage H K) v,
        E (a.representation k v) = representation (e k) (E v) := by
  obtain ⟨I,hI,e,n,hfull,t,c,ht,hdis⟩ :=
    S.original_abelian_normal_specialLinearFour_constituent
      D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm a hgen
  let ι : T →* H := inclusion (fun _x hx => hH.1.2 (Or.inr hx))
  let ts := (QuotientGroup.mk' (pCore 2 H)) (ι t)
  let tP : actorImage H T := ⟨ts,⟨ι t,t.property,rfl⟩⟩
  have hspan := HomogeneousOrbit.natural_orbit_span a.representation hI e n tP c ht
  have hcomp : IsCompl I (I.map (a.representation ts)) :=
    ⟨hdis,codisjoint_iff.mpr (hspan.symm.trans hfull)⟩
  let m := graphSumMarking a.representation ((actorImage H K).subtype.comp e.symm.toMonoidHom)
    ts I (n.lift hI.isIrrPlus.choose_spec.1) c hcomp
    (n.lift_symm_equivariant hI.isIrrPlus.choose_spec.1) ht
  refine ⟨e,m.coordinates,fun k v => ?_⟩
  have he : m.actor (e k) = k := by
    change (e.symm (e k) : H ⧸ pCore 2 H) = k
    rw [e.symm_apply_apply]
  exact he ▸ m.equivariant (e k) v

end CFSG.Quasithin.Chapter12.Section06
