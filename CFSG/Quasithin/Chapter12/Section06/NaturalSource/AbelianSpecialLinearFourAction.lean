module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSpecialLinearFourGraph
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSpecialLinearFourScalar
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NoFF.NativeSource
/-!
# Irreducibility of the original SL₃(4) graph module

The original scalar cubic has zero fixed space on the literal U_H/V₁.
A generator therefore acts without nonzero fixed vectors. The graph actor
and native B.5.1 exclude FF modules for the actual faithful quotient action.
The two strict no-FF inequalities, together with the original ratio-two
quadratic actor, saturate every nonzero component-moved invariant submodule.
Scalar movement makes every invariant submodule component-moved, proving
irreducibility for H-star on the full original section.

The final application retains the very same quadratic actor, edge-core
placement and residual-faithfulness bound. This proves the module saturation
step; the natural-plus-dual identification and nonsingular-centralizer
contradiction remain to exclude the source SL₃(4) branch.
Source: Aschbacher–Smith 12.6.32, printed p.837, using F.9.18(7) and B.5.1.
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
variable (hn : (K.subgroupOf H).Normal)
  (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4)
  [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)]
  (a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁)

include hz hTV hTz hbound hTI hns hH hKH hK hn hm in
/-- A scalar generator has no nonzero fixed vector on the actual source section. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_scalar_generator :
    ∃ x : H ⧸ pCore 2 H,
      x ∈ (center (actorImage H K)).map (actorImage H K).subtype ∧
      ∀ v, a.representation x v = v → v = 0 := by
  let C := (center (actorImage H K)).map (actorImage H K).subtype
  obtain ⟨_,hcard,_⟩ := S.original_abelian_normal_specialLinearFour_scalar
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm
  obtain ⟨_,hfixed,_⟩ := S.original_abelian_normal_specialLinearFour_scalar_movement
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm a
  change Nat.card C = 3 at hcard
  change fixedSpace a.representation C = ⊥ at hfixed
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 (by rw [hcard])
  have hxne : x ≠ 1 := by intro he; simp [he] at hx
  have hgen : zpowers (x : H ⧸ pCore 2 H) = C := by
    have hh := congrArg (Subgroup.map C.subtype) (zpowers_eq_top_of_prime_card hcard hxne)
    simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,Subgroup.coe_subtype] using hh
  refine ⟨x,x.property,?_⟩
  intro v hv
  have hvC : v ∈ fixedSpace a.representation C := by
    rw [←hgen,mem_fixedSpace_zpowers_iff]
    exact hv
  exact (Submodule.mem_bot (ZMod 2)).mp (hfixed ▸ hvC)

variable (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
      (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hn hm hgen in
/-- Native B.5.1 and the original graph actor exclude FF modules. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_not_ff :
    ¬ IsFFModule a.representation := by
  let B := actorImage H K
  let : B.Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  let _ : IsQuasisimple B :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  obtain ⟨h2,_,_⟩ := S.original_abelian_normal_specialLinearFour_quotient
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hm
  obtain ⟨e,t,c,ht⟩ := S.original_abelian_normal_specialLinearFour_graph_model
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hm
  exact NoFF.Native.not_ff a.representation
    ((S.original_star_sqtk D hZ z hz hH).subgroup B) e h2
    (pCore_quotient_pCore_eq_bot 2) a.faithful _ c ht

include hz hTV hTz hbound hTI hns hH hKH hK hn hm hgen in
/-- The original quadratic bound saturates each nonzero component-moved submodule. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_saturation
    (W : Subrepresentation a.representation) (hW : W.toSubmodule ≠ ⊥)
    (hfull : subspaceCommutator a.representation W.toSubmodule (actorImage H K) =
      W.toSubmodule) : W.toSubmodule = ⊤ := by
  let B := actorImage H K
  let : B.Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  let _ : IsQuasisimple B :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  obtain ⟨h2,_,_⟩ := S.original_abelian_normal_specialLinearFour_quotient
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hm
  obtain ⟨e,t,c,ht⟩ := S.original_abelian_normal_specialLinearFour_graph_model
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hm
  obtain ⟨x,hx,hfree⟩ := S.original_abelian_normal_specialLinearFour_scalar_generator
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm a
  obtain ⟨hU,b,_,A,_,hEA,_,hcod,_⟩ :=
    S.original_abelian_quadratic_actor D hZ z hz hTV hTz hbound hTI hns hH
  have heq := a.representation_eq b
  rw [←heq] at hcod
  have he := NoFF.Native.moved_space a.representation
    ((S.original_star_sqtk D hZ z hz hH).subgroup B) e h2
    (pCore_quotient_pCore_eq_bot 2) _ c ht x hx hfree W hW hfull
    (A.map (QuotientGroup.mk' (pCore 2 H))) hEA hcod
  exact he.trans (S.original_abelian_normal_specialLinearFour_scalar_movement
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm a).2.2

include hz hTV hTz hbound hTI hns hH hKH hK hn hm hgen in
/-- The actual H-star action on all of U_H/V₁ is irreducible. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_irreducible :
    IsIrreducible a.representation := by
  let B := actorImage H K
  have hq : IsQuasisimple B :=
    (S.original_abelian_component_quasisimple D hZ z hz hTV hTz hbound hTI hns hH hKH hK).of_mulEquiv
      (componentStarEquiv H K hKH hK)
  let _ := hq.simple
  let _ : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  let _ : Nontrivial (H ⧸ pCore 2 H) := B.subtype_injective.nontrivial
  have hU : Nontrivial (Additive ((D.fullSetup hZ T z).UH H ⧸
      ((D.fullSetup hZ T z).V₁).subgroupOf ((D.fullSetup hZ T z).UH H))) := by
    by_contra h
    let _ := not_nontrivial_iff_subsingleton.mp h
    obtain ⟨g,hg⟩ := exists_ne (1 : H ⧸ pCore 2 H)
    exact hg (a.faithful (Subsingleton.elim _ _))
  let _ := hU
  obtain ⟨x,hx,hfree⟩ := S.original_abelian_normal_specialLinearFour_scalar_generator
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm a
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun W => ?_⟩
  by_cases hW : W.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hW)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply S.original_abelian_normal_specialLinearFour_saturation
      D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm a hgen W hW
    have hKW : subspaceCommutator W.toRepresentation ⊤ (actorImage H K) = ⊤ :=
      Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved.full_of_fixedFree
        (actorImage H K) W.toRepresentation x ((map_subtype_le _) hx)
        (fun v hv => Subtype.ext (hfree v (congrArg Subtype.val hv)))
    have he := subspaceCommutator_map_embedding a.representation W.toRepresentation
      (MonoidHom.id (H ⧸ pCore 2 H)) W.toSubmodule.subtype (fun _ _ => rfl)
      (actorImage H K) ⊤
    simpa only [hKW,Submodule.map_top,Submodule.range_subtype,Subgroup.map_id] using he

omit [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)] in
include hz hTV hTz hbound hTI hns hH hKH hK hn hm hgen in
/-- Keep the original quadratic actor and both its ratio and residual-faithfulness
bounds while identifying the whole source section as an irreducible non-FF module. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_quadratic_irreducible :
    ∃ hU : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H),
      let _ := hU
      ∃ b : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁,
        quadraticRatio b.representation ≤ 2 ∧
        ¬ IsFFModule b.representation ∧ IsIrreducible b.representation ∧
        ∃ A : Subgroup H,
          A ≤ (((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H ∧
          IsElementaryTwo (A.map (QuotientGroup.mk' (pCore 2 H))) ∧
          IsQuadratic b.representation (A.map (QuotientGroup.mk' (pCore 2 H))) ∧
          fixedCodim b.representation (A.map (QuotientGroup.mk' (pCore 2 H))) ≤
            2 * rank (A.map (QuotientGroup.mk' (pCore 2 H))) ∧
          A.map (QuotientGroup.mk' (pCore 2 H)) ⊓
            centralizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  obtain ⟨hU,b,hq,A,hA,hEA,hquad,hcod,hfaith⟩ :=
    S.original_abelian_quadratic_actor D hZ z hz hTV hTz hbound hTI hns hH
  let _ := hU
  exact ⟨hU,b,hq,
    S.original_abelian_normal_specialLinearFour_not_ff
      D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm b hgen,
    S.original_abelian_normal_specialLinearFour_irreducible
      D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm b hgen,
    A,hA,hEA,hquad,hcod,hfaith⟩

end CFSG.Quasithin.Chapter12.Section06
