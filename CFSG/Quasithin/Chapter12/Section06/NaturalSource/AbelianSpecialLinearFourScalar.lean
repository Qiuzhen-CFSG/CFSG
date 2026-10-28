module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalSpecialLinearFour
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalMovement
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianQuadratic
public import Theory.Representation.GoldschmidtONan.Basic
/-!
# The scalar cubic on the original SL₃(4) section

The full Borel marking places the scalar center inside L₁-star. It is a
normal cubic subgroup of H-star. Original F.9 irreducibility propagates
its nontrivial action from the seed to all of U_H/V₁. Coprime splitting
then gives zero fixed space. The final application uses the same action
and quadratic actor supplied by F.9.16, preserving both ratio bounds.

Source: Aschbacher–Smith 12.6.31–32, printed pp.836–837, using F.9.1–2.
This prepares the module analysis; it does not exclude SL₃(4).
-/
public section
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


include hz hTV hTz hbound hTI hns hH hKH hK in
/-- The actual scalar center is a normal cubic subgroup inside the original L₁-star. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_scalar
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4) :
    let C := (center (actorImage H K)).map (actorImage H K).subtype
    C.Normal ∧ Nat.card C = 3 ∧ C ≤ actorImage H (D.fullSetup hZ T z).L₁ := by
  let B := actorImage H K
  let C := (center B).map B.subtype
  let : B.Normal := hn.map _ (QuotientGroup.mk'_surjective _)
  have hnC : C.Normal := ConjAct.normal_of_characteristic_of_normal
  obtain ⟨P,_,hB⟩ := S.original_abelian_normal_specialLinearFour_borel_star
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm
  have hCL : C ≤ actorImage H (D.fullSetup hZ T z).L₁ := by
    rw [←hB]
    exact map_mono (center_le_normalizer (P : Set B))
  obtain ⟨F,hF,hfin,hcard,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let e : B ≃* SL(3,F) := (componentStarEquiv H K hKH hK).symm.trans eK
  have hc : Nat.card C = 3 := by
    rw [card_map_of_injective B.subtype_injective,Nat.card_congr (centerCongr e).toEquiv,
      Atlas.ExceptionalSupport.card_sl_center,Fintype.card_fin,hcard]
    norm_num
  exact ⟨hnC,hc,hCL⟩

include hz hTV hTz hbound hTI hns hH hKH hK in
/-- The scalar cubic moves all of the literal U_H/V₁ and has zero fixed space. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_scalar_movement
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4)
    [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)]
    (a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁) :
    let C := (center (actorImage H K)).map (actorImage H K).subtype
    subspaceCommutator a.representation ⊤ C = ⊤ ∧
      fixedSpace a.representation C = ⊥ ∧
      subspaceCommutator a.representation ⊤ (actorImage H K) = ⊤ := by
  let C := (center (actorImage H K)).map (actorImage H K).subtype
  obtain ⟨hnC,hc,hCL⟩ := S.original_abelian_normal_specialLinearFour_scalar
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm
  let _ := hnC
  change Nat.card C = 3 at hc
  have hne : C ≠ ⊥ := by
    intro h
    have hcard : Nat.card C = 1 := card_eq_one.mpr h
    omega
  have ha : subspaceCommutator a.representation ⊤ C = ⊤ :=
    S.original_normal_local_actor_full_movement D hZ z hz hTV hTz hbound hH a C hne
      (hCL.trans (map_mono (comap_mono le_sup_left)))
  have hsplit : IsCompl (fixedSpace a.representation C)
      (subspaceCommutator a.representation ⊤ C) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := a.representation) (Y := C)
        (by rw [hc]; decide))
  refine ⟨ha,?_,?_⟩
  · have hd := hsplit.disjoint
    rw [ha] at hd
    exact disjoint_top.mp hd
  · apply top_unique
    calc
      ⊤ = subspaceCommutator a.representation ⊤ C := ha.symm
      _ ≤ subspaceCommutator a.representation ⊤ (actorImage H K) := by
        apply Submodule.span_mono
        rintro _ ⟨x,hx,v,hv,rfl⟩
        exact ⟨x,(map_subtype_le _) hx,v,hv,rfl⟩


include hz hTV hTz hbound hTI hns hH hKH hK in
/-- Scalar movement on the actual quadratic action, with the same original actor
and both ratio bounds retained for the module classification. -/
theorem SourceHypothesis.original_abelian_normal_specialLinearFour_scalar_fixed_free
    (hn : (K.subgroupOf H).Normal)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 4) :
    ∃ hU : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H),
      let _ := hU
      ∃ a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁,
        quadraticRatio a.representation ≤ 2 ∧
        subspaceCommutator a.representation ⊤
          ((center (actorImage H K)).map (actorImage H K).subtype) = ⊤ ∧
        fixedSpace a.representation
          ((center (actorImage H K)).map (actorImage H K).subtype) = ⊥ ∧
        subspaceCommutator a.representation ⊤ (actorImage H K) = ⊤ ∧
        ∃ B : Subgroup H,
          B ≤ (((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H ∧
          IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
          IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
          fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
            2 * rank (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
          B.map (QuotientGroup.mk' (pCore 2 H)) ⊓
            centralizer (actorImage H (residual H) : Set (H ⧸ pCore 2 H)) = ⊥ := by
  obtain ⟨hU,a,hr,B,hB,he,hquad,hcodim,hfaith⟩ :=
    S.original_abelian_quadratic_actor D hZ z hz hTV hTz hbound hTI hns hH
  let _ := hU
  obtain ⟨hmoved,hfixed,hKmove⟩ := S.original_abelian_normal_specialLinearFour_scalar_movement
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hm a
  exact ⟨hU,a,hr,hmoved,hfixed,hKmove,B,hB,he,hquad,hcodim,hfaith⟩

end CFSG.Quasithin.Chapter12.Section06
