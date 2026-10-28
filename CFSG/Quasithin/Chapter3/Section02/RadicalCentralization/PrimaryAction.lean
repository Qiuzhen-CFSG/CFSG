module

public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.PrimaryRadical
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.SourceNormality
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections

/-!
# Irreducibility of the original primary radical

The literal quotient I_p/O₂(I_p) is the full odd core of L/O₂(L).
Its Frattini quotient therefore has the A.3.6 irreducible Sylow action.
The comparison below intertwines the actual conjugation by T∩L with
its actual Sylow image in the component quotient. Thus T acts
irreducibly on I_p/O₂,Φ(I_p), including all higher homocyclic exponents.
Source: Aschbacher--Smith A.3.6, pp.43--45, used in 3.2.14, p.585.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.RadicalCentralization
open Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

private def primaryCoreEquiv
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    XiQuotient (primaryRadical p L) ≃* pCore p (radicalLocalImage T L) :=
  (primaryRadicalQuotientEquiv hG T hL ho).trans
    (((radicalLocalQuotientEquiv hL).subgroupMap _).trans
      (MulEquiv.subgroupCongr (pCore_map_iso p (radicalLocalQuotientEquiv hL))))

private theorem primaryCoreEquiv_apply_mk
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (x : primaryRadical p L) :
    (primaryCoreEquiv hG T hL ho (QuotientGroup.mk' _ x) : radicalLocalImage T L) =
      radicalLocalQuotientEquiv hL
        (QuotientGroup.mk' (pCore 2 L) (inclusion (map_subtype_le _) x)) := by
  change radicalLocalQuotientEquiv hL
    (primaryRadicalQuotientEquiv hG T hL ho (QuotientGroup.mk' _ x)) = _
  rw [primaryRadicalQuotientEquiv_apply_mk]

private def primaryFrattiniEquiv
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    XiFrattiniQuotient (primaryRadical p L) ≃*
      (pCore p (radicalLocalImage T L) ⧸ frattini (pCore p (radicalLocalImage T L))) :=
  QuotientGroup.congr _ _ (primaryCoreEquiv hG T hL ho) (frattini_map_equiv _)

private theorem primaryFrattiniEquiv_apply_mk
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (x : XiQuotient (primaryRadical p L)) :
    primaryFrattiniEquiv hG T hL ho (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (primaryCoreEquiv hG T hL ho x) := rfl

private theorem frattini_equivariant {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (α : MulAut A) (β : MulAut B)
    (he : ∀ a, e (α a) = β (e a)) (z : A ⧸ frattini A) :
    QuotientGroup.congr _ _ e (frattini_map_equiv e)
      (quotientAut (frattini A) α z) =
      quotientAut (frattini B) β (QuotientGroup.congr _ _ e (frattini_map_equiv e) z) := by
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective _ z
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' _ (e (α a)) = quotientAut (frattini B) β (QuotientGroup.mk' _ (e a))
  rw [quotientAut_apply_mk,he]

private theorem primaryFrattiniEquiv_equivariant
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hT : (T : Subgroup G) ≤ normalizer (primaryRadical p L : Set G))
    (t : ((T : Subgroup G) ⊓ L : Subgroup G))
    (a : XiFrattiniQuotient (primaryRadical p L)) :
    primaryFrattiniEquiv hG T hL ho
      (xiFrattiniAction (T : Subgroup G) (primaryRadical p L) hT
        (inclusion inf_le_left t) a) =
      FittingActions.coreFrattiniAction p (radicalLocalImage T L)
        (radicalLocalQuotientEquiv hL
          (QuotientGroup.mk' (pCore 2 L) (inclusion inf_le_right t)))
        (primaryFrattiniEquiv hG T hL ho a) := by
  let X := primaryRadical p L
  let := conjMulDistribMulActionOfLeNormalizer (T : Subgroup G) X hT
  let α := quotientAut (pCore 2 X)
    (MulDistribMulAction.toMulAut (T : Subgroup G) X (inclusion inf_le_left t))
  let g := radicalLocalQuotientEquiv hL
    (QuotientGroup.mk' (pCore 2 L) (inclusion inf_le_right t))
  change QuotientGroup.congr _ _ (primaryCoreEquiv hG T hL ho) _
    (quotientAut _ α a) = quotientAut _ (FittingActions.coreAction p _ g)
      (QuotientGroup.congr _ _ (primaryCoreEquiv hG T hL ho) _ a)
  apply frattini_equivariant
  intro z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective _ z
  change primaryCoreEquiv hG T hL ho
    (quotientAut (pCore 2 X)
      (MulDistribMulAction.toMulAut (T : Subgroup G) X (inclusion inf_le_left t))
      (QuotientGroup.mk' _ x)) = _
  rw [quotientAut_apply_mk]
  apply Subtype.ext
  rw [primaryCoreEquiv_apply_mk,FittingActions.coreAction_apply,primaryCoreEquiv_apply_mk]
  change radicalLocalQuotientEquiv hL (QuotientGroup.mk' (pCore 2 L)
    ((inclusion (map_subtype_le _) : X →* L)
      (MulDistribMulAction.toMulAut (T : Subgroup G) X (inclusion inf_le_left t) x))) = _
  have hc : (inclusion (map_subtype_le _) : X →* L)
      (MulDistribMulAction.toMulAut (T : Subgroup G) X (inclusion inf_le_left t) x) =
      inclusion inf_le_right t * inclusion (map_subtype_le _) x * (inclusion inf_le_right t)⁻¹ := rfl
  rw [hc,map_mul,map_inv,map_mul,map_mul,map_inv,map_mul]

private theorem fitting_card_dvd_of_equiv
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B] (e : A ≃* B) :
    Nat.card (fittingSubgroup A) ∣ Nat.card (fittingSubgroup B) := by
  have hle : (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    rintro N ⟨hN,hnil⟩
    apply map_le_iff_le_comap.mp
    let := hnil
    exact le_sSup ⟨hN.map _ e.surjective,Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩
  rw [Nat.card_congr (e.subgroupMap (fittingSubgroup A)).toEquiv]
  exact card_dvd_of_le hle

/-- A.3.6 supplies irreducibility on the full actual primary radical,
with no elementary-quotient or action-kernel hypothesis. -/
theorem primaryRadical_irreducible
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hT : (T : Subgroup G) ≤ normalizer (primaryRadical p L : Set G)) :
    ∀ A : Subgroup (XiFrattiniQuotient (primaryRadical p L)),
      (∀ t a, a ∈ A → xiFrattiniAction (T : Subgroup G)
        (primaryRadical p L) hT t a ∈ A) → A = ⊥ ∨ A = ⊤ := by
  let C := radicalLocalImage T L
  let e : XiQuotient L ≃* C := radicalLocalQuotientEquiv hL
  let q : L →* C := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨S,hS⟩ := IndexTwo.isSylowIn_inf_of_subnormal hL.2.1 le_sup_left hL.1.subnormal
  let S' : Sylow 2 C := S.mapSurjective hq
  have hQ := uniqueness_local_quotient_sqtk hG hL.2.2
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun (A : Type u) _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun (A : Type u) _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
  have hc : C.IsCComponent := by
    let := pCore_isNilpotent (p := 2) (G := (L ⊔ (T : Subgroup G) : Subgroup G))
    exact hL.1.map_quotient _
  have ha := proposition_1_2_1_four_earlier_conclusion h36 hQ hL.1
  have hnC : ¬ IsQuasisimple C := fun h => hn (h.of_mulEquiv e.symm)
  have hdC := hd.trans (fitting_card_dvd_of_equiv e)
  have hi := ((FittingActions.strengthened_frattini_actions hQ
    (pCore_quotient_pCore_eq_bot 2) hc ha).2 hnC).2.2 p hdC
  let v := primaryFrattiniEquiv hG T hL ho
  intro A hA
  have hstable : ∀ s : S', ∀ a ∈ A.map v.toMonoidHom,
      FittingActions.coreFrattiniAction p C s a ∈ A.map v.toMonoidHom := by
    rintro s a ⟨b,hb,rfl⟩
    obtain ⟨l,hl,hls⟩ := s.property
    have hlU : (l : G) ∈ (T : Subgroup G) ⊓ L := hS ▸ mem_map_of_mem L.subtype hl
    let t : ((T : Subgroup G) ⊓ L : Subgroup G) := ⟨l,hlU⟩
    refine ⟨xiFrattiniAction (T : Subgroup G) (primaryRadical p L) hT
      (inclusion inf_le_left t) b,hA _ _ hb,?_⟩
    exact (primaryFrattiniEquiv_equivariant hG T hL ho hT t b).trans
      (congrArg (fun g : C => FittingActions.coreFrattiniAction p C g (v b)) hls)
  rcases (hi.2.2.2 S').1 (A.map v.toMonoidHom) hstable with hb | ht
  · exact Or.inl ((A.map_eq_bot_iff_of_injective v.injective).mp hb)
  · right
    apply map_injective (f := v.toMonoidHom) v.injective
    rw [map_top_of_surjective v.toMonoidHom v.surjective]
    exact ht

end CFSG.Quasithin.Chapter3.RadicalCentralization
