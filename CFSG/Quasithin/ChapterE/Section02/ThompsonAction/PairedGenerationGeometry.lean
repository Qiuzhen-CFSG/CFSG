module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedGenerationLifts
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PairedLift
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModels

/-!
# The nonbinary natural pair obstructs rank-one E-generation

The marked product gives the literal two simple SL₂ factors and their Sylow
intersections. Their rank is the common field degree, and each proper Sylow
overgroup lies in its normalizer. These data discharge the paired obstruction
once the actual elementary lifts and ambient factor permutation are supplied.
Source: Aschbacher--Smith E.1.2--6, E.2.3 and 6.1.5, pp.209--210,216--217,666.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction.PairGeneration
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem linear_factor_facts (F : BinaryField) (hF : 1 < F.degree)
    (L : Subgroup H) (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
    (P : Sylow 2 L) :
    IsSimpleGroup L ∧ ¬ Group.IsSolvable L ∧ Nat.card P = 2 ^ F.degree ∧
      1 < Group.rank P ∧
      (∀ K : Subgroup L, (P : Subgroup L) ≤ K → K ≠ ⊤ →
        K ≤ normalizer (P : Set L)) := by
  have hlarge : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ F.degree by omega)
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier (by omega)
  let : IsSimpleGroup L := (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL).isSimpleGroup
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 Q :=
    (SL2NaturalOffenders.Ratios.sylow_offender Q).1.2
  have hPQ : (P : Subgroup L).map e.toMonoidHom = Q := rfl
  let : IsElementaryAbelian 2 ((P : Subgroup L).map e.toMonoidHom) := hPQ ▸ inferInstance
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective
    ((P : Subgroup L).equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom
    ((P : Subgroup L).equivMapOfInjective e.toMonoidHom e.injective).injective
  have hcard := (SL2NaturalOffenders.sylow_card L e P).trans F.card_eq
  refine ⟨inferInstance,Group.IsPerfect.not_isSolvable L,hcard,
    hF.trans_le (IsElementaryAbelian.rank_ge_of_card (p := 2) hcard),?_⟩
  intro K hPK hK
  have hK' : K.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hK
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    rw [he,map_top_of_surjective _ e.surjective]
  have hn := Matrix.SpecialLinearGroup.overgroup_le_sylowNormalizer Q (map_mono hPK) hK'
  have hm : (normalizer (P : Set L)).map e.toMonoidHom =
      normalizer (Q : Set (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) := by
    exact map_normalizer_eq_of_bijective _ e.bijective
  exact (map_le_map_iff_of_injective e.injective).mp (hm ▸ hn)

variable (F : BinaryField)
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F.Carrier

omit [Finite H] in
private theorem axis_inl (η : D × D →* H) (P : Subgroup D) :
    P.map (η.comp (MonoidHom.inl D D)) = (P.prod ⊥).map η := by
  rw [←map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩; exact ⟨ha,rfl⟩
  · rintro ⟨h,hx⟩; exact ⟨x.1,h,Prod.ext rfl hx.symm⟩

omit [Finite H] in
private theorem axis_inr (η : D × D →* H) (P : Subgroup D) :
    P.map (η.comp (MonoidHom.inr D D)) = ((⊥ : Subgroup D).prod P).map η := by
  rw [←map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩; exact ⟨rfl,ha⟩
  · rintro ⟨hx,h⟩; exact ⟨x.2,h,Prod.ext hx.symm rfl⟩

omit [Finite H] in
private theorem axis_inf_left (η : D × D →* H) (hη : Function.Injective η)
    (P Q : Subgroup D) :
    (P.prod Q).map η ⊓ ((⊤ : Subgroup D).prod ⊥).map η = (P.prod ⊥).map η := by
  rw [← Subgroup.map_inf _ _ η hη]
  congr 1
  ext x
  simp only [mem_inf,mem_prod,mem_top,mem_bot]
  constructor
  · tauto
  · rintro ⟨h,hx⟩; exact ⟨⟨h,hx ▸ Q.one_mem⟩,trivial,hx⟩

omit [Finite H] in
private theorem axis_inf_right (η : D × D →* H) (hη : Function.Injective η)
    (P Q : Subgroup D) :
    (P.prod Q).map η ⊓ ((⊥ : Subgroup D).prod ⊤).map η = ((⊥ : Subgroup D).prod Q).map η := by
  rw [← Subgroup.map_inf _ _ η hη]
  congr 1
  ext x
  simp only [mem_inf,mem_prod,mem_top,mem_bot]
  constructor
  · tauto
  · rintro ⟨hx,h⟩; exact ⟨⟨hx ▸ P.one_mem,h⟩,hx,trivial⟩

theorem not_generated_of_coordinates
    (hF : 1 < F.degree) (q : G →* H) (hq : Function.Surjective q) (T : Sylow 2 G)
    (hker : (T : Subgroup G) ⊓ q.ker = pCore 2 G) (hcore : pCore 2 H = ⊥)
    (Y : Subgroup H) [Y.Normal] (e : Y ≃* D × D) (P Q : Sylow 2 D)
    (hPQ : (T : Subgroup G).map q ⊓ Y =
      ((P : Subgroup D).prod Q).map (Y.subtype.comp e.symm.toMonoidHom))
    (hperm : ∀ g : H,
      let η := Y.subtype.comp e.symm.toMonoidHom
      let L₁ := ((⊤ : Subgroup D).prod ⊥).map η
      let L₂ := ((⊥ : Subgroup D).prod ⊤).map η
      ((L₁.map (MulAut.conj g).toMonoidHom = L₁ ∧ L₂.map (MulAut.conj g).toMonoidHom = L₂) ∨
        (L₁.map (MulAut.conj g).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj g).toMonoidHom = L₁)))
    (hlift :
      (∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ A ≤ T ∧
        A.map q = ((P : Subgroup D).prod ⊥).map (Y.subtype.comp e.symm.toMonoidHom)) ∧
      (∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ A ≤ T ∧
        A.map q = ((⊥ : Subgroup D).prod Q).map (Y.subtype.comp e.symm.toMonoidHom))) :
    ¬ IsEGenerated 1 G := by
  classical
  let η : D × D →* H := Y.subtype.comp e.symm.toMonoidHom
  have hη : Function.Injective η := Y.subtype_injective.comp e.symm.injective
  let j : Fin 2 → D →* H := ![η.comp (MonoidHom.inl D D),η.comp (MonoidHom.inr D D)]
  have hj : ∀ i, Function.Injective (j i) := by
    intro i
    fin_cases i
    · intro a b hab
      exact congrArg Prod.fst (hη hab)
    · intro a b hab
      exact congrArg Prod.snd (hη hab)
  let L : Fin 2 → Subgroup H := fun i => (j i).range
  let c (i : Fin 2) : D ≃* L i := MonoidHom.ofInjective (hj i)
  let R : Fin 2 → Sylow 2 D := ![P,Q]
  let S (i : Fin 2) : Sylow 2 (L i) := (R i).mapSurjective (f := (c i).toMonoidHom) (c i).surjective
  have hS (i : Fin 2) : (S i : Subgroup (L i)).map (L i).subtype =
      (R i : Subgroup D).map (j i) := by
    change ((R i : Subgroup D).map (c i).toMonoidHom).map (L i).subtype = _
    rw [map_map]
    rfl
  have hL₁ : L 0 = ((⊤ : Subgroup D).prod ⊥).map η := by
    change (j 0).range = _
    rw [MonoidHom.range_eq_map]
    exact axis_inl F η ⊤
  have hL₂ : L 1 = ((⊥ : Subgroup D).prod ⊤).map η := by
    change (j 1).range = _
    rw [MonoidHom.range_eq_map]
    exact axis_inr F η ⊤
  have hS₁ : (S 0 : Subgroup (L 0)).map (L 0).subtype = ((P : Subgroup D).prod ⊥).map η := by
    rw [hS]; exact axis_inl F η P
  have hS₂ : (S 1 : Subgroup (L 1)).map (L 1).subtype = ((⊥ : Subgroup D).prod Q).map η := by
    rw [hS]; exact axis_inr F η Q
  have hLY : ∀ i, L i ≤ Y := by
    intro i x hx
    obtain ⟨a,rfl⟩ := hx
    fin_cases i <;> exact (e.symm _).property
  have hinf : ∀ i, (S i : Subgroup (L i)).map (L i).subtype =
      (T : Subgroup G).map q ⊓ L i := by
    intro i
    have hh := inf_assoc ((T : Subgroup G).map q) Y (L i)
    rw [inf_of_le_right (hLY i)] at hh
    rw [←hh,hPQ]
    fin_cases i
    · change (S 0 : Subgroup (L 0)).map (L 0).subtype =
        ((P : Subgroup D).prod Q).map η ⊓ L 0
      rw [hS₁,hL₁,axis_inf_left F η hη]
    · change (S 1 : Subgroup (L 1)).map (L 1).subtype =
        ((P : Subgroup D).prod Q).map η ⊓ L 1
      rw [hS₂,hL₂,axis_inf_right F η hη]
  have hspan : (T : Subgroup G).map q ⊓ Y =
      ⨆ i, (S i : Subgroup (L i)).map (L i).subtype := by
    have hi : (⨆ i, (S i : Subgroup (L i)).map (L i).subtype) =
        (S 0 : Subgroup (L 0)).map (L 0).subtype ⊔ (S 1 : Subgroup (L 1)).map (L 1).subtype := by
      apply le_antisymm
      · apply iSup_le
        intro i
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
      · exact sup_le (le_iSup (fun i => (S i : Subgroup (L i)).map (L i).subtype) 0)
          (le_iSup (fun i => (S i : Subgroup (L i)).map (L i).subtype) 1)
    rw [hPQ,hi,hS₁,hS₂]
    rw [← Subgroup.map_sup]
    congr 1
    apply le_antisymm
    · rintro ⟨a,b⟩ ⟨ha,hb⟩
      have hx : (a,b) = (a,1) * (1,b) := by simp
      rw [hx]
      exact mul_mem (mem_sup_left ⟨ha,rfl⟩) (mem_sup_right ⟨rfl,hb⟩)
    · exact sup_le (Subgroup.prod_mono le_rfl bot_le) (Subgroup.prod_mono bot_le le_rfl)
  let : IsElementaryAbelian 2 P := (SL2NaturalOffenders.Ratios.sylow_offender P).1.2
  let : IsElementaryAbelian 2 Q := (SL2NaturalOffenders.Ratios.sylow_offender Q).1.2
  let : IsMulCommutative ((P : Subgroup D).prod (Q : Subgroup D)) := by
    apply IsMulCommutative.of_comm
    intro a b
    exact ((P : Subgroup D).prodEquiv (Q : Subgroup D)).injective (by
      rw [map_mul,map_mul,mul_comm])
  have hcomm : IsMulCommutative ((T : Subgroup G).map q ⊓ Y : Subgroup H) := by
    rw [hPQ]
    infer_instance
  have hfacts (i : Fin 2) := linear_factor_facts F hF (L i) (c i).symm (S i)
  apply ValuesEvenClassical.PairLift.not_isEGenerated_of_pair_lifts q hq T hker hcore
    Y L S hLY hinf hspan hcomm (fun i => (hfacts i).2.2.2.2) ?_
    (fun i => (hfacts i).1) (fun i => (hfacts i).2.1)
    (fun i k => (hfacts i).2.2.1.trans (hfacts k).2.2.1.symm) 1
    (fun i => (hfacts i).2.2.2.1) ?_
  · intro g i
    rcases hperm g with h | h
    · refine ⟨i,?_⟩
      fin_cases i
      · change (L 0).map (MulAut.conj g).toMonoidHom = L 0
        rw [hL₁]; exact h.1
      · change (L 1).map (MulAut.conj g).toMonoidHom = L 1
        rw [hL₂]; exact h.2
    · fin_cases i
      · refine ⟨1,?_⟩
        change (L 0).map (MulAut.conj g).toMonoidHom = L 1
        rw [hL₁,hL₂]; exact h.1
      · refine ⟨0,?_⟩
        change (L 1).map (MulAut.conj g).toMonoidHom = L 0
        rw [hL₂,hL₁]; exact h.2
  · intro i
    fin_cases i
    · change ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ A ≤ T ∧ A.map q = (S 0 : Subgroup (L 0)).map (L 0).subtype
      rw [hS₁]; exact hlift.1
    · change ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ A ≤ T ∧ A.map q = (S 1 : Subgroup (L 1)).map (L 1).subtype
      rw [hS₂]; exact hlift.2

end CFSG.Quasithin.ChapterE.ThompsonAction.PairGeneration
