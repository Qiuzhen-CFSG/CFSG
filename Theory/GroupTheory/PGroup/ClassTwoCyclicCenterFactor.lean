module

public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.PGroup.CyclicElementarySplitting
public import Theory.GroupTheory.PGroup.ExtraspecialCentralizer
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Lifting an abelianization splitting to an extraspecial factor

An abelian group has the trivial subgroup as a supplement to its center.
A nonabelian group with elementary binary central quotient and center of
order two is itself extraspecial. These dispose of the two initial cases
of the internal factor extraction. In the remaining case, a splitting of the
abelianization lifts to an extraspecial supplement: the characteristic join
has cyclic center, and maximal cyclicity of the center image identifies the
lift's center with the derived subgroup. The extraspecial centralizer argument
then proves generation with the ambient center. Applying the finite abelian
two-group splitting theorem completes the internal factor extraction.

Source: Gorenstein, *Finite Groups*, Lemma 5.4.7, pp. 196–197.
-/

open Subgroup
open scoped IsMulCommutative

namespace IsPGroup

/-- The abelian case of internal factor extraction. -/
public theorem exists_extraspecial_center_supplement_of_center_eq_top
    {Q : Type*} [Group Q] (hcenter : center Q = ⊤) :
    ∃ F : Subgroup Q, (F = ⊥ ∨ IsExtraspecial 2 F) ∧ F ⊔ center Q = ⊤ := by
  exact ⟨⊥, Or.inl rfl, by simpa using hcenter⟩

/-- A group with elementary binary central quotient and center of order two
has an extraspecial or trivial supplement to the center. -/
public theorem exists_extraspecial_center_supplement_of_center_card_two
    {Q : Type*} [Group Q]
    (hquot : IsElementaryAbelian 2 (Q ⧸ center Q))
    (hcenter : Nat.card (center Q) = 2) :
    ∃ F : Subgroup Q, (F = ⊥ ∨ IsExtraspecial 2 F) ∧ F ⊔ center Q = ⊤ := by
  by_cases hab : center Q = ⊤
  · exact exists_extraspecial_center_supplement_of_center_eq_top hab
  have hspecial : IsExtraspecial 2 Q := {
    center_order_p := hcenter
    quotient_elementary_abelian := hquot
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr hab }
  exact ⟨⊤, Or.inr (hspecial.of_mulEquiv (Subgroup.topEquiv (G := Q)).symm),
    top_sup_eq _⟩

/-- Hall's characteristic-abelian hypothesis makes the center cyclic and,
in the nonabelian case, forces the derived subgroup to have order two. -/
public theorem cyclic_center_and_card_commutator_two
    {Q : Type*} [Group Q] [Finite Q]
    (hquot : IsElementaryAbelian 2 (Q ⧸ center Q))
    (hchar : ∀ A : Subgroup Q, A.Characteristic → IsMulCommutative A → IsCyclic A)
    (hnonab : center Q ≠ ⊤) :
    IsCyclic (center Q) ∧ Nat.card (_root_.commutator Q) = 2 := by
  have hcyc := hchar (center Q) inferInstance inferInstance
  let _ := hcyc
  exact ⟨hcyc, hquot.card_commutator_eq_two_of_cyclic_center hnonab⟩

/-- The final internal assembly only needs an extraspecial normal subgroup
with cyclic quotient whose center is central in the ambient group. -/
public theorem center_supplement_of_extraspecial_cyclic_quotient
    {Q : Type*} [Group Q] [Finite Q]
    (hquot : IsElementaryAbelian 2 (Q ⧸ center Q))
    (hchar : ∀ A : Subgroup Q, A.Characteristic → IsMulCommutative A → IsCyclic A)
    (F : Subgroup Q) [F.Normal] [IsExtraspecial 2 F] [IsCyclic (Q ⧸ F)]
    (hFcenter : (center F).map F.subtype ≤ center Q) :
    F ⊔ center Q = ⊤ := by
  let : IsCyclic (center Q) := hchar (center Q) inferInstance inferInstance
  apply sup_center_eq_top_of_extraspecial_two_of_cyclic_quotient F
  apply commutator_le_center_image_of_extraspecial_two F (center Q) hFcenter
    (center_le_centralizer _) ?_
  exact (commutator_mono le_rfl le_top).trans
    hquot.commutator_le_center_of_central_quotient

private theorem extraspecial_of_center_image_eq_commutator
    {Q : Type*} [Group Q] [Finite Q] [IsCyclic (center Q)]
    (hquot : IsElementaryAbelian 2 (Q ⧸ center Q))
    (hnonab : center Q ≠ ⊤)
    (F : Subgroup Q) [F.Normal] [IsCyclic (Q ⧸ F)]
    (hcenter : (center F).map F.subtype = _root_.commutator Q) :
    IsExtraspecial 2 F := by
  refine {
    center_order_p := ?_
    quotient_elementary_abelian := hquot.central_quotient_subgroup F
    quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr ?_ }
  · calc
      Nat.card (center F) = Nat.card ((center F).map F.subtype) :=
        (card_map_of_injective F.subtype_injective).symm
      _ = 2 := hcenter ▸ hquot.card_commutator_eq_two_of_cyclic_center hnonab
  · intro hab
    have hFZ : F ≤ center Q := by
      intro x hx
      apply hquot.commutator_le_center_of_central_quotient
      rw [← hcenter]
      exact mem_map_of_mem F.subtype (hab ▸ mem_top (⟨x, hx⟩ : F))
    apply hnonab
    apply center_eq_top_iff.mpr
    apply (QuotientGroup.mk' F).isMulCommutative_of_isCyclic_of_ker_le_center
    simpa only [QuotientGroup.ker_mk'] using hFZ

private theorem center_image_le_of_characteristic_join
    {Q : Type*} [Group Q]
    (hchar : ∀ A : Subgroup Q, A.Characteristic → IsMulCommutative A → IsCyclic A)
    (F : Subgroup Q) [(F ⊔ center Q).Characteristic]
    (hmax : ∀ K : Subgroup Q, center Q ≤ K → K ≤ F ⊔ center Q →
      IsCyclic K → K = center Q) :
    (center F).map F.subtype ≤ center Q := by
  let D := F ⊔ center Q
  let K := (center D).map D.subtype
  have hZK : center Q ≤ K := by
    intro z hz
    refine ⟨⟨z, (le_sup_right : center Q ≤ D) hz⟩, ?_, rfl⟩
    exact mem_center_iff.mpr fun d => Subtype.ext (mem_center_iff.mp hz d)
  have hK : K = center Q := hmax K hZK (map_subtype_le _)
    (hchar K inferInstance inferInstance)
  rw [← hK]
  rintro x ⟨f, hf, rfl⟩
  refine ⟨⟨(f : Q), (le_sup_left : F ≤ D) f.property⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro d
  apply Subtype.ext
  have hfC : (f : Q) ∈ centralizer (F : Set Q) := by
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hf (⟨y, hy⟩ : F))
  have hfZ : (f : Q) ∈ centralizer (center Q : Set Q) := by
    intro z hz
    exact (mem_center_iff.mp hz (f : Q)).symm
  have hD : D ≤ centralizer ({(f : Q)} : Set Q) := by
    apply sup_le
    · intro y hy z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact (hfC y hy).symm
    · intro y hy z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact (hfZ y hy).symm
  exact (hD d.property (f : Q) (Set.mem_singleton _)).symm

private theorem extraspecial_center_supplement_of_characteristic_join
    {Q : Type*} [Group Q] [Finite Q]
    (hquot : IsElementaryAbelian 2 (Q ⧸ center Q))
    (hchar : ∀ A : Subgroup Q, A.Characteristic → IsMulCommutative A → IsCyclic A)
    (hnonab : center Q ≠ ⊤)
    (F : Subgroup Q) [F.Normal] [IsCyclic (Q ⧸ F)]
    [(F ⊔ center Q).Characteristic]
    (hFZ : F ⊓ center Q = _root_.commutator Q)
    (hmax : ∀ K : Subgroup Q, center Q ≤ K → K ≤ F ⊔ center Q →
      IsCyclic K → K = center Q) :
    IsExtraspecial 2 F ∧ F ⊔ center Q = ⊤ := by
  let : IsCyclic (center Q) := hchar (center Q) inferInstance inferInstance
  have hFcenter := center_image_le_of_characteristic_join hchar F hmax
  have hcenter : (center F).map F.subtype = _root_.commutator Q := by
    rw [← hFZ]
    apply le_antisymm (le_inf (map_subtype_le _) hFcenter)
    intro x hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    exact mem_center_iff.mpr fun f => Subtype.ext (mem_center_iff.mp hx.2 f)
  let hspecial : IsExtraspecial 2 F :=
    extraspecial_of_center_image_eq_commutator hquot hnonab F hcenter
  exact ⟨hspecial, IsPGroup.center_supplement_of_extraspecial_cyclic_quotient
    hquot hchar F hFcenter⟩

/-- An abelianization splitting with characteristic join and maximal cyclic
center image lifts to an extraspecial supplement of the ambient center. -/
public theorem center_supplement_of_abelianization_split
    {Q : Type*} [Group Q] [Finite Q]
    (hquot : IsElementaryAbelian 2 (Q ⧸ center Q))
    (hchar : ∀ A : Subgroup Q, A.Characteristic → IsMulCommutative A → IsCyclic A)
    (hnonab : center Q ≠ ⊤)
    (B : Subgroup (Q ⧸ _root_.commutator Q)) [B.Normal]
    [IsCyclic ((Q ⧸ _root_.commutator Q) ⧸ B)]
    (hdisj : Disjoint B ((center Q).map (QuotientGroup.mk' (_root_.commutator Q))))
    (hDchar : (B ⊔ (center Q).map
      (QuotientGroup.mk' (_root_.commutator Q))).Characteristic)
    (hmax : ∀ K : Subgroup (Q ⧸ _root_.commutator Q),
      (center Q).map (QuotientGroup.mk' (_root_.commutator Q)) ≤ K →
      K ≤ B ⊔ (center Q).map (QuotientGroup.mk' (_root_.commutator Q)) →
      IsCyclic K → K = (center Q).map (QuotientGroup.mk' (_root_.commutator Q))) :
    ∃ F : Subgroup Q, IsExtraspecial 2 F ∧ F ⊔ center Q = ⊤ := by
  let q := QuotientGroup.mk' (_root_.commutator Q)
  let F := B.comap q
  have hker : q.ker ≤ center Q := by
    simpa only [q, QuotientGroup.ker_mk'] using
      hquot.commutator_le_center_of_central_quotient
  have hZF : ((center Q).map q).comap q = center Q :=
    comap_map_eq_self hker
  have hD : F ⊔ center Q = (B ⊔ (center Q).map q).comap q := by
    rw [← comap_sup_eq q _ _ (QuotientGroup.mk'_surjective _), hZF]
  let : (F ⊔ center Q).Characteristic := by
    rw [hD]
    exact Subgroup.Characteristic.comap_quotient_mk hDchar
  have hFker : _root_.commutator Q ≤ F := by
    simpa only [q, QuotientGroup.ker_mk'] using ker_le_comap q B
  have hFB : F.map q = B :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) B
  let : IsCyclic (Q ⧸ F) := by
    let eB := QuotientGroup.quotientMulEquivOfEq hFB
    let : IsCyclic ((Q ⧸ _root_.commutator Q) ⧸ F.map q) :=
      isCyclic_of_surjective eB.symm eB.symm.surjective
    let e := QuotientGroup.quotientQuotientEquivQuotient (_root_.commutator Q) F hFker
    exact isCyclic_of_surjective e e.surjective
  have hFZ : F ⊓ center Q = _root_.commutator Q := by
    apply le_antisymm
    · intro x hx
      apply (QuotientGroup.eq_one_iff _).mp
      have hm : q x ∈ B ⊓ (center Q).map q := ⟨hx.1, mem_map_of_mem q hx.2⟩
      rw [disjoint_iff.mp hdisj] at hm
      exact hm
    · exact le_inf hFker hquot.commutator_le_center_of_central_quotient
  have hmaxF : ∀ K : Subgroup Q, center Q ≤ K → K ≤ F ⊔ center Q →
      IsCyclic K → K = center Q := by
    intro K hZK hKD hKcyc
    let := hKcyc
    have hmapK : K.map q = (center Q).map q :=
      hmax (K.map q) (map_mono hZK) (by
        rw [← hFB, ← Subgroup.map_sup]
        exact map_mono hKD)
        (isCyclic_of_surjective (q.subgroupMap K) (MonoidHom.subgroupMap_surjective q K))
    calc
      K = (K.map q).comap q := (comap_map_eq_self (hker.trans hZK)).symm
      _ = center Q := hmapK ▸ hZF
  exact ⟨F, extraspecial_center_supplement_of_characteristic_join
    hquot hchar hnonab F hFZ hmaxF⟩

/-- A finite two-group with elementary abelian central quotient and cyclic
characteristic abelian subgroups is generated by its center and an extraspecial
subgroup (or the trivial subgroup in the abelian case).

This is the internal case of Gorenstein, *Finite Groups*, Lemma 5.4.7. -/
public theorem exists_extraspecial_center_supplement
    {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q)
    (hquot : IsElementaryAbelian 2 (Q ⧸ center Q))
    (hchar : ∀ A : Subgroup Q, A.Characteristic → IsMulCommutative A → IsCyclic A) :
    ∃ F : Subgroup Q, (F = ⊥ ∨ IsExtraspecial 2 F) ∧ F ⊔ center Q = ⊤ := by
  by_cases hab : center Q = ⊤
  · exact exists_extraspecial_center_supplement_of_center_eq_top hab
  by_cases hcenter : Nat.card (center Q) = 2
  · exact exists_extraspecial_center_supplement_of_center_card_two hquot hcenter
  let : IsCyclic (center Q) := hchar (center Q) inferInstance inferInstance
  let : IsMulCommutative (Q ⧸ _root_.commutator Q) :=
    Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  let q := QuotientGroup.mk' (_root_.commutator Q)
  obtain ⟨B, hBcyc, hdisj, hDchar, hmax⟩ :=
    (hQ.to_quotient (_root_.commutator Q)).exists_cyclic_elementary_splitting
      ((center Q).map q)
      (isCyclic_of_surjective (q.subgroupMap (center Q))
        (MonoidHom.subgroupMap_surjective q (center Q)))
      (hquot.center_image_abelianization_ne_bot hab hcenter)
      hquot.abelianization_quotient_center_image
  let := hBcyc
  obtain ⟨F, hF, hFZ⟩ := center_supplement_of_abelianization_split
    hquot hchar hab B hdisj hDchar hmax
  exact ⟨F, Or.inr hF, hFZ⟩

end IsPGroup
