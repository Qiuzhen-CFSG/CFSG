module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.Quasithin.EvenCharacteristic

/-!
# Characteristic p after adjoining an invariant p-subgroup

Suppose H normalizes the p-subgroup P. In G = HP, the product O_p(H)P
is a normal p-subgroup. The normal centralizer C of O_p(G) therefore meets H
inside O_p(H). The product-order formula shows that |H:C intersect H| and
|G:C| have the same prime-to-p part; equivalently |C| divides
|C intersect H| times |G:H|. Both factors are p-powers, so C is a p-group.
This proves characteristic p in the actual join without assuming that P
normalizes H.

Source application: Aschbacher--Smith 2.5.3(2), printed p.552.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem normal_pgroup_of_inf_of_normal_supplement
    (H P C : Subgroup G) [P.Normal] [C.Normal]
    (hgen : H ⊔ P = ⊤) (hP : IsPGroup p P)
    (hCH : IsPGroup p (C ⊓ H : Subgroup G)) : IsPGroup p C := by
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hPcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes P H
    (show H ≤ normalizer (P : Set G) from le_normalizer_of_normal)
  rw [sup_comm P H, hgen, Nat.card_congr Subgroup.topEquiv.toEquiv,
    ← H.card_mul_index] at hPcard
  have hidx : H.index ∣ Nat.card P := by
    refine ⟨Nat.card (P ⊓ H : Subgroup G), ?_⟩
    apply Nat.eq_of_mul_eq_mul_right hHpos
    calc
      Nat.card P * Nat.card H = Nat.card (P ⊓ H : Subgroup G) *
          (Nat.card H * H.index) := hPcard
      _ = H.index * Nat.card (P ⊓ H : Subgroup G) * Nat.card H := by ac_rfl
  have hCcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes C H
    (show H ≤ normalizer (C : Set G) from le_normalizer_of_normal)
  have hd : Nat.card C ∣ Nat.card (C ⊓ H : Subgroup G) * H.index := by
    apply Nat.dvd_of_mul_dvd_mul_right hHpos
    rw [hCcard]
    have hh := Nat.mul_dvd_mul_left (Nat.card (C ⊓ H : Subgroup G))
      (card_subgroup_dvd_card (C ⊔ H))
    rw [← H.card_mul_index] at hh
    convert hh using 1
    ac_rfl
  obtain ⟨a, ha⟩ := hCH.exists_card_eq
  obtain ⟨b, hb⟩ := hP.exists_card_eq
  apply IsPGroup.of_card_dvd_pow (n := a + b)
  rw [pow_add]
  exact hd.trans (Nat.mul_dvd_mul ha.dvd (hidx.trans hb.dvd))

/-- Characteristic p in a supplement to a normal p-subgroup implies
characteristic p in the whole finite group. -/
theorem centralizer_pCore_le_of_normal_pgroup_supplement
    (H P : Subgroup G) [P.Normal]
    (hgen : H ⊔ P = ⊤) (hP : IsPGroup p P)
    (hH : centralizer (pCore p H : Set H) ≤ pCore p H) :
    centralizer (pCore p G : Set G) ≤ pCore p G := by
  let R := H.pCoreIn p
  let Q := R ⊔ P
  have hHR : H ≤ normalizer (R : Set G) := by
    change H ≤ normalizer ((pCore p H).map H.subtype : Set G)
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore p H).le_normalizer_map H.subtype
  have hHQ : H ≤ normalizer (Q : Set G) :=
    hHR.trans normalizer_le_normalizer_sup_normal
  have hQnormal : Q.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le hHQ (le_sup_right.trans Q.le_normalizer)
  have hQp : IsPGroup p Q := (isPGroup_pCoreIn p H).to_sup_of_normal_right hP
  have hRcore : R ≤ pCore p G := le_sup_left.trans (le_sSup ⟨hQnormal, hQp⟩)
  let C := centralizer (pCore p G : Set G)
  have hCHR : C ⊓ H ≤ R := by
    rintro x ⟨hc, hx⟩
    have hh : (⟨x, hx⟩ : H) ∈ pCore p H := by
      apply hH
      intro y hy
      exact Subtype.ext (hc y (hRcore (mem_map_of_mem H.subtype hy)))
    exact mem_map_of_mem H.subtype hh
  have hCH : IsPGroup p (C ⊓ H : Subgroup G) :=
    (isPGroup_pCoreIn p H).to_le hCHR
  exact le_sSup ⟨inferInstance,
    normal_pgroup_of_inf_of_normal_supplement H P C hgen hP hCH⟩

/-- Adjoining an H-invariant p-subgroup preserves characteristic p in
the literal subgroup join. The direction of normalization is H to P. -/
theorem centralizer_pCore_sup_le_of_normalized_pgroup
    (H P : Subgroup G)
    (hH : centralizer (pCore p H : Set H) ≤ pCore p H)
    (hP : IsPGroup p P) (hn : H ≤ normalizer (P : Set G)) :
    centralizer (pCore p (H ⊔ P : Subgroup G) : Set (H ⊔ P : Subgroup G)) ≤
      pCore p (H ⊔ P : Subgroup G) := by
  let X := H ⊔ P
  let H' := H.subgroupOf X
  let P' := P.subgroupOf X
  let : P'.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
    (sup_le hn P.le_normalizer)
  have hgen : H' ⊔ P' = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]
  exact centralizer_pCore_le_of_normal_pgroup_supplement H' P' hgen
    hP.comap_subtype ((Theory.Quasithin.centralizer_pCore_le_iff p
      (subgroupOfEquivOfLe (show H ≤ X from le_sup_left))).mpr hH)

end Theory.GroupTheory
