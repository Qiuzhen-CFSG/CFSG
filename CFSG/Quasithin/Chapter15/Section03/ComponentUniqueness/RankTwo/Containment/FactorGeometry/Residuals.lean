module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.Reductions
public import Theory.Quasithin.EvenCharacteristic
public import Mathlib.Data.Nat.Factorization.Basic
/-!
# Residual factors in the two-component argument

Conjugation carries the literal two-residual of an intersection or centralizer
to the corresponding residual of its images. This proves the required relative
normality and invariance. In a disjoint commuting product with centerless first
factor, its centralizer inside the product is the second factor. Thus the
15.3.12(2) splitting becomes the product of the two conjugate residuals.

Restricting the map to the order-nine two-core quotient constructs a normal
two-subgroup of the component residual. Its quotient has order three by the
three-part assertion in 15.3.12(2), and hence is simple.

The source application must still establish simplicity of the component and
the plane actors. No assertion of 15.3.39 or 15.3.40 is made here.
Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.12(2), 15.3.39--40, printed pp.1125 and 1137--1138.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G]

theorem componentFactor_le_left (Y L : Subgroup G) : componentFactor Y L ≤ Y :=
  (map_subtype_le _).trans inf_le_left

theorem centralizingFactor_le_left (Y L : Subgroup G) : centralizingFactor Y L ≤ Y :=
  (map_subtype_le _).trans inf_le_left

theorem componentFactor_map [Finite G] (Y L : Subgroup G) (e : G ≃* G) :
    (componentFactor Y L).map e.toMonoidHom =
      componentFactor (Y.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  unfold componentFactor
  rw [map_twoResidualAmbient_of_subgroup_image _ _ _ rfl, map_inf _ _ _ e.injective]

theorem centralizingFactor_map [Finite G] (Y L : Subgroup G) (e : G ≃* G) :
    (centralizingFactor Y L).map e.toMonoidHom =
      centralizingFactor (Y.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  unfold centralizingFactor
  rw [map_twoResidualAmbient_of_subgroup_image _ _ _ rfl, map_inf _ _ _ e.injective,
    Theory.Quasithin.map_centralizer]

theorem normalizes_componentFactor [Finite G] {Y L A : Subgroup G}
    (hY : A ≤ normalizer (Y : Set G)) (hL : A ≤ normalizer (L : Set G)) :
    A ≤ normalizer (componentFactor Y L : Set G) := by
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hYm : Y.map (MulAut.conj a).toMonoidHom = Y := mem_normalizer_iff_map_conj_eq.mp (hY ha)
  have hLm : L.map (MulAut.conj a).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp (hL ha)
  have hm := componentFactor_map Y L (MulAut.conj a)
  rw [hYm, hLm] at hm
  exact hm

theorem normalizes_centralizingFactor [Finite G] {Y L A : Subgroup G}
    (hY : A ≤ normalizer (Y : Set G)) (hL : A ≤ normalizer (L : Set G)) :
    A ≤ normalizer (centralizingFactor Y L : Set G) := by
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hYm : Y.map (MulAut.conj a).toMonoidHom = Y := mem_normalizer_iff_map_conj_eq.mp (hY ha)
  have hLm : L.map (MulAut.conj a).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp (hL ha)
  have hm := centralizingFactor_map Y L (MulAut.conj a)
  rw [hYm, hLm] at hm
  exact hm

theorem centralizingFactor_normal [Finite G] {Y V : Subgroup G}
    (hV : Y ≤ normalizer (V : Set G)) :
    ((centralizingFactor Y V).subgroupOf Y).Normal :=
  normal_subgroupOf_of_le_normalizer (normalizes_centralizingFactor Y.le_normalizer hV)

theorem componentFactor_normal [Finite G] {Y L : Subgroup G}
    (hL : Y ≤ normalizer (L : Set G)) :
    ((componentFactor Y L).subgroupOf Y).Normal :=
  normal_subgroupOf_of_le_normalizer (normalizes_componentFactor Y.le_normalizer hL)

-- A pointwise factorization, derived from the multiplication equivalence.
private theorem mem_sup_iff_of_disjoint_commuting {A B : Subgroup G}
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G)) {x : G} :
    x ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  constructor
  · intro hx
    obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
    let ab := e.symm ⟨x, hx⟩
    refine ⟨ab.1, ab.1.property, ab.2, ab.2.property, ?_⟩
    exact (he ab.1 ab.2).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩))
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact (A ⊔ B).mul_mem (mem_sup_left ha) (mem_sup_right hb)

theorem inf_centralizer_eq_inf_right {Y A B : Subgroup G}
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G))
    (hZ : center A = ⊥) (hY : Y ≤ A ⊔ B) :
    Y ⊓ centralizer (A : Set G) = Y ⊓ B := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_disjoint_commuting hd hc).mp (hY hx.1)
    have hbc : b ∈ centralizer (A : Set G) := (le_centralizer_iff.mp hc) hb
    have hac : a ∈ centralizer (A : Set G) := by
      have hh := (centralizer (A : Set G)).mul_mem hx.2
        ((centralizer (A : Set G)).inv_mem hbc)
      simpa only [← hab, mul_inv_cancel_right] using hh
    have haz : (⟨a, ha⟩ : A) ∈ center A := by
      rw [mem_center_iff]
      intro c
      exact Subtype.ext (hac c c.property)
    have ha1A : (⟨a, ha⟩ : A) = 1 := (show (⟨a, ha⟩ : A) ∈ (⊥ : Subgroup A) from hZ ▸ haz)
    have ha1 : a = 1 := congrArg Subtype.val ha1A
    have hxb : x = b := by simpa only [ha1, one_mul] using hab.symm
    exact ⟨hx.1, hxb ▸ hb⟩
  · exact inf_le_inf_left _ (le_centralizer_iff.mp hc)

theorem centralizingFactor_eq_other_componentFactor {Y A B : Subgroup G}
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G))
    (hZ : center A = ⊥) (hY : Y ≤ A ⊔ B) :
    centralizingFactor Y A = componentFactor Y B := by
  unfold centralizingFactor componentFactor
  rw [inf_centralizer_eq_inf_right hd hc hZ hY]

theorem conjugate_residual_factorization [Finite G] {Y L : Subgroup G} (s : G)
    (hd : Disjoint L (L.map (MulAut.conj s).toMonoidHom))
    (hc : L ≤ centralizer (L.map (MulAut.conj s).toMonoidHom : Set G))
    (hZ : center L = ⊥)
    (hY : Y ≤ L ⊔ L.map (MulAut.conj s).toMonoidHom)
    (hYs : s ∈ normalizer (Y : Set G))
    (hsplit : Y = componentFactor Y L ⊔ centralizingFactor Y L) :
    Y = componentFactor Y L ⊔ (componentFactor Y L).map (MulAut.conj s).toMonoidHom := by
  have hmap := componentFactor_map Y L (MulAut.conj s)
  have hYm : Y.map (MulAut.conj s).toMonoidHom = Y := mem_normalizer_iff_map_conj_eq.mp hYs
  rw [hYm] at hmap
  rw [hmap, ← centralizingFactor_eq_other_componentFactor hd hc hZ hY]
  exact hsplit


private theorem exists_normal_two_subgroup_simple_quotient [Finite G]
    {Y X : Subgroup G} (hXY : X ≤ Y)
    (hthree : 3 ^ (Nat.card X).factorization 3 = 3)
    (hquot : Nat.card (Y ⧸ pCore 2 Y) = 9) :
    ∃ (Q : Subgroup X) (hQn : Q.Normal),
      letI := hQn; IsPGroup 2 Q ∧ IsSimpleGroup (X ⧸ Q) := by
  let f : X →* Y ⧸ pCore 2 Y :=
    (QuotientGroup.mk' (pCore 2 Y)).comp (inclusion hXY)
  have hker : f.ker = (pCore 2 Y).comap (inclusion hXY) := by
    change ((QuotientGroup.mk' (pCore 2 Y)).comp (inclusion hXY)).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hQ : IsPGroup 2 f.ker := by
    rw [hker]
    exact (pCore_isPGroup (p := 2) (G := Y)).comap_of_injective
      (inclusion hXY) (inclusion_injective hXY)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hd : Nat.card f.range ∣ 3 ^ 2 := by
    change Nat.card f.range ∣ 9
    rw [← hquot]
    exact f.range.card_subgroup_dvd_card
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have hcard : Nat.card X = 2 ^ n * 3 ^ k := by
    rw [← f.ker.card_mul_index, index_ker, hn, hk]
  have hf : (Nat.card X).factorization 3 = k := by
    rw [hcard, Nat.factorization_mul (pow_ne_zero n (by decide))
      (pow_ne_zero k (by decide))]
    simp [Nat.factorization_pow, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2),
      Nat.Prime.factorization_self Nat.prime_three]
  have hk1 : k = 1 := by
    apply Nat.pow_right_injective (by decide : 1 < 3)
    simpa only [hf, pow_one] using hthree
  have hqr : Nat.card (X ⧸ f.ker) = 3 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hk, hk1, pow_one]
  exact ⟨f.ker, inferInstance, hQ, isSimpleGroup_of_prime_card hqr⟩

/-- The normal two-subgroup needed for the projection argument is the kernel
of the component factor's map into the actual order-nine two-core quotient. -/
theorem exists_componentFactor_simple_quotient [Finite G] (Y L : Subgroup G)
    (hthree : 3 ^ (Nat.card (componentFactor Y L)).factorization 3 = 3)
    (hquot : Nat.card (Y ⧸ pCore 2 Y) = 9) :
    ∃ (Q : Subgroup (componentFactor Y L)) (hQn : Q.Normal),
      letI := hQn; IsPGroup 2 Q ∧ IsSimpleGroup ((componentFactor Y L) ⧸ Q) :=
  exists_normal_two_subgroup_simple_quotient (componentFactor_le_left Y L) hthree hquot

end CFSG.Quasithin.Chapter15.Section03.RankTwo
