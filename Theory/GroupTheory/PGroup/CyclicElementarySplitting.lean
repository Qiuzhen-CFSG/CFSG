module

public import Theory.GroupTheory.PGroup.AbelianOmega

/-!
# Splitting over a cyclic subgroup of an abelian two-group

Let `H` be a finite abelian two-group and `Z` a nontrivial cyclic subgroup
with elementary abelian quotient. There is a subgroup `B` disjoint from `Z`
with cyclic quotient, such that `B ⊔ Z` is characteristic and `Z` is maximal
cyclic in that join. No characteristicity assumption on `Z` is needed.

Choose a vector-space complement to `Z ∩ Ω₁(H)` in `Ω₁(H)`. In the quotient
by this complement, every involution lifts to an involution, since its square
belongs to both the complement and `Z`. The quotient omega subgroup is
therefore cyclic, and the abelian two-group criterion makes the quotient cyclic.
The join is `Ω₁(H)Z`, the inverse image under squaring of the squares of `Z`.
Those squares are characteristic in the cyclic square subgroup of `H`, hence
characteristic in `H`. Finally, the join has exponent dividing `|Z|`, which
makes `Z` maximal cyclic inside it.

This is the abelian splitting used in Gorenstein, *Finite Groups*, Lemma 5.4.7,
pp. 196–197. The source uses maximal-order cyclic splitting (Lemma 1.3.3);
the proof here instead uses the elementary abelian omega complement.
-/

open scoped IsMulCommutative
open Subgroup

/-- All subgroups of a cyclic group are characteristic. -/
private theorem cyclic_characteristic {G : Type*} [Group G] [IsCyclic G]
    (K : Subgroup G) : K.Characteristic := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  obtain ⟨n, rfl⟩ := (Subgroup.le_zpowers_iff g K).mp (by rw [hg]; exact le_top)
  apply Subgroup.characteristic_iff_map_le.mpr
  intro φ
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_le, map_pow]
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ▸ Subgroup.mem_top (φ g))
  change (φ g) ^ n ∈ Subgroup.zpowers (g ^ n)
  rw [← hi]
  have he : (g ^ i) ^ n = (g ^ n) ^ i := by
    rw [← zpow_natCast (g ^ i), ← zpow_mul, mul_comm i, zpow_mul, zpow_natCast]
  rw [he]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _

private theorem omega_eq_square_ker {G : Type*} [CommGroup G] :
    omega₁ G (p := 2) = (powMonoidHom 2).ker := by
  have : IsElementaryAbelian 2 (omega₁ G (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative G
  apply le_antisymm
  · intro x hx
    exact elemPow_eq_one_of_isElementaryAbelian x hx
      (p := 2) (A := omega₁ G (p := 2))
  · intro x hx
    exact Subgroup.subset_closure (by simpa [omega, omega₁] using hx)

private theorem square_range_characteristic {G : Type*} [CommGroup G] :
    (powMonoidHom (α := G) 2).range.Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro φ x hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨φ y, by simp⟩

private theorem omega_join_characteristic {G : Type*} [CommGroup G]
    (Z : Subgroup G) [IsCyclic Z]
    (hsq : (powMonoidHom (α := G) 2).range ≤ Z) :
    (omega₁ G (p := 2) ⊔ Z).Characteristic := by
  let s : G →* G := powMonoidHom 2
  let R := s.range
  let D := Z.map s
  have : IsCyclic R := Subgroup.isCyclic_of_le hsq
  have : R.Characteristic := square_range_characteristic
  have hDR : D ≤ R := Subgroup.map_le_range s Z
  have : (D.subgroupOf R).Characteristic := cyclic_characteristic _
  have hD : D.Characteristic := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hDR]
    infer_instance
  have hpre : omega₁ G (p := 2) ⊔ Z = D.comap s := by
    rw [omega_eq_square_ker, Subgroup.comap_map_eq, sup_comm]
  rw [hpre]
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro φ x hx
  change (φ x) ^ 2 ∈ D
  rw [← map_pow]
  exact Subgroup.characteristic_iff_le_comap.mp hD φ hx

private theorem exists_omega_complement {G : Type*} [CommGroup G]
    (Z : Subgroup G) : ∃ B : Subgroup G,
      B ≤ omega₁ G (p := 2) ∧ Disjoint B Z ∧
      omega₁ G (p := 2) ≤ B ⊔ Z := by
  let E := omega₁ G (p := 2)
  have : IsElementaryAbelian 2 E := IsElementaryAbelian.omega₁_of_isMulCommutative G
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl 2 E (Z.subgroupOf E)
  let B := C.map E.subtype
  refine ⟨B, Subgroup.map_subtype_le _, ?_, ?_⟩
  · apply Subgroup.disjoint_def.mpr
    rintro x ⟨y, hy, rfl⟩ hxZ
    have hyZ : y ∈ Z.subgroupOf E := hxZ
    exact congrArg Subtype.val (Subgroup.disjoint_def.mp hC.disjoint hyZ hy)
  · intro x hx
    have ht : (⟨x, hx⟩ : E) ∈ Z.subgroupOf E ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨z, hz, c, hc, he⟩ := Subgroup.mem_sup.mp ht
    have he' : (z : G) * (c : G) = x := congrArg Subtype.val he
    rw [← he']
    exact (B ⊔ Z).mul_mem (Subgroup.mem_sup_right hz)
      (Subgroup.mem_sup_left (Subgroup.mem_map_of_mem E.subtype hc))

private theorem cyclic_quotient_of_omega_complement {G : Type*} [CommGroup G] [Finite G]
    (hG : IsPGroup 2 G) (Z B : Subgroup G) [IsCyclic Z]
    (hsq : (powMonoidHom (α := G) 2).range ≤ Z)
    (hdis : Disjoint B Z) (hgen : omega₁ G (p := 2) ≤ B ⊔ Z) :
    IsCyclic (G ⧸ B) := by
  let q := QuotientGroup.mk' B
  have hle : omega₁ (G ⧸ B) (p := 2) ≤ Z.map q := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective B y
    have hxB : x ^ 2 ∈ B := by
      apply (QuotientGroup.eq_one_iff (N := B) (x ^ 2)).mp
      change q (x ^ 2) = 1
      rw [map_pow]
      exact (show q x ∈ (powMonoidHom 2).ker from omega_eq_square_ker (G := G ⧸ B) ▸ hy)
    have hxZ : x ^ 2 ∈ Z := hsq ⟨x, rfl⟩
    have hxE : x ∈ omega₁ G (p := 2) := by
      rw [omega_eq_square_ker]
      exact Subgroup.disjoint_def.mp hdis hxB hxZ
    have hx : x ∈ Z ⊔ q.ker := by
      simpa [q, sup_comm] using hgen hxE
    change x ∈ (Z.map q).comap q
    rwa [Subgroup.comap_map_eq]
  have : IsCyclic (Z.map q) :=
    isCyclic_of_surjective (q.subgroupMap Z) (MonoidHom.subgroupMap_surjective q Z)
  have : IsCyclic (omega₁ (G ⧸ B) (p := 2)) := Subgroup.isCyclic_of_le hle
  have : IsElementaryAbelian 2 (omega₁ (G ⧸ B) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  apply (hG.to_quotient B).isCyclic_of_card_omega_one_le_two
  apply Nat.le_of_dvd (by decide : 0 < 2)
  rw [← IsCyclic.exponent_eq_card]
  exact IsElementaryAbelian.exponent_dvd_p 2 _

private theorem cyclic_maximal_in_omega_join {G : Type*} [CommGroup G] [Finite G]
    (hG : IsPGroup 2 G) (Z : Subgroup G) (hZne : Z ≠ ⊥)
    (K : Subgroup G) (hZK : Z ≤ K) (hKE : K ≤ omega₁ G (p := 2) ⊔ Z)
    [IsCyclic K] : K = Z := by
  have hn : 2 ∣ Nat.card Z := ((hG.to_subgroup Z).card_eq_or_dvd).resolve_left
    (fun h => hZne (Z.eq_bot_of_card_eq h))
  have hpow : ∀ x : K, x ^ Nat.card Z = 1 := by
    intro x
    apply Subtype.ext
    obtain ⟨e, he, z, hz, hez⟩ := Subgroup.mem_sup.mp (hKE x.property)
    change (x : G) ^ Nat.card Z = 1
    rw [← hez, mul_pow]
    have he2 : e ^ 2 = 1 := by
      exact (show e ∈ (powMonoidHom 2).ker from omega_eq_square_ker (G := G) ▸ he)
    have heN : e ^ Nat.card Z = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one he2).trans hn)
    have hzN : z ^ Nat.card Z = 1 := by
      exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hz⟩ : Z)))
    rw [heN, hzN, one_mul]
  have hcard : Nat.card K ∣ Nat.card Z := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
  exact (Subgroup.eq_of_le_of_card_ge hZK (Nat.le_of_dvd Nat.card_pos hcard)).symm

/-- Split a finite abelian two-group over a nontrivial cyclic subgroup with
an elementary abelian quotient. The resulting join is characteristic, and
contains no cyclic subgroup properly containing the original subgroup. -/
public theorem IsPGroup.exists_cyclic_elementary_splitting {H : Type*} [CommGroup H] [Finite H]
    (hH : IsPGroup 2 H) (Z : Subgroup H) (hZcyc : IsCyclic Z) (hZne : Z ≠ ⊥)
    (hquot : IsElementaryAbelian 2 (H ⧸ Z)) :
    ∃ B : Subgroup H, IsCyclic (H ⧸ B) ∧ Disjoint B Z ∧
      (B ⊔ Z).Characteristic ∧ ∀ K : Subgroup H,
      Z ≤ K → K ≤ B ⊔ Z → IsCyclic K → K = Z := by
  have := hZcyc
  have hsq : (powMonoidHom (α := H) 2).range ≤ Z := by
    rintro x ⟨y, rfl⟩
    simp only [powMonoidHom_apply]
    apply (QuotientGroup.eq_one_iff (N := Z) (y ^ 2)).mp
    change (QuotientGroup.mk' Z) (y ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hquot.exponent_dvd_p _
  obtain ⟨B, hBE, hdis, hgen⟩ := exists_omega_complement Z
  have hjoin : B ⊔ Z = omega₁ H (p := 2) ⊔ Z :=
    le_antisymm (sup_le_sup_right hBE _) (sup_le hgen le_sup_right)
  refine ⟨B, cyclic_quotient_of_omega_complement hH Z B hsq hdis hgen, hdis, ?_, ?_⟩
  · rw [hjoin]
    exact omega_join_characteristic Z hsq
  · intro K hZK hKB hK
    exact cyclic_maximal_in_omega_join hH Z hZne K hZK (hjoin ▸ hKB)
