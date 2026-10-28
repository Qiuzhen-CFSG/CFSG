module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Placement
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.QuotientSeed
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The whole inner Hall--Janko overlap

A checked word of order three normalizes the fixed Sylow subgroup and
centralizes the first involution. Their product B has order 384. The
characteristic radical places N(s) in p₂. If the permitted quotient
p₂/q₂ is S₃ × C₃, then B has prime index three in p₂. Two checked
nonmembership witnesses therefore identify both N(s) and l₁ ∩ p₂ with B.
The Frattini argument gives l₂B = p₂ using the relative normal closure
that defines l₂. A retained path word recovers the original generator b
from l₁ and p₂, proving generation in the actual degree-100 carrier.

Source: Aschbacher--Smith F.1.1, F.1.3 and F.1.12(I)(10), pp.259--263;
retained ATLAS J2G1-p100B0 tables. The new path words and their discovery
script are retained in source/. All permutation claims are kernel checked.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap
open Theory.GroupTheory GeneratorPair Seed PairNormalizer
open PairNormalizer.SylowData PairNormalizer.QuotientData
open GeneratorPair.SecondOrbitCertificate
open scoped Pointwise


def B : Subgroup Carrier := s ⊔ Subgroup.zpowers (oddGenerator 1)

private theorem z_inclusion : inclusion z = FirstFusion.tPerm := FirstFusion.inclusion_t

private def vConjIndex : Fin 7 → Fin 128 := ![20, 30, 15, 117, 42, 88, 6]

set_option maxRecDepth 100000 in
private theorem v_conj_check : ∀ i,
    oddTable 1 * sGenTable i * (oddTable 1)⁻¹ = sTable (vConjIndex i) := by
  apply allFin
  decide +kernel

set_option maxRecDepth 2000 in
private theorem v_conj_sGenerator (j : Fin 7) :
    oddGenerator 1 * sGenerator j * (oddGenerator 1)⁻¹ = sElement (vConjIndex j) := by
  apply inclusion_injective
  rw [map_mul, map_mul, map_inv, oddGenerator_inclusion, sGenerator_inclusion,
    sElement_inclusion]
  exact v_conj_check j

private theorem normalizes_closure {G : Type*} [Group G] [Finite G]
    {n : ℕ} (g : G) (f : Fin n → G)
    (h : ∀ i, g * f i * g⁻¹ ∈ Subgroup.closure (Set.range f)) :
    g ∈ Subgroup.normalizer (Subgroup.closure (Set.range f) : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hle : (Subgroup.closure (Set.range f)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure (Set.range f) := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    exact h j
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm)

theorem v_normalizes_s : oddGenerator 1 ∈ Subgroup.normalizer (s : Set Carrier) := by
  apply normalizes_closure
  intro j
  rw [v_conj_sGenerator]
  exact sElement_mem _

set_option maxRecDepth 100000 in
theorem v_order : orderOf (oddGenerator 1) = 3 := by
  apply orderOf_eq_prime
  · apply inclusion_injective
    rw [map_pow, map_one, oddGenerator_inclusion]
    decide +kernel
  · intro h
    have hh := congrArg inclusion h
    rw [oddGenerator_inclusion, map_one] at hh
    exact (by decide +kernel : oddTable 1 ≠ 1) hh

theorem card_B : Nat.card B = 384 := by
  have hc : Nat.card (Subgroup.zpowers (oddGenerator 1)) = 3 := by
    rw [Nat.card_zpowers, v_order]
  rw [B, Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (Subgroup.zpowers_le.mpr v_normalizes_s)
    (Subgroup.disjoint_of_coprime_natCard (by rw [card_s, hc]; decide)), card_s, hc]

theorem B_le_p₂ : B ≤ p₂ := sup_le s_le_p₂ (Subgroup.zpowers_le.mpr (oddGenerator_mem_p₂ 1))

theorem B_le_normalizer : B ≤ Subgroup.normalizer (s : Set Carrier) :=
  sup_le s.le_normalizer (Subgroup.zpowers_le.mpr v_normalizes_s)

set_option maxRecDepth 100000 in
theorem B_le_l₁ : B ≤ l₁ := by
  apply sup_le s_le_l₁
  apply Subgroup.zpowers_le.mpr
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply inclusion_injective
  rw [map_mul, map_mul, oddGenerator_inclusion, z_inclusion]
  decide +kernel

set_option maxRecDepth 100000 in
theorem u_not_mem_l₁ : oddGenerator 0 ∉ l₁ := by
  intro h
  have hh := congrArg inclusion (Subgroup.mem_centralizer_singleton_iff.mp h)
  rw [map_mul, map_mul, oddGenerator_inclusion, z_inclusion] at hh
  exact (by decide +kernel : oddTable 0 * FirstFusion.tPerm ≠
    FirstFusion.tPerm * oddTable 0) hh

set_option maxRecDepth 100000 in
private theorem u_bad_check : ∀ i : Fin 128,
    (oddTable 0 * sGenTable 3 * (oddTable 0)⁻¹) ≠ sTable i := by
  apply allFin
  decide +kernel

theorem u_not_normalizes_s : oddGenerator 0 ∉ Subgroup.normalizer (s : Set Carrier) := by
  intro h
  have hh := ((Subgroup.mem_normalizer_iff.mp h) (sGenerator 3)).mp
    (Subgroup.subset_closure ⟨3, rfl⟩)
  obtain ⟨i, hi⟩ := exists_sElement hh
  have he := congrArg inclusion hi
  rw [sElement_inclusion, map_mul, map_mul, map_inv, oddGenerator_inclusion,
    sGenerator_inclusion] at he
  exact u_bad_check i he.symm

theorem normalizer_s_le_p₂ : Subgroup.normalizer (s : Set Carrier) ≤ p₂ := by
  let : (q₂.subgroupOf s).Characteristic := q₂_characteristic
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg x hx
  let f := s.normalizerMonoidHom ⟨g, hg⟩
  have he := (inferInstance : (q₂.subgroupOf s).Characteristic).fixed f
  have hy : f ⟨x, q₂_le_s hx⟩ ∈ q₂.subgroupOf s := by
    change (⟨x, q₂_le_s hx⟩ : s) ∈ (q₂.subgroupOf s).comap f.toMonoidHom
    rw [he]
    exact hx
  exact hy

theorem card_p₂ (hP : Nonempty ((p₂ ⧸ q₂.subgroupOf p₂) ≃* QuotientModel)) :
    Nat.card p₂ = 1152 := by
  obtain ⟨e⟩ := hP
  have hi : (q₂.subgroupOf p₂).index = 18 := by
    rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv]
    simp [QuotientModel, Nat.card_eq_fintype_card, Fintype.card_perm,
      Nat.factorial]
  have hc : Nat.card (q₂.subgroupOf p₂) = 64 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe q₂.le_normalizer).toEquiv).trans card_q₂
  have h := (q₂.subgroupOf p₂).card_mul_index
  rw [hc, hi] at h
  exact h.symm

private theorem intermediate_eq_B (hP : Nat.card p₂ = 1152)
    (H : Subgroup Carrier) (hBH : B ≤ H) (hHP : H ≤ p₂) (hne : H ≠ p₂) : H = B := by
  have hi : B.relIndex p₂ = 3 := by
    have h := (B.subgroupOf p₂).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe B_le_p₂).toEquiv, card_B, hP] at h
    change (B.subgroupOf p₂).index = 3
    omega
  have hm := Subgroup.relIndex_mul_relIndex B H p₂ hBH hHP
  rw [hi] at hm
  have hd : H.relIndex p₂ ∣ 3 := ⟨B.relIndex H, by simpa only [Nat.mul_comm] using hm.symm⟩
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with he | he
  · exact (hne (le_antisymm hHP (Subgroup.relIndex_eq_one.mp he))).elim
  · rw [he] at hm
    have h1 : B.relIndex H = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hBH

theorem normalizer_s_eq_B (hP : Nat.card p₂ = 1152) :
    Subgroup.normalizer (s : Set Carrier) = B := by
  apply intermediate_eq_B hP _ B_le_normalizer normalizer_s_le_p₂
  intro h
  exact u_not_normalizes_s (h ▸ oddGenerator_mem_p₂ 0)

theorem l₁_inf_p₂_eq_B (hP : Nat.card p₂ = 1152) : l₁ ⊓ p₂ = B := by
  apply intermediate_eq_B hP _ (le_inf B_le_l₁ B_le_p₂) inf_le_right
  intro h
  exact u_not_mem_l₁ (show oddGenerator 0 ∈ l₁ ⊓ p₂ from by rw [h]; exact oddGenerator_mem_p₂ 0).1


theorem l₂_sup_B (h₁ : Nat.card l₁ = 1920) (hP : Nat.card p₂ = 1152) : l₂ ⊔ B = p₂ := by
  have hf := ((sylow h₁).subtype s_le_p₂).normalizer_sup_eq_top'
    (N := l₂.subgroupOf p₂) (show s.subgroupOf p₂ ≤ l₂.subgroupOf p₂ from
      Subgroup.comap_mono s_le_l₂)
  have hn : Subgroup.normalizer (s.subgroupOf p₂ : Set p₂) = B.subgroupOf p₂ := by
    rw [← Subgroup.subgroupOf_normalizer_eq s_le_p₂, normalizer_s_eq_B hP]
  change Subgroup.normalizer (s.subgroupOf p₂ : Set p₂) ⊔ l₂.subgroupOf p₂ = ⊤ at hf
  rw [hn, ← Subgroup.subgroupOf_sup B_le_p₂ l₂_le_p₂] at hf
  have hh := congrArg (Subgroup.map p₂.subtype) hf
  rw [Subgroup.map_subgroupOf_eq_of_le (sup_le B_le_p₂ l₂_le_p₂), ← MonoidHom.range_eq_map,
    p₂.range_subtype] at hh
  exact sup_comm l₂ B ▸ hh

private def cWord : List (Fin 3) :=
  [2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0,
   1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1]
private def c : Carrier := localWord cWord
private def cTable : Equiv.Perm (Fin 100) := evalWord ![tableA, tableB, tableB⁻¹] cWord

private theorem inclusion_word (w : List (Fin 3)) :
    inclusion (localWord w) = evalWord ![tableA, tableB, tableB⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change inclusion (![a, b, b⁻¹] i * localWord w) = _
    rw [map_mul, ih]
    congr 1
    fin_cases i <;> simp [a, b, inclusion, generatorA_eq_table, generatorB_eq_table]

private theorem c_inclusion : inclusion c = cTable := inclusion_word _

set_option maxRecDepth 100000 in
private theorem c_mem_l₁ : c ∈ l₁ := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply inclusion_injective
  rw [map_mul, map_mul, c_inclusion, z_inclusion]
  decide +kernel

private def pathLetter : Fin 5 → Carrier := ![a, c, c⁻¹, oddGenerator 0, (oddGenerator 0)⁻¹]
private def pathWord : List (Fin 5) := [3, 1, 0, 3, 1, 4, 2]

set_option maxRecDepth 2000 in
private theorem path_inclusion (w : List (Fin 5)) :
    inclusion (evalWord pathLetter w) =
      evalWord ![tableA, cTable, cTable⁻¹, oddTable 0, (oddTable 0)⁻¹] w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [evalWord, map_mul, ih, evalWord]
    congr 1
    fin_cases i
    · exact generatorA_eq_table
    · exact c_inclusion
    · exact (map_inv inclusion c).trans (congrArg Inv.inv c_inclusion)
    · exact oddGenerator_inclusion 0
    · exact (map_inv inclusion (oddGenerator 0)).trans (congrArg Inv.inv (oddGenerator_inclusion 0))

set_option maxRecDepth 100000 in
private theorem path_centralizes : evalWord pathLetter pathWord * b⁻¹ ∈ l₁ := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply inclusion_injective
  simp only [map_mul, map_inv, path_inclusion, z_inclusion]
  change (_ * generatorB⁻¹) * _ = _ * (_ * generatorB⁻¹)
  rw [generatorB_eq_table]
  decide +kernel

set_option maxRecDepth 2000 in
private theorem a_eq_sGenerator : a = sGenerator 1 := by
  apply inclusion_injective
  rw [sGenerator_inclusion]
  change generatorA = sGenTable 1
  rw [generatorA_eq_table]
  decide +kernel

set_option maxRecDepth 2000 in
theorem l₁_sup_p₂ : l₁ ⊔ p₂ = ⊤ := by
  have ha : a ∈ l₁ ⊔ p₂ := (le_sup_left : l₁ ≤ l₁ ⊔ p₂)
    (s_le_l₁ (by rw [a_eq_sGenerator]; exact Subgroup.subset_closure ⟨1, rfl⟩))
  have hc : c ∈ l₁ ⊔ p₂ := (le_sup_left : l₁ ≤ l₁ ⊔ p₂) c_mem_l₁
  have hu : oddGenerator 0 ∈ l₁ ⊔ p₂ := (le_sup_right : p₂ ≤ l₁ ⊔ p₂) (oddGenerator_mem_p₂ 0)
  have hw (w : List (Fin 5)) : evalWord pathLetter w ∈ l₁ ⊔ p₂ := by
    induction w with
    | nil => exact (l₁ ⊔ p₂).one_mem
    | cons i w ih =>
      apply (l₁ ⊔ p₂).mul_mem _ ih
      fin_cases i
      · exact ha
      · exact hc
      · exact (l₁ ⊔ p₂).inv_mem hc
      · exact hu
      · exact (l₁ ⊔ p₂).inv_mem hu
  have hb : b ∈ l₁ ⊔ p₂ := by
    have hh := (l₁ ⊔ p₂).mul_mem ((l₁ ⊔ p₂).inv_mem
      ((le_sup_left : l₁ ≤ l₁ ⊔ p₂) path_centralizes)) (hw pathWord)
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
  apply top_unique
  rw [← closure_pair_eq_top]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact ha
  · exact (Set.mem_singleton_iff.mp hx) ▸ hb

theorem L_generate (h₁ : Nat.card l₁ = 1920) (hP : Nat.card p₂ = 1152) :
    L 0 ⊔ L 1 ⊔ s = ⊤ := by
  change l₁ ⊔ l₂ ⊔ s = ⊤
  have hh : l₁ ⊔ l₂ = l₁ ⊔ p₂ := by
    rw [← l₂_sup_B h₁ hP]
    exact le_antisymm (sup_le_sup_left le_sup_left _) (sup_le le_sup_left
      (sup_le le_sup_right (B_le_l₁.trans le_sup_left)))
  rw [hh, l₁_sup_p₂, top_sup_eq]

theorem B_normalizes (i : Fin 2) : B ≤ Subgroup.normalizer (L i : Set Carrier) := by
  fin_cases i
  · exact B_le_l₁.trans l₁.le_normalizer
  · exact B_le_p₂.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer l₂_le_p₂).mp l₂_normal_in_p₂)

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap
