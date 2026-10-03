module
public import ABG.Recognition.ThreeMathieuCharacterData

/-!
# The ten irreducible characters in Wong's order-7920 branch

The regular-character degree identity, applied to the actual irreducibles,
leaves a sum of 512 after removing the trivial character and the shared seven
characters. Every remaining degree is a positive multiple of 16. The individual
square bound therefore forces degree 16; summing again gives exactly two
remaining irreducibles and ten conjugacy classes.

Source: Wong (1964), Theorem 6(a), p.107,
DOI 10.1017/S1446788700022771.
-/
open BenderGlauberman
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

private def irrDegree {G : Type*} [Group G] (θ : IrrBG19 G) : ℕ :=
  Classical.choose θ.property

private theorem irrDegree_eq {G : Type*} [Group G] (θ : IrrBG19 G) :
    θ.val 1 = (irrDegree θ : ℂ) := by
  obtain ⟨ρ, _, hρ⟩ := Classical.choose_spec θ.property
  simp [hρ, Representation.char_one, irrDegree]

private theorem irrDegree_pos {G : Type*} [Group G] (θ : IrrBG19 G) :
    0 < irrDegree θ := by
  have h := irreducible_degree_ge_one θ.property
  rw [irrDegree_eq] at h
  have : 1 ≤ irrDegree θ := by exact_mod_cast h
  omega

private theorem sum_irrDegree_sq {G : Type*} [Group G] [Finite G] :
    ∑ θ : IrrBG19 G, irrDegree θ ^ 2 = Nat.card G := by
  classical
  obtain ⟨ι, hι, χ, hχ, hsum⟩ :=
    exists_completeIrreducibleCharacterFamily_sum_degree_normSq (G := G)
  let : Fintype ι := hι
  let f : ι → IrrBG19 G := fun i =>
    ⟨ofConjClassFunction (χ i), isIrreducibleCharacter_ofConjClassFunctionBG19 (hχ.1 i)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply hχ.2.2
      ext c
      obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
      exact congrFun (congrArg Subtype.val hij) g
    · intro θ
      obtain ⟨i, hi⟩ := hχ.2.1 _
        (isIrreducibleConjCharacter_of_isIrreducibleCharacterBG19 θ.property)
      refine ⟨i, Subtype.ext ?_⟩
      change ofConjClassFunction (χ i) = θ.val
      rw [hi]
      rfl
  have hval (i : ι) : Complex.normSq (χ i (ConjClasses.mk (1 : G))) =
      (irrDegree (f i) : ℝ) ^ 2 := by
    change Complex.normSq ((f i).val 1) = _
    rw [irrDegree_eq]
    simp [Complex.normSq_apply, pow_two]
  simp_rw [hval] at hsum
  have hreindex := Fintype.sum_equiv (Equiv.ofBijective f hf)
    (fun i => (irrDegree (f i) : ℝ) ^ 2)
    (fun θ => (irrDegree θ : ℝ) ^ 2) (fun _ => rfl)
  rw [hreindex] at hsum
  exact_mod_cast hsum

namespace ABG
variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)

/-- Exactly two irreducibles remain outside the supplied seven-character catalog
and the trivial character, both of degree sixteen; there are ten classes. -/
public theorem ThreeGlobalDegreeData.mathieu_remaining_irreducibles
    (hG : Nat.card G = 7920) :
    Nat.card {θ : IrrBG19 G // θ.val ≠ 1 ∧ ∀ i, θ.val ≠ c.decomposition.χ i} = 2 ∧
    (∀ θ : IrrBG19 G, θ.val ≠ 1 → (∀ i, θ.val ≠ c.decomposition.χ i) → θ.val 1 = 16) ∧
    Nat.card (ConjClasses G) = 10 := by
  classical
  let f : Fin 7 → IrrBG19 G := fun i => ⟨c.decomposition.χ i, c.decomposition.irreducible i⟩
  let t : IrrBG19 G := ⟨1, isLinearCharacter_one.1⟩
  let k : Finset (IrrBG19 G) := insert t (Finset.univ.image f)
  have hf : Function.Injective f := fun _ _ h => c.decomposition.distinct (congrArg Subtype.val h)
  have ht : t ∉ Finset.univ.image f := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi
    exact c.decomposition.nontrivial i (congrArg Subtype.val hi)
  have hmem (θ : IrrBG19 G) : θ ∈ kᶜ ↔ θ.val ≠ 1 ∧ ∀ i, θ.val ≠ c.decomposition.χ i := by
    simp only [Finset.mem_compl, k, Finset.mem_insert, Finset.mem_image,
      Finset.mem_univ, true_and, not_or, not_exists]
    constructor
    · rintro ⟨h1, hi⟩
      exact ⟨fun h => h1 (Subtype.ext h), fun i h => hi i (Subtype.ext h.symm)⟩
    · rintro ⟨h1, hi⟩
      exact ⟨fun h => h1 (congrArg Subtype.val h), fun i h => hi i (congrArg Subtype.val h).symm⟩
  have hdf (i : Fin 7) : irrDegree (f i) = c.decomposition.degree i := by
    have h : (irrDegree (f i) : ℂ) = c.decomposition.degree i :=
      (irrDegree_eq (f i)).symm.trans (c.decomposition.degree_eq i)
    exact_mod_cast h
  have hdt : irrDegree t = 1 := by
    have h := irrDegree_eq t
    change (1 : ℂ) = (irrDegree t : ℂ) at h
    exact_mod_cast h.symm
  have hkcard : k.card = 8 := by
    simp [k, Finset.card_insert_of_notMem ht, Finset.card_image_of_injective _ hf]
  have hksum : ∑ θ ∈ k, irrDegree θ ^ 2 = 7408 := by
    rw [Finset.sum_insert ht, hdt, Finset.sum_image (fun _ _ _ _ h => hf h)]
    simp_rw [hdf, c.mathieu_degrees hG]
    norm_num [Fin.sum_univ_succ]
  have hrsum : ∑ θ ∈ kᶜ, irrDegree θ ^ 2 = 512 := by
    have h := Finset.sum_add_sum_compl k (fun θ => irrDegree θ ^ 2)
    rw [hksum, sum_irrDegree_sq, hG] at h
    omega
  have hd16 (θ : IrrBG19 G) (hθ : θ ∈ kᶜ) : irrDegree θ = 16 := by
    obtain ⟨h1, hχ⟩ := (hmem θ).mp hθ
    obtain ⟨n, hn, hn16⟩ := c.remaining_degree θ.val θ.property h1 hχ
    have hn' : irrDegree θ = n := by
      exact_mod_cast (irrDegree_eq θ).symm.trans hn
    have hpos := irrDegree_pos θ
    have hle : irrDegree θ ^ 2 ≤ 512 := by
      rw [← hrsum]
      exact Finset.single_le_sum (f := fun θ => irrDegree θ ^ 2) (fun _ _ => Nat.zero_le _) hθ
    rw [← hn'] at hn16
    obtain ⟨m, hm⟩ := hn16
    have : m = 1 := by nlinarith
    simpa [this] using hm
  have hrcard : kᶜ.card = 2 := by
    have h := hrsum
    have heq : ∑ θ ∈ kᶜ, irrDegree θ ^ 2 = kᶜ.card * 256 := by
      simp only [Finset.sum_congr rfl (fun θ hθ => congrArg (· ^ 2) (hd16 θ hθ))]
      simp
    rw [heq] at h
    omega
  refine ⟨?_, ?_, ?_⟩
  · let e : {θ : IrrBG19 G // θ.val ≠ 1 ∧ ∀ i, θ.val ≠ c.decomposition.χ i} ≃ ↥(kᶜ) :=
      { toFun := fun θ => ⟨θ.val, (hmem _).mpr θ.property⟩
        invFun := fun θ => ⟨θ.val, (hmem _).mp θ.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, hrcard]
  · intro θ h1 hi
    rw [irrDegree_eq, hd16 θ ((hmem θ).mpr ⟨h1, hi⟩)]
    norm_num
  · rw [← fintype_card_irr_eq_conjClassesBG19]
    have h := Finset.card_add_card_compl k
    rw [hkcard, hrcard] at h
    omega
include c in
/-- The order-7920 branch has ten conjugacy classes. -/
public theorem ThreeGlobalDegreeData.mathieu_class_count
    (hG : Nat.card G = 7920) : Nat.card (ConjClasses G) = 10 :=
  (c.mathieu_remaining_irreducibles hG).2.2

/-- Every irreducible absent from the eight known ones has degree sixteen. -/
public theorem ThreeGlobalDegreeData.mathieu_remaining_degree
    (hG : Nat.card G = 7920) {θ : ClassFunction G}
    (hθ : IsIrreducibleCharacter θ) (h1 : θ ≠ 1)
    (hχ : ∀ i, θ ≠ c.decomposition.χ i) : θ 1 = 16 :=
  (c.mathieu_remaining_irreducibles hG).2.1 ⟨θ, hθ⟩ h1 hχ

/-- The two missing irreducibles, with distinctness, degree sixteen, and
completeness relative to the same seven-character catalog. -/
public theorem ThreeGlobalDegreeData.exists_mathieuAdditionalCharacters (hG : Nat.card G = 7920) :
    ∃ θ : Fin 2 → ClassFunction G,
      (∀ i, IsIrreducibleCharacter (θ i)) ∧ Function.Injective θ ∧
      (∀ i, θ i ≠ 1) ∧ (∀ i j, θ i ≠ c.decomposition.χ j) ∧
      (∀ i, θ i 1 = 16) ∧
      (∀ ψ : ClassFunction G, IsIrreducibleCharacter ψ →
        (ψ = 1 ∨ (∃ j, ψ = c.decomposition.χ j) ∨ ∃! i, ψ = θ i)) := by
  classical
  let R := {ψ : IrrBG19 G // ψ.val ≠ 1 ∧ ∀ i, ψ.val ≠ c.decomposition.χ i}
  have hc : Fintype.card R = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact (c.mathieu_remaining_irreducibles hG).1
  let e : Fin 2 ≃ R := (Fintype.equivFinOfCardEq hc).symm
  let θ : Fin 2 → ClassFunction G := fun i => (e i).val.val
  have hinj : Function.Injective θ := by
    intro i j h
    exact e.injective (Subtype.ext (Subtype.ext h))
  refine ⟨θ, (fun i => (e i).val.property), hinj,
    (fun i => (e i).property.1), (fun i => (e i).property.2), ?_, ?_⟩
  · intro i
    exact c.mathieu_remaining_degree hG (e i).val.property (e i).property.1 (e i).property.2
  · intro ψ hψ
    by_cases h1 : ψ = 1
    · exact Or.inl h1
    by_cases hi : ∃ j, ψ = c.decomposition.χ j
    · exact Or.inr (Or.inl hi)
    have hr : ψ ≠ 1 ∧ ∀ j, ψ ≠ c.decomposition.χ j := ⟨h1, by simpa using hi⟩
    let r : R := ⟨⟨ψ, hψ⟩, hr⟩
    refine Or.inr (Or.inr ⟨e.symm r, ?_, ?_⟩)
    · change ψ = (e (e.symm r)).val.val
      rw [e.apply_symm_apply]
    · intro i hi
      apply hinj
      rw [← hi]
      change ψ = (e (e.symm r)).val.val
      rw [e.apply_symm_apply]

end ABG
