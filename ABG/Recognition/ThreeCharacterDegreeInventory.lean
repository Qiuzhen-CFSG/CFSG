module

public import ABG.Recognition.ThreeCharacterTheory
public import Theory.Character.IrreducibleDegrees

/-!
# Wong's degree inventory for the group of order 5616

For the shared catalog in `ThreeGlobalDegreeData`, the principal character and
the seven distinguished irreducibles contribute 4592 to the degree-square sum.
The remaining contribution is 1024. Every remaining degree is a positive
multiple of 16, hence is 16 or 32; degree divisibility excludes 32 because it
does not divide 5616. Consequently there are four remaining irreducibles and
twelve conjugacy classes.

The exported finsets consist of actual irreducible character functions. In
particular, the conclusion retains the original seven witnesses and makes no
assumption of a character table.

Source: W. J. Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2” (1964), Appendix, case (b), p.108.
-/

namespace ABG
open BenderGlauberman
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace ThreeGlobalDegreeData

variable {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)

private def sevenEmbedding : Fin 7 ↪ {χ : ClassFunction G // IsIrreducibleCharacter χ} where
  toFun i := ⟨c.decomposition.χ i, c.decomposition.irreducible i⟩
  inj' _ _ h := c.decomposition.distinct (congrArg Subtype.val h)

private theorem principal_not_mem_seven :
    (⟨1, isLinearCharacter_one.1⟩ : {χ : ClassFunction G // IsIrreducibleCharacter χ}) ∉
      Finset.univ.map c.sevenEmbedding := by
  classical
  simp only [Finset.mem_map, Finset.mem_univ, true_and, not_exists]
  intro i hi
  exact c.decomposition.nontrivial i (congrArg Subtype.val hi)

/-- The principal character together with the original seven distinguished
irreducibles. -/
public def characterCatalog : Finset {χ : ClassFunction G // IsIrreducibleCharacter χ} := by
  classical
  exact insert ⟨1, isLinearCharacter_one.1⟩ (Finset.univ.map c.sevenEmbedding)

/-- Membership in the catalog is expressed using the original character
functions, with no auxiliary choices of irreducibles. -/
public theorem mem_characterCatalog (θ : {χ : ClassFunction G // IsIrreducibleCharacter χ}) :
    θ ∈ c.characterCatalog ↔ θ.val = 1 ∨ ∃ i, θ.val = c.decomposition.χ i := by
  classical
  simp [characterCatalog, sevenEmbedding, Subtype.ext_iff, eq_comm]
  rfl

/-- The catalog contains exactly eight distinct irreducibles. -/
public theorem card_characterCatalog : c.characterCatalog.card = 8 := by
  classical
  simp [characterCatalog, Finset.card_insert_of_notMem c.principal_not_mem_seven]

/-- All irreducibles outside the principal/seven-character catalog. -/
public def remainingIrreducibles : Finset {χ : ClassFunction G // IsIrreducibleCharacter χ} := by
  classical
  exact c.characterCatalogᶜ

/-- The complement finset encodes precisely the hypotheses of the
remaining-character vanishing and divisibility theorems. -/
public theorem mem_remainingIrreducibles
    (θ : {χ : ClassFunction G // IsIrreducibleCharacter χ}) :
    θ ∈ c.remainingIrreducibles ↔ θ.val ≠ 1 ∧ ∀ i, θ.val ≠ c.decomposition.χ i := by
  classical
  simp [remainingIrreducibles, c.mem_characterCatalog]

/-- The order 5616 selects the second degree vector. -/
public theorem degrees_of_card_5616 (hG : Nat.card G = 5616) :
    c.decomposition.degree = ![26,27,26,26,39,12,13] := by
  rcases c.degree_alternatives with ⟨_, h⟩ | ⟨h, _⟩
  · omega
  · exact h

/-- The eight catalog degrees contribute 4592 to the sum of squares. -/
public theorem sum_characterCatalog_degree_sq (hG : Nat.card G = 5616) :
    ∑ θ ∈ c.characterCatalog, θ.property.degree ^ 2 = 4592 := by
  classical
  have hprincipal : (isLinearCharacter_one (G := G)).1.degree = 1 := by
    have h := (isLinearCharacter_one (G := G)).1.degree_eq
    change (1 : ℂ) = _ at h
    exact_mod_cast h.symm
  have hdegree (i : Fin 7) : (c.sevenEmbedding i).property.degree = c.decomposition.degree i := by
    have h := (c.sevenEmbedding i).property.degree_eq
    change c.decomposition.χ i 1 = _ at h
    rw [c.decomposition.degree_eq i] at h
    exact_mod_cast h.symm
  rw [characterCatalog, Finset.sum_insert c.principal_not_mem_seven, Finset.sum_map]
  simp only [hprincipal, hdegree, c.degrees_of_card_5616 hG]
  norm_num [Fin.sum_univ_succ]

/-- The remaining irreducibles contribute exactly 1024 to the sum of squares. -/
public theorem sum_remainingIrreducibles_degree_sq (hG : Nat.card G = 5616) :
    ∑ θ ∈ c.remainingIrreducibles, θ.property.degree ^ 2 = 1024 := by
  classical
  have h := Finset.sum_compl_add_sum c.characterCatalog
    (fun θ => θ.property.degree ^ 2)
  rw [Theory.Character.sum_irreducibleCharacters_degree_sq,
    c.sum_characterCatalog_degree_sq hG, hG] at h
  change (∑ θ ∈ c.remainingIrreducibles, θ.property.degree ^ 2) + 4592 = 5616 at h
  omega

/-- Every remaining irreducible in the order-5616 branch has degree 16. -/
public theorem remainingIrreducible_degree_eq_sixteen (hG : Nat.card G = 5616)
    (θ : {χ : ClassFunction G // IsIrreducibleCharacter χ})
    (hθ : θ ∈ c.remainingIrreducibles) : θ.property.degree = 16 := by
  classical
  obtain ⟨h1, hχ⟩ := (c.mem_remainingIrreducibles θ).mp hθ
  obtain ⟨n, hn, hn16⟩ := c.remaining_degree θ.val θ.property h1 hχ
  have hn' : n = θ.property.degree := by
    have h := θ.property.degree_eq
    rw [hn] at h
    exact_mod_cast h
  rw [hn'] at hn16
  have hbound := Finset.single_le_sum
    (f := fun θ : {χ : ClassFunction G // IsIrreducibleCharacter χ} => θ.property.degree ^ 2)
    (fun _ _ => Nat.zero_le _) hθ
  rw [c.sum_remainingIrreducibles_degree_sq hG] at hbound
  have hpos := θ.property.degree_pos
  have hdvd := θ.property.degree_dvd_card
  rw [hG] at hdvd
  have hle : θ.property.degree ≤ 32 := by nlinarith
  have halt : θ.property.degree = 16 ∨ θ.property.degree = 32 := by omega
  rcases halt with h | h
  · exact h
  · rw [h] at hdvd
    norm_num at hdvd

/-- There are exactly four irreducibles outside the principal/seven catalog. -/
public theorem card_remainingIrreducibles (hG : Nat.card G = 5616) :
    c.remainingIrreducibles.card = 4 := by
  have hs := c.sum_remainingIrreducibles_degree_sq hG
  have he : (∑ θ ∈ c.remainingIrreducibles, θ.property.degree ^ 2) =
      c.remainingIrreducibles.card * 256 := by
    calc
      _ = ∑ _θ ∈ c.remainingIrreducibles, (16 : ℕ)^2 :=
        Finset.sum_congr rfl (fun θ hθ => by rw [c.remainingIrreducible_degree_eq_sixteen hG θ hθ])
      _ = _ := by simp
  rw [he] at hs
  omega

/-- Function-level form of the degree-16 conclusion for a character outside
the original catalog. -/
public theorem remaining_character_degree_eq_sixteen (hG : Nat.card G = 5616)
    {θ : ClassFunction G} (hθ : IsIrreducibleCharacter θ) (h1 : θ ≠ 1)
    (hχ : ∀ i, θ ≠ c.decomposition.χ i) : θ 1 = 16 := by
  have hm := (c.mem_remainingIrreducibles ⟨θ, hθ⟩).mpr ⟨h1, hχ⟩
  rw [hθ.degree_eq, c.remainingIrreducible_degree_eq_sixteen hG ⟨θ, hθ⟩ hm]
  norm_num

/-- Four distinct degree-16 character functions enumerate exactly the
irreducibles outside the principal/seven catalog. -/
public theorem exists_four_remaining_characters (hG : Nat.card G = 5616) :
    ∃ ψ : Fin 4 → ClassFunction G, Function.Injective ψ ∧
      (∀ i, IsIrreducibleCharacter (ψ i) ∧ ψ i 1 = 16) ∧
      ∀ θ : ClassFunction G,
        (IsIrreducibleCharacter θ ∧ θ ≠ 1 ∧ ∀ i, θ ≠ c.decomposition.χ i) ↔
          ∃ i, ψ i = θ := by
  classical
  let e : Fin 4 ≃ {θ // θ ∈ c.remainingIrreducibles} :=
    (Fintype.equivFinOfCardEq (by simpa using c.card_remainingIrreducibles hG)).symm
  let ψ : Fin 4 → ClassFunction G := fun i => (e i).val.val
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    exact Subtype.ext (Subtype.ext hij)
  · intro i
    refine ⟨(e i).val.property, ?_⟩
    obtain ⟨h1, hχ⟩ := (c.mem_remainingIrreducibles (e i).val).mp (e i).property
    exact c.remaining_character_degree_eq_sixteen hG (e i).val.property h1 hχ
  · intro θ
    constructor
    · rintro ⟨hθ, h1, hχ⟩
      let a : {θ // θ ∈ c.remainingIrreducibles} :=
        ⟨⟨θ, hθ⟩, (c.mem_remainingIrreducibles ⟨θ, hθ⟩).mpr ⟨h1, hχ⟩⟩
      exact ⟨e.symm a, congrArg (fun x => x.val.val) (e.apply_symm_apply a)⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(e i).val.property,
        (c.mem_remainingIrreducibles (e i).val).mp (e i).property⟩

include c in
/-- In the order-5616 branch there are twelve irreducible character functions. -/
public theorem card_irreducibles (hG : Nat.card G = 5616) :
    Nat.card {χ : ClassFunction G // IsIrreducibleCharacter χ} = 12 := by
  classical
  have h := Finset.card_compl_add_card c.characterCatalog
  change c.remainingIrreducibles.card + c.characterCatalog.card = _ at h
  rw [c.card_remainingIrreducibles hG, c.card_characterCatalog] at h
  rw [Nat.card_eq_fintype_card]
  omega

include c in
/-- The degree inventory gives twelve conjugacy classes. -/
public theorem card_conjClasses (hG : Nat.card G = 5616) :
    Nat.card (ConjClasses G) = 12 := by
  rw [← Theory.Character.card_irreducibleCharacters]
  exact c.card_irreducibles hG

end ThreeGlobalDegreeData
end
end ABG
