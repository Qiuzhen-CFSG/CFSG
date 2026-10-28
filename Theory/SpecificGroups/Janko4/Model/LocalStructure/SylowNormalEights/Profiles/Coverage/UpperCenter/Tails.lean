module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Coverage.FiniteCatalogue
public import Theory.GroupTheory.BinaryCollection.Subsequence

/-!
# Normal tails of the Sylow presentation

The subgroup `tail n` is the literal closure of generators numbered at least
`n`. The inverse-conjugation relations make each tail normal. Binary collection
and uniqueness of the full normal forms give its order `2^(21-n)`, so no
canonical generator belongs to the next tail. Each tail consists of the next
tail and its single generator coset.

These facts support the successive quotient-centralizer tests in
`Coverage/UpperCenter.lean`. The only consistency input is the stated order
of the presentation. Source: the literal relations in `PresentationData` and
`SylowNormalEights/source/pc.json`; provenance and inverse-conjugation conventions
are documented in the adjacent source README.
-/

@[expose] public section

open Theory.GroupTheory.BinaryCollection
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.Coverage.UpperCenter

def suffix (n : Fin 22) : List (Fin 21) := (List.finRange 21).drop n.val
def tail (n : Fin 22) : Subgroup Carrier := Subgroup.closure {x | x ∈ (suffix n).map generator}

lemma mem_suffix (n : Fin 22) (i : Fin 21) : i ∈ suffix n ↔ n.val ≤ i.val :=
  (by decide +kernel : ∀ (n : Fin 22) (i : Fin 21), i ∈ suffix n ↔ n.val ≤ i.val) n i

lemma word_mem_tail (n : Fin 22) (w : List (Fin 21))
    (hw : ∀ i ∈ w, n.val ≤ i.val) : wordValue w ∈ tail n := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure (List.mem_map.mpr ⟨i, (mem_suffix n i).mpr (hw i hi), rfl⟩)

private lemma generator_mem_tail (n : Fin 22) (i : Fin 21) (hi : n.val ≤ i.val) :
    generator i ∈ tail n :=
  Subgroup.subset_closure (List.mem_map.mpr ⟨i, (mem_suffix n i).mpr hi, rfl⟩)

lemma tail_antitone {n m : Fin 22} (h : n ≤ m) : tail m ≤ tail n := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact generator_mem_tail n i (le_trans h ((mem_suffix m i).mp hi))

private lemma triangular_drop {G : Type*} [Group G] (l : List G) (h : triangular l) (n : ℕ) :
    triangular (l.drop n) := by
  induction n generalizing l with
  | zero => exact h
  | succ n ih =>
    cases l with
    | nil => trivial
    | cons a l => exact ih l h.2.2

private lemma tail_card (hcard : Nat.card Carrier = 2 ^ 21) (n : Fin 22) :
    Nat.card (tail n) = 2 ^ (21 - n.val) := by
  have hinj : Function.Injective
      (fun n : Fin (2 ^ (List.ofFn generator).length) => product (List.ofFn generator) n.val) := by
    intro n m h
    have he := (normalForm_bijective_of_card hcard).injective
      (a₁ := ⟨n.val, by simpa only [List.length_ofFn] using n.isLt⟩)
      (a₂ := ⟨m.val, by simpa only [List.length_ofFn] using m.isLt⟩) h
    exact Fin.ext (congrArg Fin.val he)
  have hs : ((suffix n).map generator).Sublist (List.ofFn generator) :=
    (List.drop_sublist n.val (List.finRange 21)).map generator
  have ht : triangular ((suffix n).map generator) := by
    unfold suffix
    rw [List.map_drop]
    exact triangular_drop (List.ofFn generator) generator_triangular n.val
  have he := card_closure_of_sublist hs ht hinj
  simpa only [tail, suffix, List.length_map, List.length_drop, List.length_finRange] using he

private lemma suffix_cons (i : Fin 21) : suffix i.castSucc = i :: suffix i.succ :=
  (by decide +kernel : ∀ i : Fin 21, suffix i.castSucc = i :: suffix i.succ) i

private lemma tail_step (i : Fin 21) (H : Subgroup Carrier) (hhead : generator i ∈ H)
    (htail : tail i.succ ≤ H) : tail i.castSucc ≤ H := by
  apply (Subgroup.closure_le _).mpr
  rw [suffix_cons, List.map_cons]
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hhead
  · exact htail (Subgroup.subset_closure hx)

lemma generator_not_tail (hcard : Nat.card Carrier = 2 ^ 21) (i : Fin 21) :
    generator i ∉ tail i.succ := by
  intro h
  have he : tail i.castSucc = tail i.succ := le_antisymm (tail_step i _ h le_rfl)
    (tail_antitone i.castSucc_le_succ)
  have hh := congrArg (fun K : Subgroup Carrier => Nat.card K) he
  rw [tail_card hcard, tail_card hcard] at hh
  exact ((by decide +kernel : ∀ i : Fin 21,
    2 ^ (21 - i.castSucc.val) ≠ (2 ^ (21 - i.succ.val) : ℕ)) i) hh

private lemma conjugate_support (i j k : Fin 21) (hij : i < j)
    (hk : k ∈ conjugateWord i j) : j.val ≤ k.val :=
  (by decide +kernel : ∀ i j k : Fin 21, i < j → k ∈ conjugateWord i j → j.val ≤ k.val) i j k hij hk

instance tail_normal (n : Fin 22) : (tail n).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← show Subgroup.closure (Set.range generator) = ⊤ from PresentedGroup.closure_range_of _]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  apply (Subgroup.normalizer (tail n : Set Carrier)).inv_mem_iff.mp
  apply Subgroup.mem_normalizer_fintype
  have hc : tail n ≤ (tail n).comap (MulAut.conj (generator i)⁻¹).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hj := (mem_suffix n j).mp hj
    change (generator i)⁻¹ * generator j * ((generator i)⁻¹)⁻¹ ∈ tail n
    rw [inv_inv]
    by_cases hij : i < j
    · rw [generator_relations.conjugate i j hij]
      exact word_mem_tail n _ (fun k hk => le_trans hj (conjugate_support i j k hij hk))
    · have hi : generator i ∈ tail n := generator_mem_tail n i (by omega)
      exact (tail n).mul_mem ((tail n).mul_mem ((tail n).inv_mem hi)
        (generator_mem_tail n j hj)) hi
  exact fun x hx => hc hx

lemma tail_two_cosets (i : Fin 21) {x : Carrier} (hx : x ∈ tail i.castSucc) :
    x ∈ tail i.succ ∨ ∃ y ∈ tail i.succ, x = generator i * y := by
  have ht : triangular (generator i :: (suffix i.succ).map generator) := by
    rw [← List.map_cons, ← suffix_cons]
    unfold suffix
    rw [List.map_drop]
    exact triangular_drop (List.ofFn generator) generator_triangular i.val
  have hc (y : Carrier) (hy : y ∈ tail i.succ) :
      (generator i)⁻¹ * y * generator i ∈ tail i.succ := by
    simpa only [inv_inv] using (tail_normal i.succ).conj_mem y hy (generator i)⁻¹
  let E := Subgroup.twoCosetExtension (tail i.succ) (generator i) ht.1 hc
  have hle : tail i.castSucc ≤ E := by
    apply tail_step i E
    · exact Or.inr ⟨1, (tail i.succ).one_mem, (mul_one _).symm⟩
    · exact fun _ h => Or.inl h
  exact hle hx

lemma tail_zero : tail 0 = ⊤ := by
  change Subgroup.closure {x | x ∈ List.ofFn generator} = ⊤
  simp only [List.mem_ofFn', Set.ofPred_mem_eq]
  exact PresentedGroup.closure_range_of _

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.Coverage.UpperCenter
