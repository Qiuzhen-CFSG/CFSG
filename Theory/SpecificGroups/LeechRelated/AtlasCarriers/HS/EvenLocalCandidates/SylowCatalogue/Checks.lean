module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue.Data

/-!
# Checked transitions for the HS subgroup enumeration

The point tables transform by each of the three original generators.
A short walk through these transitions reaches the assigned row for every
listed word. Inverse transitions are checked on row indices. These finite
identities support the word-induction proof in `Enumeration`.

Source: the fixed ATLAS permutations; GLS volume 3, Table 5.3m, printed p.274.
The candidate data are reproduced by `source/generate.py`. Every finite
identity below is checked in Lean's kernel.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData
set_option maxRecDepth 100000
set_option Elab.async false

def generatorPoint : Fin 3 → Fin 100 → Fin 100 := ![s0Map, s1Map, s2Map]

theorem generatorPoint_spec (j : Fin 3) (x : Fin 100) :
    (sylowGenerator j : Equiv.Perm (Fin 100)) x = generatorPoint j x := by
  fin_cases j <;> rfl

private def blockIndex (b : Fin 16) (i : Fin 32) : Fin 512 :=
  ⟨32 * b.val + i.val, by omega⟩

private theorem transitionBlock0 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 0 i)) x =
      generatorPoint j (point (blockIndex 0 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock1 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 1 i)) x =
      generatorPoint j (point (blockIndex 1 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock2 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 2 i)) x =
      generatorPoint j (point (blockIndex 2 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock3 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 3 i)) x =
      generatorPoint j (point (blockIndex 3 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock4 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 4 i)) x =
      generatorPoint j (point (blockIndex 4 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock5 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 5 i)) x =
      generatorPoint j (point (blockIndex 5 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock6 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 6 i)) x =
      generatorPoint j (point (blockIndex 6 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock7 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 7 i)) x =
      generatorPoint j (point (blockIndex 7 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock8 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 8 i)) x =
      generatorPoint j (point (blockIndex 8 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock9 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 9 i)) x =
      generatorPoint j (point (blockIndex 9 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock10 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 10 i)) x =
      generatorPoint j (point (blockIndex 10 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock11 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 11 i)) x =
      generatorPoint j (point (blockIndex 11 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock12 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 12 i)) x =
      generatorPoint j (point (blockIndex 12 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock13 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 13 i)) x =
      generatorPoint j (point (blockIndex 13 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock14 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 14 i)) x =
      generatorPoint j (point (blockIndex 14 i) x) := by
  apply allFin₃
  decide +kernel

private theorem transitionBlock15 : ∀ (j : Fin 3) (i : Fin 32) (x : Fin 100),
    point (next (Fin.castAdd 3 j) (blockIndex 15 i)) x =
      generatorPoint j (point (blockIndex 15 i) x) := by
  apply allFin₃
  decide +kernel

theorem point_transition (j : Fin 3) (i : Fin 512) (x : Fin 100) :
    point (next (Fin.castAdd 3 j) i) x = generatorPoint j (point i x) := by
  have h : ∀ (b : Fin 16) (k : Fin 32),
      point (next (Fin.castAdd 3 j) (blockIndex b k)) x =
        generatorPoint j (point (blockIndex b k) x) := by
    intro b
    fin_cases b
    · exact fun k => transitionBlock0 j k x
    · exact fun k => transitionBlock1 j k x
    · exact fun k => transitionBlock2 j k x
    · exact fun k => transitionBlock3 j k x
    · exact fun k => transitionBlock4 j k x
    · exact fun k => transitionBlock5 j k x
    · exact fun k => transitionBlock6 j k x
    · exact fun k => transitionBlock7 j k x
    · exact fun k => transitionBlock8 j k x
    · exact fun k => transitionBlock9 j k x
    · exact fun k => transitionBlock10 j k x
    · exact fun k => transitionBlock11 j k x
    · exact fun k => transitionBlock12 j k x
    · exact fun k => transitionBlock13 j k x
    · exact fun k => transitionBlock14 j k x
    · exact fun k => transitionBlock15 j k x
  have hi : blockIndex ⟨i.val / 32, by omega⟩ ⟨i.val % 32, by omega⟩ = i := by
    apply Fin.ext
    simp only [blockIndex]
    omega
  simpa only [hi] using h ⟨i.val / 32, by omega⟩ ⟨i.val % 32, by omega⟩

theorem next_cancel : ∀ (j : Fin 3) (i : Fin 512),
    next (Fin.castAdd 3 j) (next (Fin.natAdd 3 j) i) = i := by
  apply allFin₂
  decide +kernel

theorem point_zero : ∀ x : Fin 100, point 0 x = x := by
  apply allFin
  decide +kernel

/-- Follow a word through the candidate generator transitions. -/
def rowOfWord : List (Fin 3) → Fin 512
  | [] => 0
  | j :: w => next (Fin.castAdd 3 j) (rowOfWord w)

theorem rowOfWord_word : ∀ i : Fin 512, rowOfWord (word i) = i := by
  apply allFin
  decide +kernel

theorem decode_point : ∀ i : Fin 512, decode (point i 1) (point i 4) = i.val := by
  apply allFin
  decide +kernel

end Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData
