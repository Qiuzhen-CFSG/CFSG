module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismPointStabilizers.SmallIndex.CarrierComparison

/-!
# The centralizer of the concrete HS point stabilizer

The stabilizer generators have three orbits on the original 100 letters.
Common fixed points of the first three levels force any commuting permutation
to fix the representatives 0, 4 and 2. Words of length at most three carry
these representatives to every letter, so that permutation is the identity.
All finite identities are checked in Lean's kernel.

The subgroup comparison identifies the certified generators with the literal
point stabilizer. This supplies the HS odd-local exclusion for the Mathieu
section in Aschbacher--Smith 4.4.3, printed p.623. The original ATLAS
HSG1-p100B0 carrier and its attribution are retained by the imported modules;
see also GLS3, Table 5.3m, printed p.274.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.HS.PointCentralizer
open OrderCertificate

private theorem fixed1 : ∀ x : Fin 100, (∀ i, gen1 i x = x) → x = 0 := by
  apply allFin
  decide +kernel
private theorem fixed2 : ∀ x : Fin 100, (∀ i, gen2 i x = x) → x = 0 ∨ x = 4 := by
  apply allFin
  decide +kernel
private theorem fixed3 : ∀ x : Fin 100, (∀ i, gen3 i x = x) → x = 0 ∨ x = 4 ∨ x = 2 := by
  apply allFin
  decide +kernel
private theorem seeds_fixed1 : ∀ i, gen1 i 0 = 0 := by apply allFin; decide +kernel
private theorem seeds_fixed2 : ∀ i, gen2 i 4 = 4 := by apply allFin; decide +kernel
private theorem seeds_fixed3 : ∀ i, gen3 i 2 = 2 := by apply allFin; decide +kernel
private def orbitBase (x : Fin 100) : Fin 100 :=
  match x.val with
  | 0 => 0
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 4
  | 9 => 4
  | 10 => 4
  | 11 => 4
  | 12 => 4
  | 13 => 2
  | 14 => 2
  | 15 => 2
  | 16 => 2
  | 17 => 2
  | 18 => 2
  | 19 => 2
  | 20 => 2
  | 21 => 2
  | 22 => 2
  | 23 => 2
  | 24 => 2
  | 25 => 2
  | 26 => 4
  | 27 => 2
  | 28 => 4
  | 29 => 2
  | 30 => 2
  | 31 => 2
  | 32 => 4
  | 33 => 2
  | 34 => 2
  | 35 => 2
  | 36 => 2
  | 37 => 2
  | 38 => 4
  | 39 => 4
  | 40 => 4
  | 41 => 2
  | 42 => 2
  | 43 => 2
  | 44 => 4
  | 45 => 2
  | 46 => 2
  | 47 => 4
  | 48 => 2
  | 49 => 4
  | 50 => 4
  | 51 => 2
  | 52 => 4
  | 53 => 2
  | 54 => 2
  | 55 => 2
  | 56 => 2
  | 57 => 2
  | 58 => 2
  | 59 => 2
  | 60 => 2
  | 61 => 2
  | 62 => 2
  | 63 => 2
  | 64 => 2
  | 65 => 2
  | 66 => 4
  | 67 => 4
  | 68 => 2
  | 69 => 2
  | 70 => 4
  | 71 => 4
  | 72 => 2
  | 73 => 2
  | 74 => 2
  | 75 => 2
  | 76 => 2
  | 77 => 2
  | 78 => 2
  | 79 => 2
  | 80 => 2
  | 81 => 2
  | 82 => 2
  | 83 => 2
  | 84 => 2
  | 85 => 2
  | 86 => 2
  | 87 => 2
  | 88 => 2
  | 89 => 2
  | 90 => 2
  | 91 => 4
  | 92 => 2
  | 93 => 2
  | 94 => 2
  | 95 => 2
  | 96 => 2
  | 97 => 2
  | 98 => 2
  | _ => 2
private def orbitWord (x : Fin 100) : List (Fin 17) :=
  match x.val with
  | 0 => []
  | 1 => [11, 0]
  | 2 => []
  | 3 => [10, 2]
  | 4 => []
  | 5 => [6, 2]
  | 6 => [5, 2, 0]
  | 7 => [1, 3, 0]
  | 8 => [3, 2]
  | 9 => [0, 2]
  | 10 => [5, 0]
  | 11 => [4, 2]
  | 12 => [10, 1]
  | 13 => [8, 1]
  | 14 => [3]
  | 15 => [0]
  | 16 => [11, 2]
  | 17 => [15, 6, 1]
  | 18 => [10, 3]
  | 19 => [12, 3, 0]
  | 20 => [5]
  | 21 => [4, 0]
  | 22 => [3, 2]
  | 23 => [2, 3, 0]
  | 24 => [5, 3, 0]
  | 25 => [7, 1, 0]
  | 26 => [2, 0]
  | 27 => [1, 6]
  | 28 => [14, 0]
  | 29 => [7, 2, 0]
  | 30 => [1, 3]
  | 31 => [12, 1]
  | 32 => [3, 0]
  | 33 => [6, 3]
  | 34 => [4, 2]
  | 35 => [9, 4]
  | 36 => [10, 0]
  | 37 => [2, 2]
  | 38 => [7, 1, 0]
  | 39 => [9, 1]
  | 40 => [2]
  | 41 => [6, 3, 0]
  | 42 => [12, 4]
  | 43 => [5, 4]
  | 44 => [6, 0]
  | 45 => [12, 2, 0]
  | 46 => [2, 0]
  | 47 => [6, 1]
  | 48 => [6, 0]
  | 49 => [1, 0]
  | 50 => [12, 0]
  | 51 => [5, 0]
  | 52 => [4, 0]
  | 53 => [10, 3, 0]
  | 54 => [8, 3]
  | 55 => [11, 1]
  | 56 => [12, 2]
  | 57 => [10, 2, 0]
  | 58 => [12, 0]
  | 59 => [4]
  | 60 => [14, 4, 0]
  | 61 => [6, 1]
  | 62 => [13, 0]
  | 63 => [6]
  | 64 => [7, 4]
  | 65 => [14, 0]
  | 66 => [0]
  | 67 => [1, 1]
  | 68 => [8, 5]
  | 69 => [2]
  | 70 => [1]
  | 71 => [5, 3, 0]
  | 72 => [10, 5]
  | 73 => [12, 7, 0]
  | 74 => [8, 0]
  | 75 => [5, 2]
  | 76 => [3, 0]
  | 77 => [5, 8, 0]
  | 78 => [4, 1]
  | 79 => [1, 0]
  | 80 => [8, 9, 0]
  | 81 => [0, 6]
  | 82 => [15, 4]
  | 83 => [1, 4]
  | 84 => [0, 14, 0]
  | 85 => [16, 3, 0]
  | 86 => [9, 3]
  | 87 => [1]
  | 88 => [7, 0]
  | 89 => [1, 3, 1]
  | 90 => [4, 9, 0]
  | 91 => [10, 0]
  | 92 => [9, 1]
  | 93 => [4, 4]
  | 94 => [9, 0]
  | 95 => [3, 1]
  | 96 => [3, 3, 0]
  | 97 => [5, 3]
  | 98 => [2, 9, 0]
  | _ => [8, 2]
private theorem orbit_cover : ∀ x, evalWord gen1 (orbitWord x) (orbitBase x) = x := by
  apply allFin
  decide +kernel
private theorem orbit_bases : ∀ x, orbitBase x = 0 ∨ orbitBase x = 4 ∨ orbitBase x = 2 := by
  apply allFin
  decide +kernel

theorem perm_eq_one_of_centralizes (c : Equiv.Perm (Fin 100))
    (hc : ∀ g ∈ H1, c * g = g * c) : c = 1 := by
  have comm (g : Equiv.Perm (Fin 100)) (hg : g ∈ H1) (x : Fin 100) :
      c (g x) = g (c x) := congrArg (fun t : Equiv.Perm (Fin 100) => t x) (hc g hg)
  have h0 : c 0 = 0 := fixed1 _ (fun i => by
    rw [←comm _ (show gen1 i ∈ H1 from ⟨[i],by simp [evalWord]⟩), seeds_fixed1])
  have h4 : c 4 = 4 := by
    rcases fixed2 (c 4) (fun i => by
      rw [←comm _ (H2_le (show gen2 i ∈ H2 from ⟨[i],by simp [evalWord]⟩)),seeds_fixed2]) with hh | hh
    · have := c.injective (hh.trans h0.symm)
      contradiction
    · exact hh
  have h2 : c 2 = 2 := by
    rcases fixed3 (c 2) (fun i => by
      rw [←comm _ (H2_le (H3_le (show gen3 i ∈ H3 from ⟨[i],by simp [evalWord]⟩))),seeds_fixed3]) with hh | hh | hh
    · have := c.injective (hh.trans h0.symm)
      contradiction
    · have := c.injective (hh.trans h4.symm)
      contradiction
    · exact hh
  apply Equiv.ext
  intro x
  change c x = x
  calc
    c x = c (evalWord gen1 (orbitWord x) (orbitBase x)) := congrArg c (orbit_cover x).symm
    _ = evalWord gen1 (orbitWord x) (c (orbitBase x)) := comm _ ⟨orbitWord x,rfl⟩ _
    _ = evalWord gen1 (orbitWord x) (orbitBase x) := by
      rcases orbit_bases x with h | h | h <;> simp only [h,h0,h4,h2]
    _ = x := orbit_cover x

theorem centralizer_pointStabilizer_eq_bot : centralizer (pointStabilizer : Set Carrier) = ⊥ := by
  apply bot_unique
  intro c hc
  apply mem_bot.mpr
  apply Subtype.ext
  apply perm_eq_one_of_centralizes
  intro g hg
  obtain ⟨x,hx,hxg⟩ := (SmallIndex.pointStabilizer_map_inclusion.symm ▸ hg)
  subst g
  exact congrArg (fun y : Carrier => (y : Equiv.Perm (Fin 100))) ((hc x hx).symm)
end Sporadic.LeechRelated.HS.PointCentralizer

