module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Coverage.FiniteCatalogue
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.Profiles.Coverage.UpperCenter.CommutatorTests

/-!
# The third upper center is contained in the last four coordinates

For each initial coordinate, `CommutatorTests` supplies a quotient in which
its generator fails to centralize a chosen test generator, while the whole
next tail centralizes that test. The two-coset decomposition of the tail
therefore excludes this coordinate from any subgroup centralizing that test.

Applying this argument successively to the defining commutator condition for
the upper central series gives `Z₁ ≤ tail 20`, `Z₂ ≤ tail 19`, and
`Z₃ ≤ tail 17`. The last tail is exactly the previously constructed `upperCube`.
The order hypothesis is used only for normal-form uniqueness and separation.
No membership hypothesis for the desired center, and no enumeration of all
normal forms, is assumed.

Source: the literal presentation and candidate third center recorded in
`SylowNormalEights/source/pc.json` and `profile-data.json`; see their README
for conventions and provenance. Context: Kleidman–Wilson (1988), pp. 484–510;
Aschbacher–Smith, `refs/quasithin.pdf`, printed p. 511/PDF p. 528.
-/

public section

open scoped commutatorElement
namespace Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.Coverage
namespace UpperCenter

private def centralizerMod (n : Fin 22) (j : Fin 21) : Subgroup Carrier :=
  (Subgroup.centralizer {(QuotientGroup.mk' (tail n)) (generator j)}).comap
    (QuotientGroup.mk' (tail n))

private lemma mem_centralizerMod (n : Fin 22) (j : Fin 21) (x : Carrier) :
    x ∈ centralizerMod n j ↔ ⁅x, generator j⁆ ∈ tail n := by
  change (QuotientGroup.mk' (tail n)) x ∈ Subgroup.centralizer
    {(QuotientGroup.mk' (tail n)) (generator j)} ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff, ← commutatorElement_eq_one_iff_mul_comm,
    ← map_commutatorElement]
  exact QuotientGroup.eq_one_iff _

private lemma peel (hcard : Nat.card Carrier = 2 ^ 21) (H : Subgroup Carrier) (i : Fin 20)
    (hle : H ≤ tail i.castSucc.castSucc)
    (hc : ∀ x ∈ H, ⁅x, generator (test i)⁆ ∈ tail (pivot i).succ) :
    H ≤ tail i.castSucc.succ := by
  let K := centralizerMod (pivot i).succ (test i)
  have hH : H ≤ K := fun x hx => (mem_centralizerMod _ _ x).mpr (hc x hx)
  have hT : tail i.castSucc.succ ≤ K := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hk := (mem_suffix _ k).mp hk
    exact (mem_centralizerMod _ _ _).mpr (later_commutator_mem i k hk)
  intro x hx
  rcases tail_two_cosets i.castSucc (hle hx) with ht | ⟨y, hy, he⟩
  · exact ht
  · exfalso
    have hi : generator i.castSucc ∈ K :=
      (K.mul_mem_cancel_right (hT hy)).mp (he ▸ hH hx)
    exact self_commutator_not_mem hcard i ((mem_centralizerMod _ _ _).mp hi)

private lemma bound (hcard : Nat.card Carrier = 2 ^ 21) (H : Subgroup Carrier) (t : Fin 21)
    (hc : ∀ i : Fin 20, i.val < t.val →
      ∀ x ∈ H, ⁅x, generator (test i)⁆ ∈ tail (pivot i).succ) :
    H ≤ tail t.castSucc := by
  have hb (n : ℕ) (hn : n ≤ t.val) :
      H ≤ tail ⟨n, by have := t.isLt; omega⟩ := by
    induction n with
    | zero =>
      change H ≤ tail 0
      rw [tail_zero]
      exact le_top
    | succ n ih =>
      let i : Fin 20 := ⟨n, by have := t.isLt; omega⟩
      exact peel hcard H i (ih (by omega)) (hc i (by dsimp [i]; omega))
  exact hb t.val le_rfl

private lemma center_le (hcard : Nat.card Carrier = 2 ^ 21) :
    Subgroup.upperCentralSeries Carrier 1 ≤ tail 20 := by
  apply bound hcard _ 20
  intro i hi x hx
  have hc := Subgroup.mem_upperCentralSeries_succ_iff.mp hx (generator (test i))
  exact (show (⊥ : Subgroup Carrier) ≤ tail (pivot i).succ from bot_le) hc

private lemma second_center_le (hcard : Nat.card Carrier = 2 ^ 21) :
    Subgroup.upperCentralSeries Carrier 2 ≤ tail 19 := by
  apply bound hcard _ 19
  intro i hi x hx
  exact tail_antitone (show (pivot i).succ ≤ (20 : Fin 22) from pivot_lt_twenty i hi)
    (center_le hcard (Subgroup.mem_upperCentralSeries_succ_iff.mp hx (generator (test i))))

private lemma third_center_le (hcard : Nat.card Carrier = 2 ^ 21) :
    Subgroup.upperCentralSeries Carrier 3 ≤ tail 17 := by
  apply bound hcard _ 17
  intro i hi x hx
  exact tail_antitone (show (pivot i).succ ≤ (19 : Fin 22) from pivot_lt_nineteen i hi)
    (second_center_le hcard (Subgroup.mem_upperCentralSeries_succ_iff.mp hx (generator (test i))))

private lemma tail_seventeen : tail 17 = upperCube := by
  rw [upperCube_eq_closure]
  rfl

end UpperCenter

theorem upperCentralSeries_le_upperCube (hcard : Nat.card Carrier = 2 ^ 21) :
    Subgroup.upperCentralSeries Carrier 3 ≤ upperCube := by
  rw [← UpperCenter.tail_seventeen]
  exact UpperCenter.third_center_le hcard

end Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles.Coverage
