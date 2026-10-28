module

public import Theory.SpecificGroups.Suzuki.OddTorusContainment

/-!
# The Sylow seven- and thirteen-subgroups of Sz(8)

The order formula gives prime order for the two specified Sylow subgroups.
The proved odd-torus containment puts each in a cyclic torus of order
7, 13 or 5; divisibility forces equality. The partition centralizer theorem
then makes each Sylow subgroup self-centralizing. The final statement
transports these facts through an actual matrix-model isomorphism.

Source: Huppert–Blackburn III, XI.3.3 and XI.3.10; consumed in
Aschbacher–Smith, J.2.10, printed p.438 (PDF p.449), refs/quasithin.pdf.
These are intrinsic group calculations; the outer cubic action is separate.
-/

@[expose] public section
open Subgroup
namespace BenderSuzuki.MatrixGroups

/-- The two odd Sylow orders consumed by J.2.10. -/
theorem suzuki_eight_sylow_odd_card {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p (SuzukiMatrixGroup 1)) :
    Nat.card Y = p := by
  have hcard : Nat.card (SuzukiMatrixGroup 1) = 29120 := by
    rw [suzukiMatrixGroup_card 1 (by decide)]
    norm_num
  rw [Y.card_eq_multiplicity, hcard]
  rcases hp with rfl | rfl
  · have hf := Nat.factorization_eq_of_coprime_left (p := 7)
      (by decide : Nat.Coprime 7 4160)
      ((Nat.mem_primeFactorsList_iff_dvd (by decide) (by decide)).mpr dvd_rfl)
    change (Nat.factorization 29120) 7 = (Nat.factorization 7) 7 at hf
    rw [hf, (by decide : Nat.Prime 7).factorization_self, pow_one]
  · have hf := Nat.factorization_eq_of_coprime_left (p := 13)
      (by decide : Nat.Coprime 13 2240)
      ((Nat.mem_primeFactorsList_iff_dvd (by decide) (by decide)).mpr dvd_rfl)
    change (Nat.factorization 29120) 13 = (Nat.factorization 13) 13 at hf
    rw [hf, (by decide : Nat.Prime 13).factorization_self, pow_one]

/-- Each specified Sylow subgroup is an actual maximal odd torus. -/
theorem suzuki_eight_sylow_odd_torus {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p (SuzukiMatrixGroup 1)) :
    IsSuzukiMaximalOddTorus 1 Y := by
  have hcard := suzuki_eight_sylow_odd_card hp Y
  have hodd : Odd (Nat.card Y) := by
    rw [hcard]
    rcases hp with rfl | rfl <;> decide
  obtain ⟨U, hYU, hU⟩ :=
    suzukiOddSubgroup_exists_torus (m := 1) (by decide) (Y : Subgroup _) hodd
  have hd : p ∣ Nat.card U := hcard ▸ card_dvd_of_le hYU
  have hc := hU.card_eq (by decide)
  norm_num at hc
  have he : Nat.card U = p := by
    rcases hp with rfl | rfl <;> omega
  have hYeq : (Y : Subgroup (SuzukiMatrixGroup 1)) = U :=
    eq_of_le_of_card_ge hYU (by rw [hcard, he])
  exact hYeq.symm ▸ hU

/-- The intrinsic centralizer of either specified Sylow subgroup is itself. -/
theorem suzuki_eight_sylow_odd_centralizer {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p (SuzukiMatrixGroup 1)) :
    centralizer (Y : Set (SuzukiMatrixGroup 1)) = Y := by
  have hY := suzuki_eight_sylow_odd_torus hp Y
  let := hY.isCyclic (by decide)
  have hne : (Y : Subgroup (SuzukiMatrixGroup 1)) ≠ ⊥ := by
    intro he
    have hc := suzuki_eight_sylow_odd_card hp Y
    have hone := (eq_bot_iff_card (Y : Subgroup (SuzukiMatrixGroup 1))).mp he
    rw [hc] at hone
    exact (Fact.out : p.Prime).ne_one hone
  obtain ⟨x, hx, hx1⟩ := (Y : Subgroup (SuzukiMatrixGroup 1)).bot_or_exists_ne_one.resolve_left hne
  exact le_antisymm
    ((centralizer_le (Set.singleton_subset_iff.mpr hx)).trans
      (hY.partition.centralizer_le (by decide) hx hx1))
    (le_centralizer (Y : Subgroup (SuzukiMatrixGroup 1)))

/-- Transport cardinality and the intrinsic centralizer through a genuine model isomorphism. -/
theorem suzuki_eight_sylow_odd_model {H : Type*} [Group H] [Finite H]
    (e : H ≃* SuzukiMatrixGroup 1) {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p H) :
    Nat.card Y = p ∧ centralizer (Y : Set H) = Y := by
  let Q := Y.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card Y = p := by
    have h := suzuki_eight_sylow_odd_card hp Q
    change Nat.card ((Y : Subgroup H).map e.toMonoidHom) = p at h
    rwa [card_map_of_injective e.injective] at h
  refine ⟨hcard, ?_⟩
  have hQ := suzuki_eight_sylow_odd_centralizer hp Q
  apply le_antisymm
  · intro x hx
    have hxe : e x ∈ centralizer (Q : Set (SuzukiMatrixGroup 1)) := by
      rw [mem_centralizer_iff]
      rintro y ⟨z, hz, rfl⟩
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
        congrArg e (mem_centralizer_iff.mp hx z hz)
    rw [hQ] at hxe
    obtain ⟨z, hz, he⟩ := hxe
    exact e.injective he ▸ hz
  · let := isCyclic_of_prime_card hcard
    exact le_centralizer (Y : Subgroup H)

end BenderSuzuki.MatrixGroups
