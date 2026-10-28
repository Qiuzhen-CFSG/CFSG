module
public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.TorusCriterion
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Split-torus transfer in even-characteristic G₂

Reparametrizing the concrete split torus by `(a,b) ↦ (b²,ab)` diagonalizes
its Weyl reflection: `weylR` inverts `a` and fixes `b`.  When the split-torus
index is prime to an odd prime, two cyclic Sylow factors thus give the
inverted generators required by central-cover transfer.

This is one local input to Aschbacher–Smith I.1.3–I.1.4, printed pp.407–408
(PDF pp.418–419), and the multiplier calculation cited in GLS III §6.1.
It does not assert the nonsplit-torus or noncyclic Sylow-3 branches.
The concrete torus and Weyl maps are the licensed ATLAS ports; see
`LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section

open scoped CharTwo
open Atlas.G2
open PerfectCentralCovering

namespace Atlas.G2.MultiplierOrdinary.Nondefining

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def rootCoordinateMap : Fˣ × Fˣ →* Fˣ × Fˣ where
  toFun p := (p.2 ^ 2, p.1 * p.2)
  map_one' := by simp
  map_mul' p q := by
    apply Prod.ext
    · simp [pow_two, mul_left_comm, mul_comm]
    · simp [mul_left_comm, mul_comm]

def rootTorusHom : Fˣ × Fˣ →* Model F :=
  torusHom.comp (rootCoordinateMap (F := F))

omit [Finite F] in theorem rootCoordinateMap_injective : Function.Injective (rootCoordinateMap (F := F)) := by
  intro p q h
  have hd : p.2 = q.2 := by
    apply Units.ext
    apply CharTwo.sq_inj.mp
    exact congrArg Units.val (congrArg Prod.fst h)
  apply Prod.ext
  · have hh := congrArg Prod.snd h
    dsimp [rootCoordinateMap] at hh
    rw [hd] at hh
    apply Units.ext
    have hh' := congrArg Units.val hh
    exact mul_right_cancel₀ (Units.ne_zero q.2) hh'
  · exact hd

omit [Finite F] in theorem rootTorusHom_injective : Function.Injective (rootTorusHom (F := F)) := by
  intro p q h
  apply rootCoordinateMap_injective (F := F)
  change torusHom (rootCoordinateMap p) = torusHom (rootCoordinateMap q) at h
  exact torusHom_injective h

theorem rootCoordinateMap_surjective : Function.Surjective (rootCoordinateMap (F := F)) := by
  exact (Finite.injective_iff_surjective.mp (rootCoordinateMap_injective (F := F)))

theorem rootTorusHom_range : (rootTorusHom (F := F)).range = splitTorus (K := F) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨rootCoordinateMap p, rfl⟩
  · rintro ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := rootCoordinateMap_surjective (F := F) p
    refine ⟨q, ?_⟩
    change torusHom (rootCoordinateMap q) = torusHom p
    rw [hq]

omit [Finite F] in private theorem weylR_torus_formula (l m : Fˣ) :
    weylR * torus l m * weylR⁻¹ = torus l (l*m⁻¹) := by
  rw [weylR_inverse]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,
      weylR,weylREquiv,weylRLinear,weylRApply]
  simp [mul_comm]

omit [Finite F] in theorem weylR_rootTorus (a b : Fˣ) :
    weylR * rootTorusHom (a,b) * weylR⁻¹ = rootTorusHom (a⁻¹,b) := by
  change weylR * torus (b ^ 2) (a * b) * weylR⁻¹ = torus (b ^ 2) (a⁻¹ * b)
  rw [weylR_torus_formula]
  congr 1
  apply Units.ext
  simp [pow_two, mul_assoc, mul_comm]

/-- Transfer for the literal split torus in the concrete G₂ model. -/
theorem not_dvd_card_universal_kernel_of_split_torus
    (hF : 4 < Nat.card F) {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hindex : ¬ r ∣ (splitTorus (K := F)).index) :
    ¬ r ∣ Nat.card (PerfectCentralCovering.universalProjection (Model F)).ker := by
  rw [← rootTorusHom_range] at hindex
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  let ι : Fˣ × Fˣ →* Model F := rootTorusHom (F := F)
  have hι : Function.Injective ι := rootTorusHom_injective (F := F)
  obtain ⟨R : Sylow r Fˣ⟩ := Sylow.nonempty (p := r) (G := Fˣ)
  let D : Subgroup (Fˣ × Fˣ) := (R : Subgroup Fˣ).prod (R : Subgroup Fˣ)
  have hDp : IsPGroup r D := by
    obtain ⟨m, hm⟩ := R.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := m+m)
    rw [Nat.card_congr (Subgroup.prodEquiv (R : Subgroup Fˣ) (R : Subgroup Fˣ)).toEquiv,
      Nat.card_prod, hm, pow_add]
  let Q : Subgroup (Model F) := D.map ι
  have hQp : IsPGroup r Q := hDp.map ι
  have hQi : ¬ r ∣ Q.index := by
    rw [Subgroup.index_map_of_injective _ hι, Subgroup.index_prod]
    exact (Fact.out : r.Prime).not_dvd_mul
      ((Fact.out : r.Prime).not_dvd_mul R.not_dvd_index R.not_dvd_index) hindex
  let P : Sylow r (Model F) := hQp.toSylow hQi
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := R)
  have hx : ι ((a : Fˣ),1) ∈ Q :=
    ⟨((a : Fˣ),1), ⟨a.property, (R : Subgroup Fˣ).one_mem⟩, rfl⟩
  have hy : ι (1,(a : Fˣ)) ∈ Q :=
    ⟨(1,(a : Fˣ)), ⟨(R : Subgroup Fˣ).one_mem, a.property⟩, rfl⟩
  have hP : PerfectCentralCovering.InvertedGenerators (P : Subgroup (Model F)) := by
    refine {
      left := ⟨ι ((a : Fˣ),1), hx⟩
      right := ⟨ι (1,(a : Fˣ)), hy⟩
      commute := (Commute.all ((a : Fˣ),1) (1,(a : Fˣ))).map ι
      normalForm := ?_
      inverter := weylR
      invert_left := by
        calc
          _ = rootTorusHom (a⁻¹,1) := weylR_rootTorus (F := F) a 1
          _ = (ι (a,1))⁻¹ := by
            change rootTorusHom (((a : Fˣ)⁻¹),1) = (rootTorusHom ((a : Fˣ),1))⁻¹
            simpa only [Prod.inv_mk, inv_one] using
              (map_inv (rootTorusHom (F := F)) ((a : Fˣ), 1))
      fix_right := by simpa using weylR_rootTorus (F := F) 1 a }
    intro z
    obtain ⟨⟨c,d⟩, hcd, he⟩ := z.property
    change c ∈ (R : Subgroup Fˣ) ∧ d ∈ (R : Subgroup Fˣ) at hcd
    obtain ⟨i, hi⟩ := ha ⟨c, hcd.1⟩
    obtain ⟨j, hj⟩ := ha ⟨d, hcd.2⟩
    refine ⟨i, j, ?_⟩
    change (z : Model F) = ι ((a : Fˣ),1)^i * ι (1,(a : Fˣ))^j
    rw [← he, ← map_zpow, ← map_zpow, ← map_mul]
    apply congrArg ι
    apply Prod.ext
    · simpa using (congrArg (fun x : R => (x : Fˣ)) hi).symm
    · simpa using (congrArg (fun x : R => (x : Fˣ)) hj).symm
  exact PerfectCentralCovering.not_dvd_card_kernel_of_inverted_sylow hr2 P hP
    (universalProjection (Model F)) (universalProjection_surjective _)
    (universalProjection_ker_le_center _)

omit [CharP F 2] in
/-- The exact index of the split torus. -/
theorem splitTorus_index : (splitTorus (K := F)).index =
    Nat.card F ^ 6 * (Nat.card F + 1)^2 * (Nat.card F^4 + Nat.card F^2 + 1) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hf2 : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
  have hf6 : Nat.card F ^ 6 - 1 =
      (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 + Nat.card F ^ 2 + 1) := by
    simpa [Finset.sum_range_succ, ← pow_mul, mul_comm, add_comm, add_left_comm, add_assoc] using
      (geom_sum_mul_of_one_le (Nat.one_le_pow 2 (Nat.card F) hq.le) 3).symm
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (show 0 < Nat.card F - 1 by omega) 2)
  rw [← card_splitTorus, Subgroup.card_mul_index, card_Model, hf6, hf2, card_splitTorus]
  ring

omit [CharP F 2] in
/-- A prime dividing `q − 1`, other than 2 or 3, does not divide the split-torus index. -/
theorem not_dvd_splitTorus_index {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hd : r ∣ Nat.card F - 1) :
    ¬ r ∣ (splitTorus (K := F)).index := by
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hnot2 : ¬ r ∣ 2 := fun h =>
    hr2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hr.ne_one)
  have hnot3 : ¬ r ∣ 3 := fun h =>
    hr3 ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hr.ne_one)
  have hnotq : ¬ r ∣ Nat.card F := by
    intro h
    have hh := Nat.dvd_sub h hd
    rw [Nat.sub_sub_self hq] at hh
    exact hr.not_dvd_one hh
  have hplus : ¬ r ∣ Nat.card F + 1 := by
    intro h
    have hh := Nat.dvd_sub h hd
    rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at hh
    exact hnot2 hh
  have hd2 : r ∣ Nat.card F ^ 2 - 1 := hd.trans (Nat.sub_one_dvd_pow_sub_one _ _)
  have hd4 : r ∣ Nat.card F ^ 4 - 1 := hd.trans (Nat.sub_one_dvd_pow_sub_one _ _)
  have hquartic : ¬ r ∣ Nat.card F ^ 4 + Nat.card F ^ 2 + 1 := by
    intro h
    have hh := Nat.dvd_sub h (dvd_add hd4 hd2)
    rw [show Nat.card F ^ 4 + Nat.card F ^ 2 + 1 -
        ((Nat.card F ^ 4 - 1) + (Nat.card F ^ 2 - 1)) = 3 by
      have := Nat.one_le_pow 2 (Nat.card F) hq
      have := Nat.one_le_pow 4 (Nat.card F) hq
      omega] at hh
    exact hnot3 hh
  rw [splitTorus_index]
  exact hr.not_dvd_mul
    (hr.not_dvd_mul (fun h => hnotq (hr.dvd_of_dvd_pow h))
      (fun h => hplus (hr.dvd_of_dvd_pow h))) hquartic

/-- The split-torus branch of the even-characteristic ordinary multiplier
calculation, with its index premise discharged by the exact group order. -/
theorem not_dvd_card_universal_kernel_of_dvd_sub_one
    (hF : 4 < Nat.card F) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hd : r ∣ Nat.card F - 1) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker :=
  not_dvd_card_universal_kernel_of_split_torus hF hr2
    (not_dvd_splitTorus_index Fact.out hr2 hr3 hd)

/-- Odd primes absent from the group order are excluded by the same transfer. -/
theorem not_dvd_card_universal_kernel_of_not_dvd_model
    (hF : 4 < Nat.card F) {r : ℕ} [Fact r.Prime]
    (hr2 : r ≠ 2) (hr : ¬ r ∣ Nat.card (Model F)) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker :=
  not_dvd_card_universal_kernel_of_split_torus hF hr2
    (fun h => hr (h.trans (splitTorus (K := F)).index_dvd_card))

end Atlas.G2.MultiplierOrdinary.Nondefining

end
