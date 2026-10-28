module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.MarkedContaining
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.Mathieu.M24.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Small containing carriers excluded by the marked prime rank

The marked image has p-rank at least two for p > 3. Thus its containing
component has order divisible by p². The concrete orders exclude all
alternating rows, the five Mathieu rows, J₁, the binary linear groups of
degrees three through five, and the two small derived rank-two groups.
The alternating and Mathieu central three-covers are treated using their
actual central quotient and center order.

Only the already proved carrier orders are used; no simplicity or
representation certification is added. These are containing-model
exclusions for Aschbacher–Smith A.3.12, pp.47–48, in 1.3.8, p.513.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 Section02.LocalModels ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {p r : ℕ} {L : Subgroup G} {T : Sylow 2 G}
variable {C : Subgroup (radicalCore p L T)} {K : Subgroup G}

private def smallOrderBound : ℕ := 2 ^ 11 * 3 ^ 3 * 5 * 7 * 11 * 19 * 23 * 31

private theorem large_prime_square_not_dvd {p : ℕ} (hp : p.Prime) (hl : 3 < p) :
    ¬ p ^ 2 ∣ smallOrderBound := by
  intro hd
  have hpd : p ∣ smallOrderBound :=
    (show p ∣ p ^ 2 from dvd_pow_self _ (by decide)).trans hd
  change p ∣ 2 ^ 11 * 3 ^ 3 * 5 * 7 * 11 * 19 * 23 * 31 at hpd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31), or_assoc] at hpd
  rcases hpd with hd' | hd' | rfl | rfl | rfl | rfl | rfl | rfl
  · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two hd'
    omega
  · have := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_three hd'
    omega
  all_goals norm_num [smallOrderBound] at hd

private theorem SourceData.not_small_order (h : SourceData 𝒦 p r L T C K)
    (hc : Nat.card (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) ∣ smallOrderBound) : False := by
  let : Fact p.Prime := ⟨h.prime⟩
  have hu := primeRank_le_one_of_square_not_dvd
    (fun hd => large_prime_square_not_dvd h.prime h.large (hd.trans hc))
  have hl := h.containing_image_rank
  omega

private theorem three_cover_card {A : Type*} [Group A] [Finite A]
    {M : Type} [Group M] (h : IsThreeCover A M) : Nat.card A = 3 * Nat.card M := by
  have hz : Nat.card (center A) = 3 := by
    rw [Nat.card_congr h.2.1.some.toEquiv]
    simp
  calc
    Nat.card A = Nat.card (center A) * Nat.card (A ⧸ center A) := by
      rw [← index_eq_card, card_mul_index]
    _ = 3 * Nat.card M := by rw [hz, Nat.card_congr h.2.2.some.toEquiv]

/-- Every alternating carrier in the full Theorem C range is excluded. -/
theorem SourceData.containing_not_alternating (h : SourceData 𝒦 p r L T C K)
    {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 8) :
    ¬ IsAlternating (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) n := by
  rintro ⟨e⟩
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  apply h.not_small_order
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  obtain ⟨hl, hu⟩ := hn
  interval_cases n <;> norm_num [Nat.factorial, smallOrderBound]

/-- The actual central three-covers of A₆ and A₇ are excluded too. -/
theorem SourceData.containing_not_alternating_cover (h : SourceData 𝒦 p r L T C K)
    {n : ℕ} (hn : n = 6 ∨ n = 7) :
    ¬ IsAlternatingCover (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) n := by
  intro hm
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  apply h.not_small_order
  rw [three_cover_card hm, nat_card_alternatingGroup]
  rcases hn with rfl | rfl <;> norm_num [Nat.factorial, smallOrderBound]

/-- No Mathieu containing carrier in Theorem C has the marked prime rank. -/
theorem SourceData.containing_sporadic_name (h : SourceData 𝒦 p r L T C K)
    (name : SporadicName) (hne : name ≠ .j3)
    (hm : Nonempty (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G)) ≃* name.Carrier)) :
    name = .j2 ∨ name = .hs ∨ name = .ru ∨ name = .he ∨ name = .j4 := by
  obtain ⟨e⟩ := hm
  cases name with
  | m11 =>
    exfalso
    apply h.not_small_order
    rw [Nat.card_congr e.toEquiv]
    change Nat.card Sporadic.Mathieu.M11 ∣ smallOrderBound
    rw [Sporadic.Mathieu.m11_order]
    norm_num [smallOrderBound]
  | m12 =>
    exfalso
    apply h.not_small_order
    rw [Nat.card_congr e.toEquiv]
    change Nat.card Sporadic.Mathieu.M12 ∣ smallOrderBound
    rw [Sporadic.Mathieu.m12_order]
    norm_num [smallOrderBound]
  | m22 =>
    exfalso
    apply h.not_small_order
    rw [Nat.card_congr e.toEquiv]
    change Nat.card Sporadic.Mathieu.M22 ∣ smallOrderBound
    rw [Sporadic.Mathieu.m22_order]
    norm_num [smallOrderBound]
  | m23 =>
    exfalso
    apply h.not_small_order
    rw [Nat.card_congr e.toEquiv]
    change Nat.card Sporadic.Mathieu.M23 ∣ smallOrderBound
    rw [Sporadic.Mathieu.m23_order]
    norm_num [smallOrderBound]
  | m24 =>
    exfalso
    apply h.not_small_order
    rw [Nat.card_congr e.toEquiv]
    change Nat.card Sporadic.Mathieu.M24 ∣ smallOrderBound
    rw [Sporadic.Mathieu.m24_order]
    norm_num [smallOrderBound]
  | j3 => exact (hne rfl).elim
  | j2 | hs | ru | he | j4 => simp

/-- The separate J₁ entry of the genuine catalogue is excluded. -/
theorem SourceData.containing_not_janko_one (h : SourceData 𝒦 p r L T C K) :
    ¬ Nonempty (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G)) ≃* Janko1.Model) := by
  rintro ⟨e⟩
  apply h.not_small_order
  rw [Nat.card_congr e.toEquiv, Janko1.card_model]
  norm_num [smallOrderBound]

/-- The actual Mathieu central three-cover is excluded using its center. -/
theorem SourceData.containing_not_mathieu_cover (h : SourceData 𝒦 p r L T C K) :
    ¬ IsM22Cover (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) := by
  intro hm
  apply h.not_small_order
  rw [three_cover_card hm, Sporadic.Mathieu.m22_order]
  norm_num [smallOrderBound]

/-- The small binary linear orders exclude degrees three, four and five. -/
theorem SourceData.containing_not_small_binary_linear (h : SourceData 𝒦 p r L T C K)
    {n : ℕ} (hn : 3 ≤ n ∧ n ≤ 5) :
    ¬ ClassicalGroup.IsPSL (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) n 2 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let b := (e.trans (Atlas.fieldEquivPSL n a)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < n))
  apply h.not_small_order
  rw [Nat.card_congr b.toEquiv, BinaryLinear.card_SL]
  obtain ⟨hl, hu⟩ := hn
  interval_cases n <;> norm_num [BinaryLinear.order, Fin.prod_univ_succ, smallOrderBound]

/-- The small derived symplectic carrier is its actual A₆ model. -/
theorem SourceData.containing_not_symplectic_derived (h : SourceData 𝒦 p r L T C K) :
    ¬ Nonempty (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G)) ≃*
      _root_.commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  rintro ⟨e⟩
  exact h.containing_not_alternating (by omega : 5 ≤ 6 ∧ 6 ≤ 8)
    ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩

/-- The literal derived G₂(2) carrier has no large-prime square in its order. -/
theorem SourceData.containing_not_g2_derived (h : SourceData 𝒦 p r L T C K) :
    ¬ Nonempty (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G)) ≃*
      _root_.commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨e⟩
  apply h.not_small_order
  rw [Nat.card_congr e.toEquiv, Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
  norm_num [smallOrderBound]

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
