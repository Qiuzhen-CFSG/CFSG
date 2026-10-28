module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.Covered
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.AlignFactors
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.ThompsonComparison.FixedPoints
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.NormalizedSupCard
public import Stellmacher.ElementaryAbelianMaxDefs

/-!
# The Thompson comparison for the covered Suzuki pair

Let A be an elementary abelian subgroup of largest order in Tᵥ, and A₀ its
factor stabilizer. The explicit action hypothesis says that square-one
elements stabilizing K centralize Ω₁(T₀). Hence A₀Ω₁(T₀) is elementary.
If A contains a swapping element u, then |A:A₀| = 2, whereas the fixed-point
count gives |Ω₁(T₀):C_Ω₁(T₀)(u)| ≥ q ≥ 8. Comparing A with A₀Ω₁(T₀)
contradicts maximality. Every such A therefore stabilizes K, and the same
action hypothesis proves that J(Tᵥ) centralizes Ω₁(T₀).

The final theorem uses the actual covered omega and its full quotient
image, including the Sz(8) central covers. An unaligned version chooses
compatible factor markings with PairFactors.exists_aligned. The genuine
earlier elementary-center and involution-lifting inputs, and the pointwise
factor-stabilizer action input, remain explicit. OmegaGeometry's source
assembly discharges them; no maximal-subgroup centralization is assumed.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 / PDF p.944;
the elementary Thompson convention is B.2.2–4, printed pp.74–75.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
variable {G : Type*} [Group G] {T K : Subgroup G} {v : G}
namespace PairFactors
variable {d : Marking T K v} (c : PairFactors d)

variable [Finite G]

include c in
/-- A maximum elementary subgroup cannot exchange the two components:
its factor stabilizer joined with omega would be larger. -/
theorem maxElementary_le_normalizer_of_stable_involutions
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (omega T K v)]
    (himage : ((omega T K v).subgroupOf (orbit T K v)).map d.quotientMap =
      (omegaOneAmbient (SuzukiRootSubgroup d.parameter)).prod
        (omegaOneAmbient (SuzukiRootSubgroup d.parameter)))
    (hstable : ∀ x ∈ Tv T v, x ^ 2 = 1 → x ∈ normalizer (K : Set G) →
      x ∈ centralizer (omega T K v : Set G))
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (Tv T v)) :
    A ≤ normalizer (K : Set G) := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  intro x hx
  by_contra hxN
  let A₀ := A ⊓ normalizer (K : Set G)
  let I := omega T K v ⊓ A₀
  let F := omega T K v ⊓ centralizer ({x} : Set G)
  have hA₀C : A₀ ≤ centralizer (omega T K v : Set G) := by
    intro a ha
    exact hstable a (hA.1 ha.1) (elemPow_eq_one_of_isElementaryAbelian _ ha.1) ha.2
  let _ : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.of_le (show A₀ ≤ A from inf_le_left)
  have hsup : IsElementaryAbelian 2 (omega T K v ⊔ A₀ : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hA₀C
  have hmax : Nat.card (omega T K v ⊔ A₀ : Subgroup G) ≤ Nat.card A :=
    hA.2.2 _ (sup_le ((omegaOneAmbient_le _).trans inf_le_left)
      (inf_le_left.trans hA.1)) hsup
  have hindex := c.stabilizer_relIndex A hA.1 ⟨x, hx⟩ hxN
  have hAcard : Nat.card A₀ * 2 = Nat.card A := by
    have h := relIndex_mul_relIndex (⊥ : Subgroup G) A₀ A bot_le inf_le_left
    simpa only [relIndex_bot_left, A₀, inf_comm A, inf_relIndex_right, hindex] using h
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes (omega T K v) A₀
    (hA₀C.trans (centralizer_le_normalizer _))
  have hupper : Nat.card (omega T K v) ≤ 2 * Nat.card I := by
    apply Nat.le_of_mul_le_mul_right (c := Nat.card A₀) ?_ Nat.card_pos
    calc
      Nat.card (omega T K v) * Nat.card A₀ =
          Nat.card I * Nat.card (omega T K v ⊔ A₀ : Subgroup G) := hprod
      _ ≤ Nat.card I * Nat.card A := Nat.mul_le_mul_left _ hmax
      _ = (2 * Nat.card I) * Nat.card A₀ := by rw [← hAcard]; ac_rfl
  have hIF : I ≤ F := by
    intro y hy
    refine ⟨hy.1, mem_centralizer_singleton_iff.mpr ?_⟩
    exact ((le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative A)) hy.2.1 x hx).symm
  have hlower : 2 ^ (2 * d.parameter + 1) * Nat.card I ≤ Nat.card (omega T K v) :=
    (Nat.mul_le_mul_left _ (card_le_of_le hIF)).trans
      (c.omega_fixed_card_bound hKG hK himage ⟨x, hA.1 hx⟩ hxN)
  have hq : 2 ^ (2 * d.parameter + 1) ≤ 2 :=
    Nat.le_of_mul_le_mul_right (hlower.trans hupper) Nat.card_pos
  have hlarge : 2 ^ 3 ≤ 2 ^ (2 * d.parameter + 1) :=
    Nat.pow_le_pow_right (by decide) (by have := d.positive; omega)
  norm_num at hlarge
  omega

include c in
/-- The Thompson centralization for the aligned covered pair. The only action
input is pointwise centralization by square-one factor stabilizers. -/
theorem thompson_le_centralizer_of_stable_involutions
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter))
    (hstable : ∀ x ∈ Tv T v, x ^ 2 = 1 → x ∈ normalizer (K : Set G) →
      x ∈ centralizer (omega T K v : Set G)) :
    elementaryAbelianMaxJ (Tv T v) ≤ centralizer (omega T K v : Set G) := by
  let _ := c.omega_elementary P hP hKG hK hlift ha
  have himage := c.omega_image P hP hKG hK hlift ha
  apply sSup_le
  intro A hA
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have hAN := c.maxElementary_le_normalizer_of_stable_involutions hKG hK himage hstable A hA
  intro x hx
  exact hstable x (hA.1 hx) (elemPow_eq_one_of_isElementaryAbelian _ hx) (hAN hx)

include c in
/-- Choose compatible aligned factors and apply the covered-pair comparison. -/
theorem thompson_le_centralizer_of_stable_involutions_unaligned
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (hstable : ∀ x ∈ Tv T v, x ^ 2 = 1 → x ∈ normalizer (K : Set G) →
      x ∈ centralizer (omega T K v : Set G)) :
    elementaryAbelianMaxJ (Tv T v) ≤ centralizer (omega T K v : Set G) := by
  obtain ⟨d', c', _, _, ha⟩ := c.exists_aligned P hP hKG
  exact c'.thompson_le_centralizer_of_stable_involutions P hP hKG hK hlift ha hstable

end PairFactors
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
