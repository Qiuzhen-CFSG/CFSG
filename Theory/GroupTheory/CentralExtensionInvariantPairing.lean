module

public import Theory.GroupTheory.ClassTwoCommutator
public import Theory.GroupTheory.CyclicNormRetraction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Invariant commutator pairings in central double extensions

In a group of class at most two, the central commutator is multiplicative in
both variables. It descends through any central kernel using the literal
surjective homomorphism. Compose it with an invariant retraction of the center
onto a kernel of order two. If the induced base action admits no invariant
binary pairing, this retraction kills the derived group, so its kernel cannot
lie in the derived group.

The retraction is the cyclic norm for an odd-period actor that fixes the kernel
and acts without nonidentity fixed points on the base center. This is the local
obstruction in the direct Sylow-center proof of GLS4, Chapter 4, Lemma 2.8(c).
The concrete torus actions and their binary weight calculation remain inputs.
-/

namespace CentralExtension
open Subgroup
open scoped commutatorElement IsMulCommutative
variable {S T C : Type*} [Group S] [Group T] [CommGroup C]

public theorem exists_descended_pairing
    (f : S →* T) (hf : Function.Surjective f) (b : S →* (S →* C))
    (hl : ∀ x ∈ f.ker, b x = 1) (hr : ∀ x, f.ker ≤ (b x).ker) :
    ∃ c : T →* (T →* C), ∀ x y, c (f x) (f y) = b x y := by
  let row (x : S) : T →* C := f.liftOfSurjective hf ⟨b x, hr x⟩
  have hrow (x y : S) : row x (f y) = b x y :=
    f.liftOfRightInverse_comp_apply _ _ _ y
  let rows : S →* (T →* C) := {
    toFun := row
    map_one' := by
      ext t
      obtain ⟨y, rfl⟩ := hf t
      rw [hrow, map_one]
      rfl
    map_mul' := by
      intro x y
      ext t
      obtain ⟨z, rfl⟩ := hf t
      change row (x * y) (f z) = row x (f z) * row y (f z)
      rw [hrow, hrow, hrow, map_mul]
      rfl }
  have hker : f.ker ≤ rows.ker := by
    intro x hx
    apply MonoidHom.ext
    intro t
    obtain ⟨y, rfl⟩ := hf t
    change row x (f y) = 1
    rw [hrow, hl x hx]
    rfl
  refine ⟨f.liftOfSurjective hf ⟨rows, hker⟩, ?_⟩
  intro x y
  rw [f.liftOfRightInverse_comp_apply _ _ _ x]
  exact hrow x y

public theorem exists_center_commutator_pairing (hd : commutator S ≤ center S) :
    ∃ b : S →* (S →* center S),
      ∀ x y, (b x y : S) = ⁅x, y⁆ := by
  have hc (x y : S) : ⁅x,y⁆ ∈ center S :=
    hd (commutator_mem_commutator (mem_top x) (mem_top y))
  let row (x : S) : S →* center S :=
    (ClassTwo.commutatorHom hd x).codRestrict (center S) (hc x)
  have hrow (x y : S) : (row x y : S) = ⁅x,y⁆ := rfl
  refine ⟨{
    toFun := row
    map_one' := ?_
    map_mul' := ?_ }, hrow⟩
  · ext y
    change ⁅(1 : S), y⁆ = 1
    simp
  · intro x y
    ext z
    change ⁅x*y,z⁆ = ⁅x,z⁆ * ⁅y,z⁆
    rw [commutatorElement_mul_left_eq_conj_mul,
      mem_center_iff.mp (hc y z) x, mul_inv_cancel_right,
      mem_center_iff.mp (hc x z) ⁅y,z⁆]

public theorem exists_invariant_pairing_of_center_retraction
    (f : S →* T) (hf : Function.Surjective f) (hk : f.ker ≤ center S)
    (hd : commutator S ≤ center S)
    (a : MulAut S) (b : MulAut T) (hab : ∀ x, f (a x) = b (f x))
    (n : center S →* C)
    (hn : ∀ x : center S, n (centerCongr a x) = n x) :
    ∃ c : T →* (T →* C),
      (∀ x y : S, c (f x) (f y) = n
        ⟨⁅x,y⁆, hd (commutator_mem_commutator (mem_top x) (mem_top y))⟩) ∧
      (∀ x y, c (b x) (b y) = c x y) := by
  obtain ⟨d, hdval⟩ := exists_center_commutator_pairing hd
  let nd : S →* (S →* C) := {
    toFun x := n.comp (d x)
    map_one' := by ext y; simp
    map_mul' := by intro x y; ext z; simp }
  have hnd (x y : S) : nd x y = n (d x y) := rfl
  have hl : ∀ x ∈ f.ker, nd x = 1 := by
    intro x hx
    ext y
    change n (d x y) = 1
    have he : d x y = 1 := by
      apply Subtype.ext
      rw [hdval]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hk hx) y).symm
    rw [he, map_one]
  have hr : ∀ x, f.ker ≤ (nd x).ker := by
    intro x y hy
    change n (d x y) = 1
    have he : d x y = 1 := by
      apply Subtype.ext
      rw [hdval]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hk hy) x)
    rw [he, map_one]
  obtain ⟨c, hc⟩ := exists_descended_pairing f hf nd hl hr
  refine ⟨c, ?_, ?_⟩
  · intro x y
    rw [hc, hnd]
    congr 1
    apply Subtype.ext
    exact hdval x y
  · intro x y
    obtain ⟨u, rfl⟩ := hf x
    obtain ⟨v, rfl⟩ := hf y
    rw [← hab, ← hab, hc, hc, hnd, hnd]
    have he : d (a u) (a v) = centerCongr a (d u v) := by
      apply Subtype.ext
      change (d (a u) (a v) : S) = a (d u v)
      rw [hdval, hdval, map_commutatorElement]
    rw [he, hn]

public theorem retraction_kills_derived_of_pairing_trivial
    (hd : commutator S ≤ center S) (n : center S →* C)
    (hn : ∀ x y : S, n
      ⟨⁅x,y⁆, hd (commutator_mem_commutator (mem_top x) (mem_top y))⟩ = 1) :
    ∀ x : center S, (x : S) ∈ commutator S → n x = 1 := by
  have hle : commutator S ≤ n.ker.map (center S).subtype := by
    rw [commutator_def]
    apply commutator_le.mpr
    intro x _ y _
    exact ⟨⟨⁅x,y⁆, hd (commutator_mem_commutator (mem_top x) (mem_top y))⟩,
      hn x y, rfl⟩
  intro x hx
  obtain ⟨y, hy, he⟩ := hle hx
  have he' : y = x := Subtype.ext he
  change n y = 1 at hy
  simpa only [he'] using hy

end CentralExtension

namespace CentralExtension
open Subgroup
open scoped IsMulCommutative
variable {S T : Type*} [Group S] [Group T]

public theorem exists_center_norm_retraction
    (f : S →* T) (hf : Function.Surjective f) (hk : f.ker ≤ center S)
    (hcard : Nat.card f.ker = 2)
    (a : MulAut S) (b : MulAut T) (hab : ∀ x, f (a x) = b (f x))
    (hkerfix : ∀ x ∈ f.ker, a x = x)
    (r : ℕ) (hr : a ^ r = 1) (hodd : Odd r)
    (hfixed : ∀ z ∈ center T, b z = z → z = 1) :
    ∃ n : center S →* f.ker,
      (∀ z : center S, f (z : S) = 1 → (n z : S) = z) ∧
      (∀ z, n (centerCongr a z) = n z) := by
  let A : Subgroup (center S) := f.ker.subgroupOf (center S)
  let az : MulAut (center S) := centerCongr a
  have hpow (i : ℕ) (z : center S) : ((az ^ i) z : S) = (a ^ i) z := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ', pow_succ']
      change a ((az ^ i) z) = a ((a ^ i) z)
      rw [ih]
  have haz : az ^ r = 1 := by
    ext z
    change ((az ^ r) z : S) = z
    rw [hpow, hr]
    rfl
  have hfix : ∀ z : center S, az z = z ↔ z ∈ A := by
    intro z
    constructor
    · intro hz
      change f (z : S) = 1
      apply hfixed
      · rw [mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := hf y
        rw [← map_mul, ← map_mul, mem_center_iff.mp z.property x]
      · rw [← hab]
        exact congrArg f (congrArg Subtype.val hz)
    · intro hz
      exact Subtype.ext (hkerfix z hz)
  have hsq : ∀ z ∈ A, z ^ 2 = 1 := by
    intro z hz
    have hp := pow_card_eq_one' (x := (⟨(z : S), hz⟩ : f.ker))
    rw [hcard] at hp
    apply Subtype.ext
    exact congrArg (fun x : f.ker => (x : S)) hp
  obtain ⟨n, hn, hinv⟩ := MulAut.exists_cyclicNorm_retraction az haz hodd A hfix hsq
  let e : A ≃* f.ker := subgroupOfEquivOfLe hk
  refine ⟨e.toMonoidHom.comp n, ?_, ?_⟩
  · intro z hz
    have he := congrArg (fun x : A => ((x : center S) : S)) (hn ⟨z, hz⟩)
    exact he
  · intro z
    change e (n (az z)) = e (n z)
    rw [hinv]

public theorem false_of_invariant_pairings_trivial
    (f : S →* T) (hf : Function.Surjective f) (hk : f.ker ≤ center S)
    (hcard : Nat.card f.ker = 2)
    (hkd : f.ker ≤ commutator S) (hd : commutator S ≤ center S)
    (a : MulAut S) (b : MulAut T) (hab : ∀ x, f (a x) = b (f x))
    (hkerfix : ∀ x ∈ f.ker, a x = x)
    (r : ℕ) (hr : a ^ r = 1) (hodd : Odd r)
    (hfixed : ∀ z ∈ center T, b z = z → z = 1)
    (hforms : ∀ c : T →* (T →* Multiplicative (ZMod 2)),
      (∀ x y, c (b x) (b y) = c x y) → c = 1) : False := by
  obtain ⟨n, hn, hninv⟩ := exists_center_norm_retraction f hf hk hcard
    a b hab hkerfix r hr hodd hfixed
  let e : f.ker ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hcard (by simp)
  let n' := e.toMonoidHom.comp n
  obtain ⟨c, hc, hinv⟩ := exists_invariant_pairing_of_center_retraction
    f hf hk hd a b hab n' (fun z => congrArg e (hninv z))
  have hc1 := hforms c hinv
  have hnD := retraction_kills_derived_of_pairing_trivial hd n' (fun x y => by
    rw [← hc, hc1]; rfl)
  have hbot : f.ker = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have he := hnD ⟨z, hk hz⟩ (hkd hz)
    have hnz : n ⟨z, hk hz⟩ = 1 := e.injective (by
      change n' ⟨z, hk hz⟩ = e 1
      rw [he, map_one])
    have hnzval := congrArg Subtype.val hnz
    rw [hn ⟨z, hk hz⟩ hz] at hnzval
    exact hnzval
  simp only [hbot, Subgroup.card_bot] at hcard
  contradiction
end CentralExtension
