module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Detecting splitting with a commuting pair of involution lifts

Suppose the nontrivial perfect two-primary covers of a perfect group have
kernel of order two and no involution outside that kernel. A central two-group
extension splits if lifts of two independent involutions commute. Pass to its
derived subgroup; in the nonsplit case the two lifts have the same nonidentity
square, so their product contradicts the involution condition.

A square root of one base involution commuting with the other supplies the
commuting-lifts condition in every central extension. This distinguishes the
native ambient-group obligation from mere existence of involution lifts.

Application: Aschbacher–Smith I.2.2(6), printed p.412. For A₆ the explicit
cover-data input follows from the earlier SL₂(9) covering identification in
I.2.2(1); this module does not assert that identification.
-/

@[expose] public section
namespace CentralExtension
open Subgroup PerfectCentralCovering
open scoped commutatorElement
universe u v w

/-- An explicit earlier covering-classification input, not a splitting assertion.
For A₆ its nontrivial branch is the double cover SL₂(9). -/
def TwoPrimaryInvolutionData (A : Type v) [Group A] : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (c : Cover D A),
    IsPGroup 2 c.toMonoidHom.ker → c.toMonoidHom.ker = ⊥ ∨
      (Nat.card c.toMonoidHom.ker = 2 ∧ ∀ x : D, x ^ 2 = 1 → c.toMonoidHom x = 1)

/-- A commuting Klein-four pair detects the trivial derived cover and gives
a section of the original map. -/
theorem exists_section_of_commuting_involution_lifts {E : Type u} {A : Type v} [Group E] [Finite E] [Group A] [Group.IsPerfect A]
    (hcover : TwoPrimaryInvolutionData.{u} A)
    (f : E →* A) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (hp : IsPGroup 2 f.ker)
    (a b : A) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a * b ≠ 1)
    (hcomm : ∀ x y : E, f x = a → f y = b → Commute x y) :
    ∃ s : A →* E, f.comp s = MonoidHom.id A := by
  let D := commutator E
  let g : D →* A := f.comp D.subtype
  have hg : Function.Surjective g := by
    have hm : D.map f = ⊤ := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf, commutator_eq_self]
    intro a
    obtain ⟨x, hx, hxa⟩ := (show a ∈ D.map f by rw [hm]; trivial)
    exact ⟨⟨x, hx⟩, hxa⟩
  have hgc : g.ker ≤ center D := fun d hd => mem_center_iff.mpr fun x =>
    Subtype.ext (mem_center_iff.mp (hc hd) x)
  let c : Cover D A := {
    toMonoidHom := g
    surjective := hg
    isPerfect := commutator_isPerfect_of_surjective_of_ker_le_center f hf hc
    ker_le_center := hgc }
  let k : g.ker →* f.ker := (D.subtype.comp g.ker.subtype).codRestrict _ (fun x => x.property)
  have hki : Function.Injective k := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : E)) h))
  have hker : g.ker = ⊥ := by
    rcases hcover D c (hp.of_injective k hki) with h | ⟨hcard, hinv⟩
    · exact h
    · obtain ⟨x, hx⟩ := hg a
      obtain ⟨y, hy⟩ := hg b
      have hx2 : x ^ 2 ∈ g.ker := by rw [MonoidHom.mem_ker, map_pow, hx, ha]
      have hy2 : y ^ 2 ∈ g.ker := by rw [MonoidHom.mem_ker, map_pow, hy, hb]
      have hx2n : (⟨x ^ 2, hx2⟩ : g.ker) ≠ 1 := fun h =>
        ha1 (hx.symm.trans (hinv x (congrArg Subtype.val h)))
      have hy2n : (⟨y ^ 2, hy2⟩ : g.ker) ≠ 1 := fun h =>
        hb1 (hy.symm.trans (hinv y (congrArg Subtype.val h)))
      obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : g.ker)).mp hcard
      have heq : x ^ 2 = y ^ 2 := congrArg Subtype.val
        ((hz _ hx2n).trans (hz _ hy2n).symm)
      have hxy : Commute x y := Subtype.ext (hcomm x y hx hy).eq
      have hxy2 : (x * y) ^ 2 = 1 := by
        rw [hxy.mul_pow, heq, ← pow_two]
        have h := pow_card_eq_one' (x := (⟨y ^ 2, hy2⟩ : g.ker))
        rw [hcard] at h
        exact congrArg Subtype.val h
      exact (hab (by rw [← hx, ← hy, ← map_mul]; exact hinv (x * y) hxy2)).elim
  let e : D ≃* A := MulEquiv.ofBijective g ⟨g.ker_eq_bot_iff.mp hker, hg⟩
  refine ⟨D.subtype.comp e.symm.toMonoidHom, ?_⟩
  ext a
  exact e.apply_symm_apply a

/-- A square root commuting with a base involution forces arbitrary lifts of
its square and that involution to commute. -/
theorem commute_lifts_of_commuting_square_root
    {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (a b r : G) (hr : r ^ 2 = a) (hb : b ^ 2 = 1) (hrb : Commute r b)
    (x y : E) (hx : f x = a) (hy : f y = b) : Commute x y := by
  obtain ⟨s, hs⟩ := hf r
  have hc : ⁅s, y⁆ ∈ center E := hk (by
    rw [MonoidHom.mem_ker, map_commutatorElement, hs, hy]
    exact hrb.commutator_eq)
  have hconj (t : E) : t * ⁅s, y⁆ * t⁻¹ = ⁅s, y⁆ := by
    rw [mem_center_iff.mp hc t, mul_inv_cancel_right]
  have hl : ⁅s ^ 2, y⁆ = ⁅s, y⁆ ^ 2 := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hconj, pow_two]
  have hr' : ⁅s, y ^ 2⁆ = ⁅s, y⁆ ^ 2 := by
    rw [pow_two, commutatorElement_mul_right_eq_mul_conj,
      mul_assoc, mul_assoc, ← mul_assoc y, hconj, pow_two]
  have hyc : y ^ 2 ∈ center E := hk (by
    rw [MonoidHom.mem_ker, map_pow, hy, hb])
  apply commutatorElement_eq_one_iff_mul_comm.mp
  calc
    ⁅x, y⁆ = ⁅s ^ 2, y⁆ := commutator_eq_of_image_eq f hk
      (by rw [map_pow, hs, hr, hx]) rfl
    _ = ⁅s, y ^ 2⁆ := hl.trans hr'.symm
    _ = 1 := (show Commute s (y ^ 2) from mem_center_iff.mp hyc s).commutator_eq

/-- Apply the commuting-pair criterion to the literal preimage of an embedded
perfect subgroup. The resulting lift retains the specified embedding. -/
theorem exists_lift_of_commuting_involution_lifts
    {E : Type u} {A : Type v} {G : Type w}
    [Group E] [Finite E] [Group A] [Group.IsPerfect A] [Group G]
    (hcover : TwoPrimaryInvolutionData.{u} A)
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (hp : IsPGroup 2 f.ker) (j : A →* G) (hj : Function.Injective j)
    (a b : A) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a * b ≠ 1)
    (hcomm : ∀ x y : E, f x = j a → f y = j b → Commute x y) :
    ∃ s : A →* E, f.comp s = j := by
  let H := j.range.comap f
  let e := MonoidHom.ofInjective hj
  let q₀ : H →* j.range := f.subgroupComap j.range
  let q : H →* A := e.symm.toMonoidHom.comp q₀
  have hq (x : H) : j (q x) = f x := congrArg Subtype.val (e.apply_symm_apply (q₀ x))
  have hqsur : Function.Surjective q :=
    e.symm.surjective.comp (f.subgroupComap_surjective_of_surjective j.range hf)
  have hqker {x : H} (hx : x ∈ q.ker) : (x : E) ∈ f.ker := by
    change f x = 1
    rw [← hq, MonoidHom.mem_ker.mp hx, map_one]
  have hqcentral : q.ker ≤ center H := fun x hx => mem_center_iff.mpr fun y =>
    Subtype.ext (mem_center_iff.mp (hk (hqker hx)) y)
  let k : q.ker →* f.ker :=
    (H.subtype.comp q.ker.subtype).codRestrict _ (fun x => hqker x.property)
  have hki : Function.Injective k := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : E)) h))
  have hc (x y : H) (hx : q x = a) (hy : q y = b) : Commute x y :=
    Subtype.ext (hcomm x y ((hq x).symm.trans (congrArg j hx))
      ((hq y).symm.trans (congrArg j hy))).eq
  obtain ⟨s, hs⟩ := exists_section_of_commuting_involution_lifts hcover q hqsur hqcentral
    (hp.of_injective k hki) a b ha hb ha1 hb1 hab hc
  refine ⟨H.subtype.comp s, ?_⟩
  ext a
  change f (s a) = j a
  rw [← hq]
  exact congrArg j (DFunLike.congr_fun hs a)

end CentralExtension
