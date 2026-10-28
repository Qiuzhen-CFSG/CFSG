module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.BorelCollection

/-!
# Abstract Bruhat coverage for the signed triality presentation

Ascending steps use the five positive conjugation identities, with the two
Frobenius shifts on the short orbit. Descending steps use the signed rank-one
factorization. The braid identifies the two words of length six, closing the
cover under the generators and their inverses. No model map, group order,
abstract normal-form uniqueness, or simplicity is an input.

The finite cover proves finiteness and reduces evaluation faithfulness to the
concrete Borel and nonidentity Weyl cells. It does not itself verify the
relations in a model or assert presentation faithfulness.
Source: GLS3 2.3.5 and 2.4.8; the same double-cell argument appears in the
proved G₂ `RootPresentationRecognition/BruhatCollection` family.
-/

@[expose] public noncomputable section
namespace Triality.Standard.RootPresentationRecognition.SignedRoots
open Parabolics ConcreteBruhat.TorusCoordinates
variable {n : ℕ} {hn : 0 < n} {Y : Type*} [Group Y]
local notation "P" => binaryParameters n hn
variable (L : SignedRoots (n := n) (hn := hn) Y) (R : L.Relations)

/-- Alternating simple Weyl words. -/
def alternating (a : Bool) : ℕ → Y
  | 0 => 1
  | k+1 => L.reflection a * alternating (!a) k

@[simp] theorem alternating_zero (a : Bool) : L.alternating a 0 = 1 := rfl

include R in
theorem alternating_conjugate_succ (a : Bool) (k : ℕ) (x : Y) :
    (L.alternating a (k+1))⁻¹ * x * L.alternating a (k+1) =
      (L.alternating (!a) k)⁻¹ * (L.reflection a * x * (L.reflection a)⁻¹) *
        L.alternating (!a) k := by
  simp only [alternating, mul_inv_rev, L.reflection_inv R, mul_assoc]

include R in
theorem alternating_longest : L.alternating true 6 = L.alternating false 6 := by
  apply eq_of_mul_inv_eq_one
  calc
    _ = (L.nA 1 * L.nB 1)^6 := by
      have ha : (L.nA 1)⁻¹ = L.nA 1 := L.reflection_inv R true
      have hb : (L.nB 1)⁻¹ = L.nB 1 := L.reflection_inv R false
      simp only [alternating, reflection, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        if_true, if_false, mul_inv_rev, ha, hb,
        pow_succ, pow_zero, mul_one, one_mul, mul_assoc]
    _ = 1 := R.braid

include R in
theorem alternating_longest_flip (a : Bool) : L.alternating (!a) 6 = L.alternating a 6 := by
  cases a
  · exact L.alternating_longest R
  · exact (L.alternating_longest R).symm

/-- Five ascending steps stay in positive roots. The short orbit uses both
Frobenius shifts, which cancel after one cubic cycle. -/
theorem alternating_simple_mem (a : Bool) (k : ℕ) (hk : k ≤ 5)
    (v : PositiveParameters n hn) :
    (L.alternating (!a) k)⁻¹ * L.simpleValue a v * L.alternating (!a) k ∈ L.borel R := by
  have hs1 := R.arms_short1 true
  have hs2 := R.arms_short2 true
  have hl := R.arms_long true
  have hcs := R.central_short true
  have hcl1 := R.central_long1 true
  have hcl2 := R.central_long2 true
  simp only [shortSigned, longSigned, if_true] at hs1 hs2 hl hcs hcl1 hcl2
  cases a <;> interval_cases k
  all_goals
    simp only [Bool.not_true, Bool.not_false, simpleValue, if_true, Bool.false_eq_true,
      if_false, L.alternating_conjugate_succ R, reflection, hs1, hs2, hl, hcs,
      hcl1, hcl2, show (![1,0,2] : Fin 3 → Fin 3) 0 = 1 from rfl,
      show (![1,0,2] : Fin 3 → Fin 3) 1 = 0 from rfl,
      show (![1,0,2] : Fin 3 → Fin 3) 2 = 2 from rfl,
      alternating_zero, inv_one, one_mul, mul_one, fieldFrobenius_three]
    first | exact L.short_mem_borel R _ _ | exact L.long_mem_borel R _ _

/-- A Borel double cell represented by an alternating word of length at most six. -/
def Covered (g : Y) : Prop := ∃ (b c : Y) (a : Bool) (k : ℕ),
  b ∈ L.borel R ∧ c ∈ L.borel R ∧ k ≤ 6 ∧ g = b * L.alternating a k * c

theorem covered_one : L.Covered R 1 :=
  ⟨1,1,false,0,Subgroup.one_mem _,Subgroup.one_mem _,by omega,by simp⟩

theorem covered_left (b : Y) (hb : b ∈ L.borel R) {g : Y} (hg : L.Covered R g) :
    L.Covered R (b*g) := by
  obtain ⟨c,d,a,k,hc,hd,hk,rfl⟩ := hg
  exact ⟨b*c,d,a,k,Subgroup.mul_mem _ hb hc,hd,hk,by simp only [mul_assoc]⟩

theorem covered_right (b : Y) (hb : b ∈ L.borel R) {g : Y} (hg : L.Covered R g) :
    L.Covered R (g*b) := by
  obtain ⟨c,d,a,k,hc,hd,hk,rfl⟩ := hg
  exact ⟨c,d*b,a,k,hc,Subgroup.mul_mem _ hd hb,hk,by simp only [mul_assoc]⟩

theorem covered_ascent (a : Bool) (k : ℕ) (hk : k ≤ 5) (v : PositiveParameters n hn) :
    L.Covered R (L.reflection a * L.simpleValue a v * L.alternating (!a) k) := by
  refine ⟨1,(L.alternating (!a) k)⁻¹ * L.simpleValue a v * L.alternating (!a) k,
    a,k+1,Subgroup.one_mem _,L.alternating_simple_mem R a k hk v,by omega,?_⟩
  simp only [alternating]
  group

include R in
theorem torus_short (t : (ExtensionField P)ˣ) : L.torus (t,1) = L.hA t := by
  have hb : L.nB 1 * L.nB 1 = 1 := (pow_two _).symm.trans R.nB_sq
  simp only [torus,hB,hb,mul_one]

include R in
theorem torus_long (t : (fixedField P)ˣ) : L.torus (1,t) = L.hB t := by
  have ha : L.nA 1 * L.nA 1 = 1 := (pow_two _).symm.trans R.nA_sq
  simp only [torus,hA,ha,one_mul]

include R in
theorem short_exchange (t : (ExtensionField P)ˣ) :
    L.nA 1 * L.shortValue 0 t.val * L.nA 1 =
      L.shortValue 0 (t⁻¹).val * L.torus (t⁻¹,1) * L.nA 1 * L.shortValue 0 (t⁻¹).val := by
  have h := R.arms_short0 true t.val
  simp only [shortSigned, Bool.not_true, Bool.false_eq_true, if_true, if_false] at h
  have hi : (L.nA 1)⁻¹ = L.nA 1 := L.reflection_inv R true
  rw [hi] at h
  rw [h, L.torus_short R]
  exact L.negativeShort_factorization R.toWeylRelations t

include R in
theorem long_exchange (t : (fixedField P)ˣ) :
    L.nB 1 * L.longValue 0 t.val * L.nB 1 =
      L.longValue 0 (t⁻¹).val * L.torus (1,t⁻¹) * L.nB 1 * L.longValue 0 (t⁻¹).val := by
  have h := R.central_long0 true t.val
  simp only [longSigned, Bool.not_true, Bool.false_eq_true, if_true, if_false] at h
  have hi : (L.nB 1)⁻¹ = L.nB 1 := L.reflection_inv R false
  rw [hi] at h
  rw [h, L.torus_long R]
  exact L.negativeLong_factorization R.toWeylRelations t

/-- Descending steps use the actual short or long rank-one factorization. -/
theorem covered_descent (a : Bool) (k : ℕ) (hk : k ≤ 5) (v : PositiveParameters n hn) :
    L.Covered R (L.reflection a * L.simpleValue a v * L.alternating a (k+1)) := by
  have step (z : PositiveParameters n hn) (p : TorusParameters n hn)
      (he : L.reflection a * L.simpleValue a v * L.reflection a =
        L.simpleValue a z * L.torus p * L.reflection a * L.simpleValue a z) :
      L.Covered R (L.reflection a * L.simpleValue a v * L.alternating a (k+1)) := by
    refine ⟨L.simpleValue a z * L.torus p,
      (L.alternating (!a) k)⁻¹ * L.simpleValue a z * L.alternating (!a) k,a,k+1,
      Subgroup.mul_mem _ (L.simple_mem_borel R a z) (L.torus_mem_borel R p),
      L.alternating_simple_mem R a k hk z,by omega,?_⟩
    change _ * (L.reflection a * L.alternating (!a) k) =
      _ * (L.reflection a * L.alternating (!a) k) * _
    rw [← mul_assoc,he]
    group
  have zero (he : L.simpleValue a v = 1) :
      L.Covered R (L.reflection a * L.simpleValue a v * L.alternating a (k+1)) := by
    refine ⟨1,1,!a,k,Subgroup.one_mem _,Subgroup.one_mem _,by omega,?_⟩
    simp only [he,alternating,mul_one,one_mul]
    rw [← mul_assoc,L.reflection_sq R,one_mul]
  cases a
  · by_cases ht : v.2 0 = 0
    · apply zero
      exact (congrArg (L.positive.longRoot 0) (show Multiplicative.ofAdd (v.2 0) = 1 by rw [ht]; rfl)).trans (map_one _)
    · let t : (fixedField P)ˣ := Units.mk0 (v.2 0) ht
      exact step (0,fun _ => (t⁻¹).val) (1,t⁻¹) (L.long_exchange R t)
  · by_cases ht : v.1 0 = 0
    · apply zero
      exact (congrArg (L.positive.shortRoot 0) (show Multiplicative.ofAdd (v.1 0) = 1 by rw [ht]; rfl)).trans (map_one _)
    · let t : (ExtensionField P)ˣ := Units.mk0 (v.1 0) ht
      exact step (fun _ => (t⁻¹).val,0) (t⁻¹,1) (L.short_exchange R t)

theorem covered_transition (a start : Bool) (k : ℕ) (hk : k ≤ 6) (v : PositiveParameters n hn) :
    L.Covered R (L.reflection a * L.simpleValue a v * L.alternating start k) := by
  by_cases he : start = a
  · subst start
    cases k with
    | zero => simpa only [alternating_zero] using L.covered_ascent R a 0 (by omega) v
    | succ k => exact L.covered_descent R a k (by omega) v
  · have hs : start = !a := by cases start <;> cases a <;> simp_all
    subst start
    by_cases hlast : k = 6
    · subst k
      rw [L.alternating_longest_flip R]
      exact L.covered_descent R a 5 (by omega) v
    · exact L.covered_ascent R a k (by omega) v

theorem covered_reflection (a : Bool) {g : Y} (hg : L.Covered R g) :
    L.Covered R (L.reflection a * g) := by
  obtain ⟨b,c,start,k,hb,hc,hk,rfl⟩ := hg
  obtain ⟨d,v,hd,he⟩ := L.reflection_borel R a b hb
  have h := L.covered_right R c hc
    (L.covered_left R d hd (L.covered_transition R a start k hk v))
  have hh : L.reflection a * (b * L.alternating start k * c) =
      d * (L.reflection a * L.simpleValue a v * L.alternating start k) * c := by
    calc
      _ = (L.reflection a * b) * L.alternating start k * c := by group
      _ = _ := by rw [he]; group
  rw [hh]
  exact h

/-- The map-free signed relations imply a finite Bruhat cover. -/
theorem bruhat_collection {g : Y} (hg : g ∈ L.signedClosure) : L.Covered R g := by
  rw [L.signedClosure_eq_simpleClosure R.toActionRelations] at hg
  have hcl : L.simpleClosure = Subgroup.closure
      ((L.positive.positiveClosure : Set Y) ∪ {L.nA 1,L.nB 1}) := by
    rw [Subgroup.closure_union,Subgroup.closure_eq]
    rfl
  rw [hcl] at hg
  induction hg using Subgroup.closure_induction_left with
  | one => exact L.covered_one R
  | mul_left x hx y _ ih =>
      rcases hx with hx | hx
      · exact L.covered_left R x (Subgroup.mem_sup_left hx) ih
      · rcases hx with rfl | rfl
        · exact L.covered_reflection R true ih
        · exact L.covered_reflection R false ih
  | inv_mul_cancel x hx y _ ih =>
      rcases hx with hx | hx
      · exact L.covered_left R x⁻¹ (Subgroup.mem_sup_left (Subgroup.inv_mem _ hx)) ih
      · rcases hx with rfl | rfl
        · change L.Covered R ((L.reflection true)⁻¹ * y)
          rw [L.reflection_inv R]
          exact L.covered_reflection R true ih
        · change L.Covered R ((L.reflection false)⁻¹ * y)
          rw [L.reflection_inv R]
          exact L.covered_reflection R false ih

/-- The abstract normal-form parameter space is finite, even when the target
was not given a finiteness instance. Repeated identity/longest labels are harmless
for this cover; no refined order or uniqueness is asserted here. -/
def normalForm (z : (PositiveParameters n hn × TorusParameters n hn) ×
    (Bool × Fin 7) × (PositiveParameters n hn × TorusParameters n hn)) : Y :=
  (L.positive.product z.1.1 * L.torus z.1.2) * L.alternating z.2.1.1 z.2.1.2.val *
    (L.positive.product z.2.2.1 * L.torus z.2.2.2)

include R in
theorem normalForm_surjective (hgen : L.signedClosure = ⊤) : Function.Surjective L.normalForm := by
  intro g
  obtain ⟨b,c,a,k,hb,hc,hk,he⟩ := L.bruhat_collection R
    (g := g) (hgen ▸ Subgroup.mem_top g)
  obtain ⟨v,p,rfl⟩ := (L.mem_borel_iff R b).mp hb
  obtain ⟨w,q,rfl⟩ := (L.mem_borel_iff R c).mp hc
  exact ⟨((v,p),(a,⟨k,by omega⟩),(w,q)),he.symm⟩

include R in
theorem finite_of_generated (hgen : L.signedClosure = ⊤) : Finite Y :=
  Finite.of_surjective L.normalForm (L.normalForm_surjective R hgen)

/-- A concrete evaluation faithful on the Borel and excluding nonidentity Weyl
cells is faithful everywhere. The Bruhat cover, rather than an assumed model
isomorphism or abstract normal-form uniqueness, supplies the kernel argument. -/
theorem injective_of_borel_and_weyl {Z : Type*} [Group Z] (f : Y →* Z) (B : Subgroup Z)
    (hgen : L.signedClosure = ⊤)
    (hB : ∀ b ∈ L.borel R, f b ∈ B)
    (hker : ∀ b ∈ L.borel R, f b = 1 → b = 1)
    (hW : ∀ a k, k ≤ 6 → 0 < k → f (L.alternating a k) ∉ B) : Function.Injective f := by
  apply (injective_iff_map_eq_one f).mpr
  intro g hg
  obtain ⟨b,c,a,k,hb,hc,hk,rfl⟩ := L.bruhat_collection R
    (g := g) (hgen ▸ Subgroup.mem_top g)
  have hw : f (L.alternating a k) ∈ B := by
    have he : f (L.alternating a k) = (f b)⁻¹ * (f c)⁻¹ := by
      rw [map_mul,map_mul] at hg
      calc
        _ = (f b)⁻¹ * (f b * f (L.alternating a k) * f c) * (f c)⁻¹ := by group
        _ = _ := by rw [hg,mul_one]
    rw [he]
    exact B.mul_mem (B.inv_mem (hB b hb)) (B.inv_mem (hB c hc))
  have hk0 : k = 0 := by
    by_contra hne
    exact hW a k hk (Nat.pos_of_ne_zero hne) hw
  simp only [hk0,alternating_zero,mul_one] at hg ⊢
  exact hker _ (Subgroup.mul_mem _ hb hc) hg

end Triality.Standard.RootPresentationRecognition.SignedRoots
