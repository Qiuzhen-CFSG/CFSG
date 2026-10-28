module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Equivariant sections over odd normalizers in central two-extensions

A homomorphic section of a central extension gives a retraction onto its
kernel. Average this retraction over an odd-order group of automorphisms,
using the product of its conjugates. If the kernel has exponent two and is
fixed pointwise, the average is still a retraction. The kernel of the average
projects isomorphically onto the original base, giving an equivariant section.
The base is allowed to be nonabelian.

For a subgroup of a quotient group, centrality makes conjugation by a lift
independent of the lift. Factoring this conjugation homomorphism through an
odd normalizing subgroup gives equivariance under every lift of every actor.
Only the existence of the original section remains an explicit premise.

This is the elementary coprime averaging argument used for the root-block
lifting step in GLS3 §6.1 and Aschbacher–Smith I.1.1–4 (printed pp.407–408).
The concrete Ree application is in CentralCovers/TwoPrimary/NormalizedBlocks.
-/

public section
open scoped BigOperators
namespace CentralExtension

private theorem odd_power {K : Type*} [Group K] (k : K)
    (hsq : k ^ 2 = 1) {n : ℕ} (hn : Odd n) : k ^ n = k := by
  obtain ⟨r, rfl⟩ := hn
  rw [pow_add, pow_mul, hsq, one_pow, pow_one, one_mul]

/-- Averaging a retraction over an odd action preserves its restriction to
an elementary abelian two-group fixed pointwise by that action. -/
theorem exists_invariant_retraction {A E K : Type*} [Group A] [Finite A]
    [Group E] [CommGroup K] (α : A →* MulAut E) (ι : K →* E)
    (r : E →* K) (hr : r.comp ι = MonoidHom.id K)
    (hfix : ∀ a k, α a (ι k) = ι k)
    (hodd : Odd (Nat.card A)) (hsq : ∀ k : K, k ^ 2 = 1) :
    ∃ R : E →* K, R.comp ι = MonoidHom.id K ∧
      ∀ a x, R (α a x) = R x := by
  classical
  let := Fintype.ofFinite A
  let R : E →* K := ∏ a : A, r.comp (α a).toMonoidHom
  have hR (x : E) : R x = ∏ a : A, r (α a x) := by
    simp [R]
  refine ⟨R, MonoidHom.ext (fun k => ?_), ?_⟩
  · change R (ι k) = k
    rw [hR]
    simp only [hfix, show ∀ k, r (ι k) = k from DFunLike.congr_fun hr]
    simpa only [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card] using
      odd_power k (hsq k) hodd
  · intro a x
    simp only [hR]
    have hmul (b : A) : α b (α a x) = α (b * a) x := by
      rw [map_mul]
      rfl
    simp only [hmul]
    exact Equiv.prod_comp (Equiv.mulRight a) (fun b => r (α b x))


open Subgroup
open scoped IsMulCommutative

/-- A section of the prescribed central extension gives a kernel retraction. -/
theorem exists_kernel_retraction {E B : Type*} [Group E] [Group B]
    (f : E →* B) (hk : f.ker ≤ center E)
    (s : B →* E) (hs : f.comp s = MonoidHom.id B) :
    ∃ r : E →* f.ker, r.comp f.ker.subtype = MonoidHom.id f.ker := by
  have hs' (b : B) : f (s b) = b := DFunLike.congr_fun hs b
  let r (x : E) : f.ker := ⟨x * (s (f x))⁻¹, by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, hs', mul_inv_cancel]⟩
  have hc (x y : E) : x * (r y).val = (r y).val * x :=
    mem_center_iff.mp (hk (r y).property) x
  refine ⟨{ toFun := r, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply Subtype.ext
    simp [r]
  · intro x y
    apply Subtype.ext
    change x * y * (s (f (x*y)))⁻¹ = (r x).val * (r y).val
    calc
      _ = x * (r y).val * (s (f x))⁻¹ := by simp [r, mul_assoc]
      _ = (r y).val * (r x).val := by rw [hc]; exact mul_assoc _ _ _
      _ = (r x).val * (r y).val := (hc (r x).val y).symm
  · apply MonoidHom.ext
    intro k
    apply Subtype.ext
    change k.val * (s (f k.val))⁻¹ = k.val
    simp only [MonoidHom.mem_ker.mp k.property, map_one, inv_one, mul_one]

/-- An odd action fixing a central exponent-two kernel admits an equivariant
section whenever the prescribed extension already has a section. -/
theorem exists_equivariant_section {A E B : Type*}
    [Group A] [Finite A] [Group E] [Group B]
    (f : E →* B) (hk : f.ker ≤ center E)
    (α : A →* MulAut E) (β : A →* MulAut B)
    (heq : ∀ a x, f (α a x) = β a (f x))
    (hfix : ∀ (a : A) (k : f.ker), α a k.val = k.val)
    (hodd : Odd (Nat.card A)) (hsq : ∀ k : f.ker, k ^ 2 = 1)
    (s : B →* E) (hs : f.comp s = MonoidHom.id B) :
    ∃ S : B →* E, f.comp S = MonoidHom.id B ∧
      ∀ a x, α a (S x) = S (β a x) := by
  let : IsMulCommutative f.ker := ⟨⟨fun x y =>
    Subtype.ext (mem_center_iff.mp (hk y.property) x.val)⟩⟩
  obtain ⟨r, hr⟩ := exists_kernel_retraction f hk s hs
  obtain ⟨R, hR, hinv⟩ := exists_invariant_retraction α f.ker.subtype r hr hfix hodd hsq
  have hR' (k : f.ker) : R k.val = k := DFunLike.congr_fun hR k
  let p : R.ker →* B := f.comp R.ker.subtype
  have hpi : Function.Injective p := by
    apply (MonoidHom.ker_eq_bot_iff p).mp
    apply bot_unique
    intro x hx
    have hxker : f x.val = 1 := hx
    have he : R x.val = (⟨x.val, hxker⟩ : f.ker) := hR' ⟨x.val, hxker⟩
    rw [MonoidHom.mem_ker.mp x.property] at he
    exact Subtype.ext (congrArg (fun z : f.ker => z.val) he.symm)
  have hps : Function.Surjective p := by
    intro b
    let x := s b
    let y := x * (R x).val⁻¹
    have hy : y ∈ R.ker := by
      change R (x * (R x).val⁻¹) = 1
      rw [map_mul, map_inv, hR', mul_inv_cancel]
    refine ⟨⟨y,hy⟩, ?_⟩
    change f (x * (R x).val⁻¹) = b
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp (R x).property, inv_one, mul_one]
    exact DFunLike.congr_fun hs b
  let e := MulEquiv.ofBijective p ⟨hpi, hps⟩
  let S : B →* E := R.ker.subtype.comp e.symm.toMonoidHom
  have hS (b : B) : f (S b) = b := e.apply_symm_apply b
  refine ⟨S, MonoidHom.ext hS, ?_⟩
  intro a b
  have hb : α a (S b) ∈ R.ker := by
    change R (α a (S b)) = 1
    rw [hinv]
    exact (e.symm b).property
  exact congrArg Subtype.val (hpi (show p ⟨α a (S b), hb⟩ = p (e.symm (β a b)) from
    (heq a (S b)).trans ((congrArg (β a) (hS b)).trans (hS (β a b)).symm)))


/-- A splitting over a subgroup can be made equivariant under every lift of
an odd-order normalizing subgroup, if the central kernel has exponent two. -/
theorem exists_odd_normalizer_equivariant_section {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (hsq : ∀ k : f.ker, k ^ 2 = 1)
    (T P : Subgroup G) [Finite T] (hodd : Odd (Nat.card T))
    (hn : T ≤ normalizer (P : Set G))
    (s : P →* E) (hs : f.comp s = P.subtype) :
    ∃ S : P →* E, f.comp S = P.subtype ∧
      ∀ (a b : P) (g : E), f g ∈ T → f g * a.val * (f g)⁻¹ = b.val →
        g * S a * g⁻¹ = S b := by
  let H := P.comap f
  let N := T.comap f
  let p : H →* P := (f.comp H.subtype).codRestrict P (fun x => x.property)
  let t : N →* T := (f.comp N.subtype).codRestrict T (fun x => x.property)
  have ht : Function.Surjective t := by
    intro a
    obtain ⟨g,hg⟩ := hf a.val
    exact ⟨⟨g, show f g ∈ T from hg ▸ a.property⟩, Subtype.ext hg⟩
  let n : N →* normalizer (H : Set E) := N.subtype.codRestrict _ (by
    intro g
    apply mem_normalizer_iff.mpr
    intro x
    change f x ∈ P ↔ f (g.val * x * g.val⁻¹) ∈ P
    simpa only [map_mul, map_inv] using mem_normalizer_iff.mp (hn g.property) (f x))
  let c : N →* MulAut H := H.normalizerMonoidHom.comp n
  have hck : t.ker ≤ c.ker := by
    intro g hg
    have hg' : g.val ∈ f.ker := congrArg Subtype.val (show t g = 1 from hg)
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change g.val * x.val * g.val⁻¹ = x.val
    rw [← mem_center_iff.mp (hk hg') x.val, mul_inv_cancel_right]
  let α : T →* MulAut H := t.liftOfSurjective ht ⟨c,hck⟩
  have ha (g : N) : α (t g) = c g :=
    t.liftOfRightInverse_comp_apply _ _ ⟨c,hck⟩ g
  have ha' (g : N) (x : H) : (α (t g) x).val = g.val * x.val * g.val⁻¹ := by
    rw [ha]
    rfl
  let β : T →* MulAut P := P.normalizerMonoidHom.comp (T.subtype.codRestrict _ (fun x => hn x.property))
  have heq (a : T) (x : H) : p (α a x) = β a (p x) := by
    obtain ⟨g,rfl⟩ := ht a
    apply Subtype.ext
    change f ((α (t g) x).val) = (t g).val * f x.val * (t g).val⁻¹
    rw [ha', map_mul, map_mul, map_inv]
    rfl
  have hpk : p.ker ≤ center H := by
    intro x hx
    have hx' : x.val ∈ f.ker := congrArg Subtype.val (show p x = 1 from hx)
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hk hx') y.val)
  have hfix (a : T) (k : p.ker) : α a k.val = k.val := by
    obtain ⟨g,rfl⟩ := ht a
    have hk' : k.val.val ∈ f.ker := congrArg Subtype.val (show p k.val = 1 from k.property)
    apply Subtype.ext
    rw [ha', mem_center_iff.mp (hk hk') g.val, mul_inv_cancel_right]
  have hpsq (k : p.ker) : k ^ 2 = 1 := by
    have hk' : k.val.val ∈ f.ker := congrArg Subtype.val (show p k.val = 1 from k.property)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => z.val) (hsq ⟨k.val.val, hk'⟩)
  let s' : P →* H := s.codRestrict H (by
    intro a
    change f (s a) ∈ P
    rw [show f (s a) = a.val from DFunLike.congr_fun hs a]
    exact a.property)
  have hs' : p.comp s' = MonoidHom.id P :=
    MonoidHom.ext fun a => Subtype.ext (DFunLike.congr_fun hs a)
  obtain ⟨S,hS,hSe⟩ := exists_equivariant_section p hpk α β heq hfix hodd hpsq s' hs'
  refine ⟨H.subtype.comp S, MonoidHom.ext (fun a => ?_), ?_⟩
  · exact congrArg Subtype.val (DFunLike.congr_fun hS a)
  · intro a b g hg he
    let g' : N := ⟨g,hg⟩
    have he' : β (t g') a = b := Subtype.ext he
    have h := congrArg Subtype.val (hSe (t g') a)
    rw [ha', he'] at h
    exact h

end CentralExtension
