module
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.OrderOfElement

/-!
# A central complement for an inverted odd-order automorphism

Let `A` be a finite central subgroup invariant under automorphisms `r` and `x`.
Suppose `r` has odd order, `x` inverts `r`, and `r` has no nonidentity fixed
point in `A`. If `A` together with the fixed subgroup of `x` generates the
ambient group, then the fixed subgroup of `r` complements `A` and is fixed
pointwise by `x`. In particular, generation holds if the fixed subgroup of
`x` has index two and `x` moves an element of `A`.

On the quotient by `A`, the automorphism `x` is trivial. The inversion relation
then makes the square of `r` trivial, and odd order makes `r` trivial as well.
The displacement homomorphism on `A` is injective, hence surjective; it corrects
any quotient representative to an `r`-fixed element. Finally, an `x`-displacement
of such an element belongs to both factors and so is trivial.

This is the central splitting argument in Janko–Thompson, Math. Z. 113 (1970),
Lemma 3.1, printed p. 388. Neither commutativity of the ambient group nor an
involution hypothesis on `x` is required.
-/

namespace MulAut
variable {T : Type*} [Group T] [Finite T]

/-- An inverted odd-order automorphism acting freely on a finite central subgroup
has a fixed complement when that subgroup and the inverter's fixed subgroup generate. -/
public theorem fixed_complement_of_inverted_odd_sup_eq_top (A : Subgroup T) (r x : MulAut T)
    (hcentral : A ≤ Subgroup.center T) (hodd : Odd (orderOf r))
    (hrA : ∀ a ∈ A, r a ∈ A) (hxA : ∀ a ∈ A, x a ∈ A)
    (hinverts : x * r * x⁻¹ = r⁻¹)
    (hfree : ∀ a ∈ A, r a = a → a = 1)
    (hgen : A ⊔ fixedSubgroup x = ⊤) :
    (A ⊔ fixedSubgroup r = ⊤) ∧ Disjoint A (fixedSubgroup r) ∧
      ∀ b ∈ fixedSubgroup r, x b = b := by
  -- First show that both automorphisms act trivially on the quotient by `A`.
  let : A.Normal := ⟨fun a ha t => by
    rw [Subgroup.mem_center_iff.mp (hcentral ha) t, mul_assoc, mul_inv_cancel, mul_one]
    exact ha⟩
  let q : T →* T ⧸ A := QuotientGroup.mk' A
  let R : T ⧸ A →* T ⧸ A := QuotientGroup.map A A r.toMonoidHom hrA
  have hR (t : T) : R (q t) = q (r t) := rfl
  have hqA (a : T) (ha : a ∈ A) : q a = 1 := (QuotientGroup.eq_one_iff a).2 ha
  have hqx (t : T) : q (x t) = q t := by
    have hle : A ⊔ fixedSubgroup x ≤ (q.comp x.toMonoidHom).eqLocus q := by
      refine sup_le ?_ ?_
      · intro a ha
        change q (x a) = q a
        rw [hqA _ (hxA a ha), hqA _ ha]
      · intro a ha
        change q (x a) = q a
        rw [(mem_fixedSubgroup x a).mp ha]
    exact hle (hgen ▸ Subgroup.mem_top t)
  have hrxr : r * x * r = x := by
    have h := congrArg (fun e : MulAut T => r * e * x) hinverts
    simpa [mul_assoc] using h
  have hsquare (t : T) : q (r (r t)) = q t := by
    calc
      q (r (r t)) = R (q (x (r t))) := by rw [hqx, hR]
      _ = q (r (x (r t))) := hR _
      _ = q (x t) := by
        have h := congrArg (fun e : MulAut T => e t) hrxr
        exact congrArg q h
      _ = q t := hqx t
  have heven (n : ℕ) (t : T) : q ((r ^ (2 * n)) t) = q t := by
    induction n generalizing t with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, pow_add]
      change q ((r ^ (2 * n)) (r (r t))) = q t
      rw [ih, hsquare]
  have hqr (t : T) : q (r t) = q t := by
    obtain ⟨n, hn⟩ := hodd
    have hh := heven n (r t)
    have hp : r ^ (2 * n) * r = 1 := by
      rw [← pow_succ, ← hn, pow_orderOf_eq_one]
    have ht := congrArg (fun e : MulAut T => e t) hp
    change (r ^ (2 * n)) (r t) = t at ht
    rw [ht] at hh
    exact hh.symm
  -- The displacement map is a bijection on the finite central subgroup.
  let : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hcentral b.property) a) }
  let ra : A →* A :=
    { toFun := fun a => ⟨r a, hrA a a.property⟩
      map_one' := Subtype.ext (map_one r)
      map_mul' := fun a b => Subtype.ext (map_mul r (a : T) (b : T)) }
  let d : A →* A :=
    { toFun := fun a => a⁻¹ * ra a
      map_one' := by simp only [map_one, inv_one, mul_one]
      map_mul' := by
        intro a b
        simp only [mul_inv_rev, map_mul]
        ac_rfl }
  have hd : Function.Injective d := by
    apply (injective_iff_map_eq_one d).mpr
    intro a ha
    apply Subtype.ext
    apply hfree a a.property
    have hh := congrArg Subtype.val ha
    change (a : T)⁻¹ * r a = 1 at hh
    exact (inv_mul_eq_one.mp hh).symm
  have hsurj := Finite.surjective_of_injective hd
  -- Correct a representative by its unique displacement preimage.
  have hfactor (t : T) : ∃ a ∈ A, ∃ b ∈ fixedSubgroup r, a * b = t := by
    have ht : t⁻¹ * r t ∈ A := (QuotientGroup.eq_one_iff _).mp (by
      change q (t⁻¹ * r t) = 1
      rw [map_mul, map_inv, hqr, inv_mul_cancel])
    obtain ⟨a, ha⟩ := hsurj ⟨t⁻¹ * r t, ht⟩
    have ha' := congrArg Subtype.val ha
    change (a : T)⁻¹ * r a = t⁻¹ * r t at ha'
    have hrat : r a = (a : T) * (t⁻¹ * r t) := (inv_mul_eq_iff_eq_mul).mp ha'
    refine ⟨a, a.property, (a : T)⁻¹ * t, ?_, by simp⟩
    rw [mem_fixedSubgroup, map_mul, map_inv, hrat]
    have hc := Subgroup.mem_center_iff.mp (hcentral a.property) t
    have hcr := Subgroup.mem_center_iff.mp (hcentral (hrA a a.property)) (r t)
    have heq : r t * (r a)⁻¹ = t * (a : T)⁻¹ := by
      rw [hrat]
      simp [mul_assoc]
    rw [← hrat]
    calc
      (r a)⁻¹ * r t = r t * (r a)⁻¹ := (Commute.inv_right hcr).eq.symm
      _ = t * (a : T)⁻¹ := heq
      _ = (a : T)⁻¹ * t := (Commute.inv_right hc).eq
  -- The complement is disjoint from `A`, and its `x`-displacements lie in both.
  have hdisj : Disjoint A (fixedSubgroup r) := by
    rw [Subgroup.disjoint_def]
    intro a ha har
    exact hfree a ha ((mem_fixedSubgroup r a).mp har)
  refine ⟨?_, hdisj, ?_⟩
  · apply top_unique
    intro t _
    obtain ⟨a, ha, b, hb, rfl⟩ := hfactor t
    exact Subgroup.mul_mem_sup ha hb
  · intro b hb
    have hrb := (mem_fixedSubgroup r b).mp hb
    have hrxb : r (x b) = x b := by
      have h := congrArg (fun e : MulAut T => e b) hrxr
      change r (x (r b)) = x b at h
      rwa [hrb] at h
    have hdiff : b⁻¹ * x b ∈ A := (QuotientGroup.eq_one_iff _).mp (by
      change q (b⁻¹ * x b) = 1
      rw [map_mul, map_inv, hqx, inv_mul_cancel])
    have hdiffr : b⁻¹ * x b ∈ fixedSubgroup r := by
      rw [mem_fixedSubgroup, map_mul, map_inv, hrb, hrxb]
    exact (inv_mul_eq_one.mp (Subgroup.disjoint_def.mp hdisj hdiff hdiffr)).symm

/-- The index-two version of the central fixed-complement theorem. -/
public theorem fixed_complement_of_inverted_odd_index_two (A : Subgroup T) (r x : MulAut T)
    (hcentral : A ≤ Subgroup.center T) (hodd : Odd (orderOf r))
    (hrA : ∀ a ∈ A, r a ∈ A) (hxA : ∀ a ∈ A, x a ∈ A)
    (hinverts : x * r * x⁻¹ = r⁻¹)
    (hfree : ∀ a ∈ A, r a = a → a = 1)
    (hindex : (fixedSubgroup x).index = 2)
    (hnontrivial : ∃ a ∈ A, x a ≠ a) :
    (A ⊔ fixedSubgroup r = ⊤) ∧ Disjoint A (fixedSubgroup r) ∧
      ∀ b ∈ fixedSubgroup r, x b = b := by
  apply fixed_complement_of_inverted_odd_sup_eq_top A r x hcentral hodd hrA hxA hinverts hfree
  obtain ⟨a, ha, hxa⟩ := hnontrivial
  have haf : a ∉ fixedSubgroup x := by simpa only [mem_fixedSubgroup] using hxa
  apply top_unique
  intro t _
  by_cases ht : t ∈ fixedSubgroup x
  · exact (show fixedSubgroup x ≤ A ⊔ fixedSubgroup x from le_sup_right) ht
  have hat : a⁻¹ * t ∈ fixedSubgroup x := by
    rw [Subgroup.mul_mem_iff_of_index_two hindex, Subgroup.inv_mem_iff]
    exact iff_of_false haf ht
  simpa using Subgroup.mul_mem_sup ha hat
end MulAut
