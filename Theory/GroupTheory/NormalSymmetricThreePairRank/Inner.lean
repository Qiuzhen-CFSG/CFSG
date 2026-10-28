module

public import Theory.GroupTheory.SpecificGroups.PermThreeProduct
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group

/-!
# Inner action on a normal symmetric-three pair

Automorphisms of S₃ are inner: the images of two generating transpositions
are distinct transpositions and can be simultaneously conjugated back.
Consequently an ambient element preserving both coordinate subgroups of a
normal S₃ × S₃ acts by an inner automorphism, and lies in K C_A(K).
The coordinates are actual pullbacks through the given group isomorphism.

Source: the finite-group argument in Aschbacher–Smith, proof of 13.8.5,
combined manuscript of 1 March 2004, printed p.947 (PDF p.964).
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.NormalSymmetricThreePairRank
local notation "S3" => Equiv.Perm (Fin 3)
private def s : S3 := Equiv.swap 0 1
private def t : S3 := Equiv.swap 1 2
private theorem words : ∀ x : S3, x = 1 ∨ x = s ∨ x = t ∨ x = s * t ∨ x = t * s ∨ x = s * t * s := by
  decide +kernel
private theorem pairs : ∀ x y : S3,
    (x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y ∧ x ^ 2 = 1 ∧ y ^ 2 = 1) →
    ∃ k : S3, k * s * k⁻¹ = x ∧ k * t * k⁻¹ = y := by
  decide +kernel

/-- Every automorphism of the three-letter symmetric group is inner. -/
theorem symmetricThree_aut_inner (α : MulAut S3) : ∃ k, α = MulAut.conj k := by
  obtain ⟨k, hs, ht⟩ := pairs (α s) (α t) ⟨
    fun h => (by decide : s ≠ 1) (α.injective (h.trans α.map_one.symm)),
    fun h => (by decide : t ≠ 1) (α.injective (h.trans α.map_one.symm)),
    fun h => (by decide : s ≠ t) (α.injective h),
    by rw [← map_pow]; exact (by decide : s ^ 2 = 1) ▸ α.map_one,
    by rw [← map_pow]; exact (by decide : t ^ 2 = 1) ▸ α.map_one⟩
  refine ⟨k, ?_⟩
  have hs' : α s = (MulAut.conj k) s := hs.symm
  have ht' : α t = (MulAut.conj k) t := ht.symm
  ext x
  rcases words x with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [map_one, map_mul, hs', ht']

/-- The centre of the concrete three-letter symmetric group is trivial. -/
theorem symmetricThree_center_trivial : ∀ x : S3, (∀ y, y * x=x * y) → x=1 := by
  decide +kernel

/-- A factor-preserving automorphism of the product is inner. -/
theorem pair_aut_inner (α : MulAut (S3 × S3))
    (h₁ : ∀ x : S3, (α (x, 1)).2 = 1)
    (h₂ : ∀ x : S3, (α (1, x)).1 = 1) :
    ∃ k, α = MulAut.conj k := by
  let f₁ : S3 →* S3 := (MonoidHom.fst S3 S3).comp
    (α.toMonoidHom.comp (MonoidHom.inl S3 S3))
  let f₂ : S3 →* S3 := (MonoidHom.snd S3 S3).comp
    (α.toMonoidHom.comp (MonoidHom.inr S3 S3))
  have hi₁ : Function.Injective f₁ := by
    intro x y h
    exact congrArg Prod.fst (α.injective (Prod.ext h ((h₁ x).trans (h₁ y).symm)))
  have hi₂ : Function.Injective f₂ := by
    intro x y h
    exact congrArg Prod.snd (α.injective (Prod.ext ((h₂ x).trans (h₂ y).symm) h))
  obtain ⟨k₁, hk₁⟩ := symmetricThree_aut_inner
    (MulEquiv.ofBijective f₁ ⟨hi₁, Finite.surjective_of_injective hi₁⟩)
  obtain ⟨k₂, hk₂⟩ := symmetricThree_aut_inner
    (MulEquiv.ofBijective f₂ ⟨hi₂, Finite.surjective_of_injective hi₂⟩)
  have hf₁ (x : S3) : (α (x, 1)).1 = k₁ * x * k₁⁻¹ := DFunLike.congr_fun hk₁ x
  have hf₂ (x : S3) : (α (1, x)).2 = k₂ * x * k₂⁻¹ := DFunLike.congr_fun hk₂ x
  refine ⟨(k₁, k₂), ?_⟩
  apply MulEquiv.ext
  rintro ⟨x, y⟩
  have he : (x, y) = (x, 1) * (1, y) := by simp
  rw [he, map_mul]
  apply Prod.ext <;> simp [hf₁, hf₂, h₁, h₂, MulAut.conj_apply]

variable {A : Type*} [Group A] (K : Subgroup A) [K.Normal]
  (e : K ≃* (S3 × S3))

/-- The actual first coordinate subgroup inside the ambient group. -/
def firstFactor : Subgroup A :=
  (((⊤ : Subgroup S3).prod ⊥).comap e.toMonoidHom).map K.subtype

/-- The actual second coordinate subgroup inside the ambient group. -/
def secondFactor : Subgroup A :=
  (((⊥ : Subgroup S3).prod ⊤).comap e.toMonoidHom).map K.subtype

/-- An ambient element normalizing both coordinates acts on K by an inner automorphism. -/
theorem normalizing_pair_inner (b : A)
    (h₁ : b ∈ normalizer (firstFactor K e : Set A))
    (h₂ : b ∈ normalizer (secondFactor K e : Set A)) :
    ∃ k : K, ∀ x : K, b * x * b⁻¹ = (k * x * k⁻¹ : K) := by
  let α : MulAut (S3 × S3) := e.symm.trans ((MulAut.conjNormal b).trans e)
  have he₁ (x : S3) : (α (x, 1)).2 = 1 := by
    let y : K := e.symm (x, 1)
    have hy : (y : A) ∈ firstFactor K e := by
      exact ⟨y, by simp [y, Subgroup.mem_prod], rfl⟩
    have hm := (mem_normalizer_iff.mp h₁) y
    have hc : b * (y:A) * b⁻¹ ∈ firstFactor K e := hm.mp hy
    obtain ⟨z, hz, he⟩ := hc
    have hez : z = MulAut.conjNormal b y := Subtype.ext he
    rw [hez] at hz
    exact hz.2
  have he₂ (x : S3) : (α (1, x)).1 = 1 := by
    let y : K := e.symm (1, x)
    have hy : (y : A) ∈ secondFactor K e := by
      exact ⟨y, by simp [y, Subgroup.mem_prod], rfl⟩
    have hm := (mem_normalizer_iff.mp h₂) y
    have hc : b * (y:A) * b⁻¹ ∈ secondFactor K e := hm.mp hy
    obtain ⟨z, hz, he⟩ := hc
    have hez : z = MulAut.conjNormal b y := Subtype.ext he
    rw [hez] at hz
    exact hz.1
  obtain ⟨k, hk⟩ := pair_aut_inner α he₁ he₂
  refine ⟨e.symm k, fun x => ?_⟩
  change ((MulAut.conjNormal b x : K) : A) = _
  apply congrArg (fun z : K => (z : A))
  apply e.injective
  have hx := DFunLike.congr_fun hk (e x)
  simpa [α, MulAut.conj_apply] using hx

/-- The factor normalizer is contained in K times its ambient centralizer. -/
theorem normalizing_pair_decomposition (b : A)
    (h₁ : b ∈ normalizer (firstFactor K e : Set A))
    (h₂ : b ∈ normalizer (secondFactor K e : Set A)) :
    ∃ k ∈ K, ∃ c ∈ centralizer (K : Set A), b = k * c := by
  obtain ⟨k, hk⟩ := normalizing_pair_inner K e b h₁ h₂
  refine ⟨k, k.property, (k:A)⁻¹ * b, ?_, by group⟩
  apply mem_centralizer_iff.mpr
  intro x hx
  have he := hk ⟨x, hx⟩
  change b * x * b⁻¹ = (k:A) * x * (k:A)⁻¹ at he
  have hh := congrArg (fun z : A => (k:A)⁻¹ * z * b) he
  simpa [mul_assoc] using hh.symm

end Theory.GroupTheory.NormalSymmetricThreePairRank
