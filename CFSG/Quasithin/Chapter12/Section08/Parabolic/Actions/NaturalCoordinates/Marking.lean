module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalPreimage.Coordinates
import all CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryModule

/-!
# Simultaneous markings of the parabolic quotient

The image of U has order two. Its internal conjugate, representing the
original Uᵍ, has a distinct nonidentity element because the two images
generate S₃. A single inner automorphism marks them by (1 2) and (0 2).
The internal representative preserves the original Wᵍ.

The private import of BinaryModule is an intentional internal proof split:
it supplies the equation for its unexposed projection without changing that
shared module. Only the equation below is exported, not its private helpers.

Source: Aschbacher–Smith, Lemma 12.8.9(1–3), printed pp.852–853.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise TensorProduct
open InvertedCubicTensor
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Evaluation of the existing quotient projection on its literal representative. -/
theorem binaryCoreProjection_apply (F : InvariantFlag T V n) (L : Subgroup G)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃) (i : F.I₂ L) :
    F.binaryCoreProjection L e i = e (QuotientGroup.mk' (pCore 2 (F.I₂ L)) i) := by
  unfold binaryCoreProjection
  rfl

private theorem mark_two_involutions : ∀ a b : Equiv.Perm (Fin 3),
    a ^ 2 = 1 ∧ a ≠ 1 ∧ b ^ 2 = 1 ∧ b ≠ 1 ∧ a ≠ b →
    ∃ c : Equiv.Perm (Fin 3), c * a * c⁻¹ = Equiv.swap 1 2 ∧ c * b * c⁻¹ = Equiv.swap 0 2 := by
  decide

private theorem involution_not_central : ∀ a : S₃,
    a ^ 2 = 1 → a ≠ 1 → ∃ b : S₃, b * a ≠ a * b := by
  decide

/-- Mark both original conjugate U-images using one inner automorphism. -/
theorem binary_marked_quotient (F : InvariantFlag T V n) (L : Subgroup G)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hPH : (F.P L).pCoreIn 2 ≤ F.H)
    (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    (hindex : F.W.relIndex F.U = 2) :
    ∃ (e' : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃)
      (u h : F.I₂ L),
      (u : G) ∈ F.U ∧ (u : G) ∉ F.W ∧ F.X (h : G) = F.X g ∧
      (∀ v : F.I₂ L, (v : G) ∈ F.U → (v : G) ∉ F.W →
        F.binaryCoreProjection L e' v = Equiv.swap 1 2) ∧
      F.binaryCoreProjection L e' (h⁻¹ * u * h) = Equiv.swap 0 2 := by
  classical
  let I := F.I₂ L
  let U := F.U.subgroupOf I
  let π := F.binaryCoreProjection L e
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : π.ker = pCore 2 I := by
    ext i
    change e (QuotientGroup.mk i) = 1 ↔ i ∈ pCore 2 I
    rw [← e.map_one, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hUI : F.U ≤ I := le_conjugateSpanBy _ _
  have hW : F.U ⊓ I.pCoreIn 2 = F.W := by
    rw [← hcore, ← inf_assoc, inf_eq_left.mpr hUI]
    rfl
  have hUf : Nat.card (U.map π) = 2 := by
    rw [← relIndex_ker U π, hk]
    have he := relIndex_map_map_of_injective (pCore 2 I) U I.subtype_injective
    rw [show U.map I.subtype = F.U from map_subgroupOf_eq_of_le hUI] at he
    change (I.pCoreIn 2).relIndex F.U = (pCore 2 I).relIndex U at he
    rw [← he, ← inf_relIndex_left, hW]
    exact hindex
  obtain ⟨a, ha, huniq⟩ := (Nat.card_eq_two_iff' (1 : U.map π)).mp hUf
  obtain ⟨u, hu, hua⟩ := a.property
  have hu1 : π u ≠ 1 := fun he => ha (Subtype.ext (hua.symm.trans he))
  have huw : (u : G) ∉ F.W := by
    intro hw
    have hs := (hW.ge hw).2
    obtain ⟨v, hv, hvu⟩ := hs
    have hvu' : v = u := Subtype.ext hvu
    exact hu1 (show u ∈ π.ker from hk ▸ (hvu' ▸ hv))
  have hall (v : I) (hv : (v : G) ∈ F.U) : π v = 1 ∨ π v = π u := by
    by_cases he : π v = 1
    · exact Or.inl he
    · exact Or.inr ((congrArg Subtype.val (huniq ⟨π v, mem_map_of_mem π hv⟩
        (fun h => he (congrArg Subtype.val h)))).trans hua.symm)
  have ht : (π u) ^ 2 = 1 := by
    have hp := pow_card_eq_one' (x := (⟨π u, mem_map_of_mem π hu⟩ : U.map π))
    rw [hUf] at hp
    exact congrArg Subtype.val hp
  obtain ⟨h, hh, _, hUg, hX, _⟩ := F.exists_internal_natural_representative
    L g hgP hgH hfactor hPH hcore
  let hi : I := ⟨h, hh⟩
  let t := π (hi⁻¹ * u * hi)
  have htdef : t = (π hi)⁻¹ * π u * π hi := by simp [t]
  have ht2 : t ^ 2 = 1 := by
    rw [htdef]
    calc
      ((π hi)⁻¹ * π u * π hi) ^ 2 = (π hi)⁻¹ * (π u) ^ 2 * π hi := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [ht]; simp
  have ht1 : t ≠ 1 := by
    rw [htdef]
    intro he
    apply hu1
    calc
      π u = π hi * ((π hi)⁻¹ * π u * π hi) * (π hi)⁻¹ := by group
      _ = 1 := by rw [he]; simp
  have hne : π u ≠ t := by
    intro he
    let K := (centralizer ({π u} : Set S₃)).comap π
    have hK (v : I) (hv : (v : G) ∈ F.U) : v ∈ K := by
      change ∀ b ∈ ({π u} : Set S₃), b * π v = π v * b
      intro b hb
      have hb' : b = π u := Set.mem_singleton_iff.mp hb
      subst b
      rcases hall v hv with hv1 | hvu
      · simp [hv1]
      · rw [hvu]
    have hUK : F.U ≤ K.map I.subtype := by
      intro v hv
      exact ⟨⟨v, hUI hv⟩, hK _ hv, rfl⟩
    have hUgK : conjugate F.U g ≤ K.map I.subtype := by
      rw [← hUg]
      rintro v ⟨w, hw, rfl⟩
      let wi : I := ⟨w, hUI hw⟩
      refine ⟨hi⁻¹ * wi * hi, ?_, by simp [hi, wi]⟩
      change ∀ b ∈ ({π u} : Set S₃), b * π (hi⁻¹ * wi * hi) =
        π (hi⁻¹ * wi * hi) * b
      intro b hb
      have hb' : b = π u := Set.mem_singleton_iff.mp hb
      subst b
      simp only [map_mul, map_inv]
      rcases hall wi hw with hw1 | hwu
      · simp [hw1]
      · rw [hwu, ← htdef, ← he]
    have hIK : I ≤ K.map I.subtype := by
      change F.I₂ L ≤ _
      rw [← hgen]
      exact sup_le hUK hUgK
    obtain ⟨b, hb⟩ := involution_not_central (π u) ht hu1
    obtain ⟨v, rfl⟩ := hπ b
    obtain ⟨w, hw, hwv⟩ := hIK v.property
    have hwv' : w = v := Subtype.ext hwv
    subst w
    exact hb (((show π v ∈ centralizer ({π u} : Set S₃) from hw) _ (by simp)).symm)
  obtain ⟨c, hcU, hcX⟩ := mark_two_involutions (π u) t ⟨ht, hu1, ht2, ht1, hne⟩
  let e' := e.trans (MulAut.conj c)
  refine ⟨e', u, hi, hu, huw, hX, ?_, ?_⟩
  · intro v hv hvw
    have hv1 : π v ≠ 1 := by
      intro he
      have hvS : (v : G) ∈ I.pCoreIn 2 :=
        mem_map_of_mem I.subtype (hk ▸ (show v ∈ π.ker from he))
      exact hvw (hW ▸ (show (v : G) ∈ F.U ⊓ I.pCoreIn 2 from ⟨hv, hvS⟩))
    have hvu := (hall v hv).resolve_left hv1
    change c * π v * c⁻¹ = _
    rw [hvu, hcU]
  · exact hcX
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
