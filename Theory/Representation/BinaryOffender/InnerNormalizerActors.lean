module

public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.Quotient
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.Representation.BinaryIrreducibleCentralizer

/-!
# Elementary normalizer actors when involutory automorphisms are inner

Conjugation sends a normalizing involution to an involutory automorphism of
its faithful action image. An inner representative of square one differs
from it by a centralizing involution, which binary Schur's lemma kills.
Consequently every elementary subgroup in the full linear normalizer is the
image of an elementary subgroup of the original group, with the original
operators retained. No almost-simple hypothesis on the full normalizer is
assumed.

This is the outer-actor step in Guralnick--Malle II, Lemma 8.8, internal p.57,
used by Aschbacher--Smith K.3, printed p.457.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) G V)

/-- An involution in the full normalizer is an actual original operator. -/
theorem normalizer_involution_inner
    (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (hinner : ∀ a : MulAut G, a ^ 2 = 1 → ∃ x : G, x ^ 2 = 1 ∧ a = MulAut.conj x)
    (t : linearNormalizer σ) (ht : t ^ 2 = 1) :
    ∃ x : G, x ^ 2 = 1 ∧ t.val = σ.asGroupHom x := by
  have hσ : Function.Injective σ.asGroupHom := fun _ _ h => hf (congrArg Units.val h)
  let e : G ≃* actionImage σ := MonoidHom.ofInjective hσ
  let t' : normalizer (actionImage σ : Set (Module.End (ZMod 2) V)ˣ) :=
    ⟨t.val, t.property⟩
  have ht' : t' ^ 2 = 1 := Subtype.ext (congrArg Subtype.val ht)
  let α := (actionImage σ).normalizerMonoidHom t'
  have ha2 : (MulAut.congr e.symm α) ^ 2 = 1 := by
    rw [← map_pow, show α ^ 2 = 1 by
      dsimp [α]
      rw [← map_pow, ht', map_one], map_one]
  obtain ⟨x, hx2, hx⟩ := hinner (MulAut.congr e.symm α) ha2
  have ha : α = MulAut.conj (e x) := by
    apply (MulAut.congr e.symm).injective
    rw [MulAut.congr_conj, e.symm_apply_apply]
    exact hx
  let y : (Module.End (ZMod 2) V)ˣ := (e x).val
  have hy2 : y ^ 2 = 1 := by
    change σ.asGroupHom x ^ 2 = 1
    rw [← map_pow, hx2, map_one]
  have ht2 : t.val ^ 2 = 1 := congrArg Subtype.val ht
  have he (g : actionImage σ) : t.val * g.val * t.val⁻¹ = y * g.val * y⁻¹ :=
    congrArg Subtype.val (MulEquiv.congr_fun ha g)
  have hty : Commute t.val y := by
    have h := he (e x)
    change t.val * y * t.val⁻¹ = y * y * y⁻¹ at h
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hu2 : (y⁻¹ * t.val) ^ 2 = 1 := by
    rw [hty.symm.inv_left.mul_pow, inv_pow, hy2, ht2, inv_one, one_mul]
  have huc : y⁻¹ * t.val ∈ centralizer (actionImage σ : Set _) := by
    apply mem_centralizer_iff.mpr
    intro g hg
    have hconj : (y⁻¹ * t.val) * g * (y⁻¹ * t.val)⁻¹ = g := by
      calc
        _ = y⁻¹ * (t.val * g * t.val⁻¹) * y := by group
        _ = y⁻¹ * (y * g * y⁻¹) * y := by rw [he ⟨g, hg⟩]
        _ = g := by group
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  let : IsIrreducible ((Units.coeHom (Module.End (ZMod 2) V)).comp
      (actionImage σ).subtype) :=
    (irreducible_comp_surjective_iff (actionHom σ)
      σ.asGroupHom.rangeRestrict_surjective (imageRepresentation σ)).mp hi
  have hu := BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
    (Units.coeHom (Module.End (ZMod 2) V)) (actionImage σ)
    (fun _ _ h => Units.ext h) hu2 huc
  exact ⟨x, hx2, (inv_mul_eq_one.mp hu).symm⟩


/-- The literal action homomorphism into the full linear normalizer. -/
@[expose] noncomputable def normalizerEmbedding : G →* linearNormalizer σ :=
  (Subgroup.inclusion (actionImage σ).le_normalizer).comp (actionHom σ)

/-- Faithfulness is retained by the normalizer embedding. -/
theorem normalizerEmbedding_injective (hf : Function.Injective σ) :
    Function.Injective (normalizerEmbedding σ) := by
  intro x y h
  exact hf (congrArg (fun z : linearNormalizer σ => z.val.val) h)

/-- Every elementary normalizer actor is the image of an original actor. -/
theorem elementary_normalizer_is_image
    (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (hinner : ∀ a : MulAut G, a ^ 2 = 1 → ∃ x : G, x ^ 2 = 1 ∧ a = MulAut.conj x)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) :
    ∃ B : Subgroup G, IsElementaryTwo B ∧ B.map (normalizerEmbedding σ) = A := by
  let : IsElementaryAbelian 2 A := hA.2
  let j := normalizerEmbedding σ
  have hj : Function.Injective j := normalizerEmbedding_injective σ hf
  let B := A.comap j
  have hm : B.map j = A := by
    apply le_antisymm (map_comap_le _ _)
    intro t ht
    obtain ⟨x, _, hx⟩ := normalizer_involution_inner σ hf hi hinner t
      (elemPow_eq_one_of_isElementaryAbelian t ht)
    have hjx : j x = t := Subtype.ext hx.symm
    exact ⟨x, show j x ∈ A from hjx.symm ▸ ht, hjx⟩
  have hB : IsElementaryAbelian 2 B := {
    toIsMulCommutative := A.comap_injective_isMulCommutative hj
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      apply hj
      change j ((x : G) ^ 2) = j 1
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (j x) x.property }
  refine ⟨B, ⟨?_, hB⟩, hm⟩
  intro hb
  apply hA.1
  rw [← hm, hb, Subgroup.map_bot]

end Representation.BinaryOffender
