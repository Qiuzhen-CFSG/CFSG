module

public import Theory.Representation.BinaryOffender.CubicConjugateBound
public import Theory.Representation.BinaryOffender.UniformFixedSpace

/-!
# Equality in the cubic actor displacement bound

When an element of A attains the upper displacement bound for A, its fixed
space equals C_V(A). Conjugating elements of A by an element centralizing
that first actor preserves the common fixed space. Products of these actors
therefore cannot have larger displacement. This supplies the strict step
that a lone involution estimate cannot prove.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript p.9, used in Aschbacher--Smith K.2, printed p.453. The applications
to parameters 11, 17 and 25 are in LinearExclusion.RankOneSmall. The local
group and representation calculations producing the actors are separate.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- An element attaining the rank bound has the whole actor's fixed space. -/
theorem fixedSpace_eq_of_saturated_actor {A : Subgroup G} {t : G} {n r : ℕ}
    (ht : t ∈ A) (hr : rank A ≤ r)
    (hsmall : fixedCodim ρ A ≤ n * rank A)
    (htlarge : n * r ≤ fixedCodim ρ (zpowers t)) :
    fixedCodim ρ A = n * r ∧ fixedSpace ρ A = fixedSpace ρ (zpowers t) := by
  have hd := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr ht))
  have hdA := fixedCodim_add_finrank ρ A
  have hdt := fixedCodim_add_finrank ρ (zpowers t)
  have hmul := Nat.mul_le_mul_left n hr
  refine ⟨by omega, fixedSpace_eq_of_fixedCodim_eq ρ (zpowers_le.mpr ht) (by omega)⟩

/-- Products from A and a conjugate inside C_G(t) fix the common fixed space. -/
theorem fixedCodim_centralizer_product_le {A : Subgroup G} {t g a b : G}
    (heq : fixedSpace ρ A = fixedSpace ρ (zpowers t))
    (hg : Commute g t) (ha : a ∈ A) (hb : b ∈ A) :
    fixedCodim ρ (zpowers (a * (g * b * g⁻¹))) ≤ fixedCodim ρ (zpowers t) := by
  have hfix : fixedSpace ρ (zpowers t) ≤
      fixedSpace ρ (zpowers (a * (g * b * g⁻¹))) := by
    intro v hv
    have htv := (mem_fixedSpace_zpowers_iff ρ t v).mp hv
    have hw : ρ g⁻¹ v ∈ fixedSpace ρ (zpowers t) := by
      rw [mem_fixedSpace_zpowers_iff]
      rw [← Module.End.mul_apply, ← map_mul, hg.inv_left.symm.eq,
        map_mul, Module.End.mul_apply, htv]
    have hav : ρ a v = v := (show v ∈ fixedSpace ρ A from heq.symm ▸ hv) ⟨a, ha⟩
    have hbw : ρ b (ρ g⁻¹ v) = ρ g⁻¹ v := (heq.symm ▸ hw) ⟨b, hb⟩
    have hginv : ρ g (ρ g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    rw [mem_fixedSpace_zpowers_iff]
    simp only [map_mul, Module.End.mul_apply, hbw, hginv, hav]
  have hd := Submodule.finrank_mono hfix
  have hdt := fixedCodim_add_finrank ρ (zpowers t)
  have hdp := fixedCodim_add_finrank ρ (zpowers (a * (g * b * g⁻¹)))
  omega

/-- A product of larger displacement rules out equality at any threshold. -/
theorem not_small_actor_of_centralizer_product {A : Subgroup G} {t g a b : G}
    {n r : ℕ} (hr : rank A ≤ r) (ht : t ∈ A)
    (htlarge : n * r ≤ fixedCodim ρ (zpowers t))
    (hg : Commute g t) (ha : a ∈ A) (hb : b ∈ A)
    (hprod : n * r < fixedCodim ρ (zpowers (a * (g * b * g⁻¹)))) :
    ¬ fixedCodim ρ A ≤ n * rank A := by
  intro hsmall
  obtain ⟨hcodim, heq⟩ := fixedSpace_eq_of_saturated_actor ρ ht hr hsmall htlarge
  have heqdim : fixedCodim ρ A = fixedCodim ρ (zpowers t) := by
    have hdim := congrArg (fun U : Submodule (ZMod 2) V => Module.finrank (ZMod 2) U) heq
    have hdA := fixedCodim_add_finrank ρ A
    have hdt := fixedCodim_add_finrank ρ (zpowers t)
    omega
  have hle := fixedCodim_centralizer_product_le ρ heq hg ha hb
  omega

end Representation.BinaryOffender
