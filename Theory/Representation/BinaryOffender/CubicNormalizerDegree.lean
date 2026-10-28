module

public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.ThreeConjugateNormalizer.CentralCover
public import Theory.GroupTheory.PrimeRankCentralCover

/-!
# Cubic degree bounds for an ambient binary action

Let L be a normal subgroup acting faithfully and irreducibly on V. The ambient
action embeds into the full linear normalizer of L. An elementary actor of
ratio at most two contains an involution moving at most twice the actor rank;
three conjugates spanning the component therefore bound dim V by six times
the automorphism two-rank of its central quotient.

Only the actual ambient action is assumed to have small cubic ratio. No SQTK
condition on its full normalizer, or FF hypothesis, is used. The central-cover
version retains the specified quotient equivalence and all outer actions.
Source application: Aschbacher–Smith, Chapter K, printed pp.451 and 457.
-/

public section
namespace Representation.BinaryOffender
open Subgroup Theory.GroupTheory
open scoped ENNReal

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]

/-- A cubic actor of ratio at most two bounds the degree through the literal
normalizer of the component image, including ambient outer involutions. -/
theorem finrank_le_six_mul_image_aut_rank_of_cubic
    [Nontrivial L] (hf : Function.Injective ρ)
    (hi : Representation.IsIrreducible (ρ.comp L.subtype))
    (hgen : NormalizerThreeConjugates (ρ.comp L.subtype))
    (hc : cubicRatio ρ ≤ 2) :
    Module.finrank (ZMod 2) V ≤
      6 * primeRank 2 (MulAut (actionImage (ρ.comp L.subtype))) := by
  let σ := ρ.comp L.subtype
  let j : G →* linearNormalizer σ :=
    ρ.asGroupHom.codRestrict _ (fun g =>
      actionImage_le_linearNormalizer ρ L ⟨g, rfl⟩)
  have hj : Function.Injective j := by
    intro a b hab
    apply hf
    exact congrArg (fun x : linearNormalizer σ => (x.val : Module.End (ZMod 2) V)) hab
  obtain ⟨A, hA, _, hratio⟩ := (cubicRatio_le_nat_iff ρ 2).mp hc
  let : IsElementaryAbelian 2 A := hA.2
  have hAm : IsElementaryAbelian 2 (A.map j) := IsElementaryAbelian.map j
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have hcard := (primeRank_le_iff_elementary_card_le (linearNormalizer σ)).mp
    (primeRank_linearNormalizer_le σ hi) (A.map j) hAm
  have hrank : rank A ≤ primeRank 2 (MulAut (actionImage σ)) := by
    have hh := Nat.log_mono_right (b := 2) hcard
    have hh' : rank (A.map j) ≤ primeRank 2 (MulAut (actionImage σ)) := by
      simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
    rwa [rank_map_injective j hj] at hh'
  obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hja : j a ≠ 1 := fun h => ha1 (hj (h.trans j.map_one.symm))
  have hja2 : j a ^ 2 = 1 := by
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian a ha, map_one]
  obtain ⟨g, h, hgh⟩ := hgen (j a) hja hja2
  have hσ : Function.Injective σ := hf.comp L.subtype_injective
  have hd := SL2SevenCentralProduct.finrank_le_three_mul_fixedCodim_of_three_conjugates
    (normalizerRepresentation σ) _ (normalizerImage_subspaceCommutator_eq_top σ hσ hi)
    (j a) g h hgh
  have he : fixedCodim (normalizerRepresentation σ) (zpowers (j a)) =
      fixedCodim ρ (zpowers a) := by
    rw [fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_eq_displacement_rank]
    rfl
  rw [he] at hd
  have hfix : fixedSpace ρ A ≤ fixedSpace ρ (zpowers a) := by
    intro v hv b
    exact hv ⟨b, (zpowers_le.mpr ha) b.property⟩
  have hmono := Submodule.finrank_mono hfix
  have h₁ := fixedCodim_add_finrank ρ A
  have h₂ := fixedCodim_add_finrank ρ (zpowers a)
  have hcodim : fixedCodim ρ (zpowers a) ≤ fixedCodim ρ A := by omega
  calc
    Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (zpowers a) := hd
    _ ≤ 3 * (2 * rank A) := Nat.mul_le_mul_left 3 (hcodim.trans hratio)
    _ ≤ 6 * primeRank 2 (MulAut (actionImage σ)) := by omega

/-- Central-quotient geometry gives a degree window for the original ambient
representation; arbitrary faithful central covers are retained. -/
theorem finrank_le_six_mul_of_cubic_central_quotient
    [IsQuasisimple L] {S : Type*} [Group S]
    (hf : Function.Injective ρ) (hi : Representation.IsIrreducible (ρ.comp L.subtype))
    (e : L ⧸ center L ≃* S) (hgen : ThreeConjugateAutomorphisms S)
    {r : ℕ} (hr : primeRank 2 (MulAut S) ≤ r) (hc : cubicRatio ρ ≤ 2) :
    Module.finrank (ZMod 2) V ≤ 6 * r := by
  let σ := ρ.comp L.subtype
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  let : Finite S := Finite.of_surjective e e.surjective
  have hσ : Function.Injective σ := hf.comp L.subtype_injective
  have hk : σ.ker ≤ center L := by
    rw [(MonoidHom.ker_eq_bot_iff σ).mpr hσ]
    exact bot_le
  let := actionImage_quasisimple_of_central_kernel σ hk
  let e' : actionImage σ ⧸ center (actionImage σ) ≃* S :=
    (simpleQuotientEquivImage σ hk).symm.trans e
  have hbound := automorphism_primeRank_le_quotient_center (E := actionImage σ) 2
  rw [primeRank_equiv 2 (MulAut.congr e')] at hbound
  exact (finrank_le_six_mul_image_aut_rank_of_cubic ρ L hf hi
    (normalizerThreeConjugates_of_centralCover σ hσ hi e hgen) hc).trans
      (Nat.mul_le_mul_left 6 (hbound.trans hr))

end Representation.BinaryOffender
