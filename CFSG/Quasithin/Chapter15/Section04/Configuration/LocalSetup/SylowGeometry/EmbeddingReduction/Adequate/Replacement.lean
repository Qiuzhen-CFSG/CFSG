module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Adequate
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# Residual replacement with Held retained

The adequate intrinsic theorem gives three possible actual components.
The residual identity supplies the same Sylow-maximal replacement KU as in
the original source argument. Idempotence and monotonicity identify the
residual there with the original K; applying the adequate theorem again
identifies its normal closure. Each component alternative restricts to KU.
No original Held-excluding embedding theorem or replacement record is assumed.
Source: Aschbacher--Smith, 15.4.20, pp.1163--1164.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem embedded_residual_eq_of_intermediate
    (p : ℕ) [Fact p.Prime] {H K D : Subgroup G}
    (hK : K = (primeToResidual p H).map H.subtype)
    (hKD : K ≤ D) (hDH : D ≤ H) :
    K = (primeToResidual p D).map D.subtype := by
  have hid : (primeToResidual p K).map K.subtype = K := by
    rw [hK, ← map_embedded_primeToResidual_of_hom p (primeToResidual p H) H.subtype,
      embedded_primeToResidual_eq_of_normal p (primeToResidual p H) le_rfl]
  apply le_antisymm
  · calc
      K = (primeToResidual p K).map K.subtype := hid.symm
      _ ≤ (primeToResidual p D).map D.subtype := embedded_primeToResidual_mono p hKD
  · exact (embedded_primeToResidual_mono p hDH).trans_eq hK.symm

variable {κ : GroupClass.{u}}
variable {d : Source.Geometry G} {i j : Bool} {H U : Subgroup G}

/-- Construct the replacement and retain its actual normal closure, residual
and all three literal component alternatives. -/
theorem PlacedX.adequate_replacement (hG : IsSimpleQTKE κ G)
    (embedding : Chapter1.XiEmbedding.AdequateLocalEmbeddingTheorem κ)
    (orbits : ComponentOrbitTheorem κ) (residual : TwoOrbitResidualTheorem κ)
    (h : PlacedX d i j H U) (P : Sylow 3 d.wholeX) :
    let P₀ := (P : Subgroup d.wholeX).map d.wholeX.subtype
    let K := normalClosureIn d.wholeX H
    let D := K ⊔ U
    ∃ _hD : PlacedX d i j D U,
      K = normalClosureIn d.wholeX D ∧ K = (primeToResidual 3 D).map D.subtype ∧
      (BinaryCase D U K ∨ ExchangedCase D U P₀ K ∨ HeldCase D K) := by
  obtain ⟨hK, hb⟩ := h.normalClosure_adequate hG embedding orbits residual P
  have hrepl := h.residual_replacement
  dsimp only at hrepl
  rw [← hK] at hrepl
  obtain ⟨hD, hU, _, hcore⟩ := hrepl
  obtain ⟨placed⟩ := h.replacement_configuration hD hU hcore
  have hUH : U ≤ H := h.sylow_image ▸ map_subtype_le (h.sylow : Subgroup H)
  have hDH : normalClosureIn d.wholeX H ⊔ U ≤ H :=
    sup_le (normalClosureIn_le_overgroup _ _) hUH
  have hres := embedded_residual_eq_of_intermediate 3 hK le_sup_left hDH
  refine ⟨placed, hres.trans
    (placed.normalClosure_adequate hG embedding orbits residual P).1.symm, hres, ?_⟩
  rcases hb with hb | he | hh
  · exact Or.inl (hb.restrict le_sup_left hDH)
  · exact Or.inr (Or.inl (he.restrict hG orbits le_sup_left le_sup_right hDH hD.1))
  · exact Or.inr (Or.inr (hh.restrict le_sup_left hDH))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction
