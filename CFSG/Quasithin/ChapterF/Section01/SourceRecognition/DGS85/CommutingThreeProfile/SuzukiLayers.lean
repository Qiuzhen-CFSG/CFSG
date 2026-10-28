module

public import Theory.Representation.Suzuki.MinimalDegree
public import Theory.Representation.Quotient
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.PGroupCore

/-!
# The Suzuki layer argument on the literal source quotient

For a normal subgroup D of L and U normal in D, retain the actual elementary
abelian quotient D/U and its conjugation action by L/O₂(L). A concrete
noncentral displacement makes that action nontrivial. Under the geometric
upper bound |D/U| ≤ q⁴, the smallest-degree theorem proves irreducibility
and equality. With exact centralizer control the result includes q = 2.
The displayed representative identity prevents replacement of the source
action by an unrelated representation of an isomorphic group.

Apply this with D = Qβ, U = Gβ^(2), or D = Vβ, U = Zβ. These are the
irreducible layers in DGS85 (12.6), p.183, and (12.9)(c2), p.186.
The source geometry must still establish normality, elementary abelianness,
the quotient marking, action descent and the upper bound. The nonbinary
version uses an actual moving pair; the binary version requires the actual
centralizer to be O₂(L). No complete Chapter 12 profile is asserted here.
-/

public noncomputable section
open Subgroup Representation
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile

/-- A concrete noncentral displacement forces the nonbinary literal layer to have order q⁴. -/
theorem suzuki_layer_of_conjugation {L : Type*} [Group L]
    (D : Subgroup L) [D.Normal] (U : Subgroup D) [U.Normal]
    [Finite (D ⧸ U)] [IsElementaryAbelian 2 (D ⧸ U)]
    {m : ℕ} (hm : 1 ≤ m)
    (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m)
    (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (D ⧸ U)))
    (hconj : ∀ l : L, ∀ d : D,
      (ρ (QuotientGroup.mk l) (Additive.ofMul (QuotientGroup.mk d))).toMul =
        QuotientGroup.mk (MulAut.conjNormal l d))
    (hmove : ∃ l : L, ∃ d : D, MulAut.conjNormal l d * d⁻¹ ∉ U)
    (hsmall : Nat.card (D ⧸ U) ≤ (2 ^ (2 * m + 1)) ^ 4) :
    ρ.IsIrreducible ∧ Nat.card (D ⧸ U) = (2 ^ (2 * m + 1)) ^ 4 := by
  let σ := ρ.comp e.symm.toMonoidHom
  have hn : σ ≠ 1 := by
    intro hs
    obtain ⟨l, d, hld⟩ := hmove
    have he : ρ (QuotientGroup.mk l) (Additive.ofMul (QuotientGroup.mk d)) =
        Additive.ofMul (QuotientGroup.mk d) := by
      have hh := DFunLike.congr_fun (DFunLike.congr_fun hs (e (QuotientGroup.mk l)))
        (Additive.ofMul (QuotientGroup.mk d))
      change ρ (e.symm (e (QuotientGroup.mk l))) (Additive.ofMul (QuotientGroup.mk d)) =
        Additive.ofMul (QuotientGroup.mk d) at hh
      simpa only [e.symm_apply_apply] using hh
    have hsame : (QuotientGroup.mk (MulAut.conjNormal l d) : D ⧸ U) =
        QuotientGroup.mk d := (hconj l d).symm.trans (congrArg Additive.toMul he)
    apply hld
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' U) (MulAut.conjNormal l d * d⁻¹) = 1
    rw [map_mul, map_inv]
    change QuotientGroup.mk (MulAut.conjNormal l d) * (QuotientGroup.mk d)⁻¹ = 1
    rw [hsame, mul_inv_cancel]
  obtain ⟨hi, hc⟩ := Representation.Suzuki.irreducible_of_small_card hm σ hn hsmall
  exact ⟨(irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mp hi, hc⟩

/-- Exact centralizer control supplies the same layer conclusion, including q = 2. -/
theorem suzuki_layer_of_centralizer {L : Type*} [Group L]
    (D : Subgroup L) [D.Normal] (U : Subgroup D) [U.Normal]
    [Finite (D ⧸ U)] [IsElementaryAbelian 2 (D ⧸ U)]
    {m : ℕ} (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m)
    (ρ : Representation (ZMod 2) (L ⧸ pCore 2 L) (Additive (D ⧸ U)))
    (hconj : ∀ l : L, ∀ d : D,
      (ρ (QuotientGroup.mk l) (Additive.ofMul (QuotientGroup.mk d))).toMul =
        QuotientGroup.mk (MulAut.conjNormal l d))
    (hcentral : ∀ l : L, (∀ d : D, MulAut.conjNormal l d * d⁻¹ ∈ U) → l ∈ pCore 2 L)
    (hsmall : Nat.card (D ⧸ U) ≤ (2 ^ (2 * m + 1)) ^ 4) :
    ρ.IsIrreducible ∧ Nat.card (D ⧸ U) = (2 ^ (2 * m + 1)) ^ 4 := by
  have hf : Function.Injective ρ := by
    apply ρ.ker_eq_bot_iff.mp
    apply bot_unique
    intro z hz
    change z = 1
    induction z using QuotientGroup.induction_on with
    | H l =>
      apply (QuotientGroup.eq_one_iff l).mpr
      apply hcentral l
      intro d
      have he : ρ (QuotientGroup.mk l) (Additive.ofMul (QuotientGroup.mk d)) =
          Additive.ofMul (QuotientGroup.mk d) :=
        DFunLike.congr_fun (show ρ (QuotientGroup.mk l) = 1 from hz) _
      have hsame : (QuotientGroup.mk (MulAut.conjNormal l d) : D ⧸ U) =
          QuotientGroup.mk d := (hconj l d).symm.trans (congrArg Additive.toMul he)
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' U) (MulAut.conjNormal l d * d⁻¹) = 1
      rw [map_mul, map_inv]
      change QuotientGroup.mk (MulAut.conjNormal l d) * (QuotientGroup.mk d)⁻¹ = 1
      rw [hsame, mul_inv_cancel]
  obtain ⟨hi, hc⟩ := Representation.Suzuki.irreducible_of_faithful_small_card
    (ρ.comp e.symm.toMonoidHom) (hf.comp e.symm.injective) hsmall
  exact ⟨(irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mp hi, hc⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
