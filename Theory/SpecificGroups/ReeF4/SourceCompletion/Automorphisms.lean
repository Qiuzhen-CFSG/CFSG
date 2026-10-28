module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms

/-!
# The native automorphism-order bound for general Ree extensions

Sylow conjugacy puts an arbitrary automorphism into the positive-subgroup
stabilizer. The proved opposite-pair and signed-block recovery then give one
common inner-times-field expression on the generating root blocks. The
coefficient-field Frobenius has period 2m+1. Thus the native automorphism
group, and every group faithfully represented in it, has order at most
(2m+1)|ReeF4.Model m|. No simplicity or perfectness hypothesis is needed.

This supplies the field-factor bound for the source extension Mbar in
F.4.24,43–44. It does not construct a representation from two local source
actions: that compatible extension remains an independent obligation of
the ambient-recognition argument. The Chapter6/12 consumers keep it explicit.
Source: GLS3 §2.5; Aschbacher–Smith 5.3.2 and F.4.24,43–44,
printed pp.659,287,296 (`refs/quasithin.pdf`).
-/

public noncomputable section
namespace ReeF4.SourceCompletion
open Subgroup LargeLocalSeeds Parabolics
open Parabolics.OuterLocal Parabolics.OuterLocal.LargeAutomorphisms

/-- Every native automorphism has a single common inner-times-field expression. -/
theorem inner_field (m : ℕ) (hm : 0 < m) (a : MulAut (Model m)) :
    ∃ (g : Model m) (k : ℕ), a = MulAut.conj g * fieldAutomorphism m ^ k := by
  have hindex : Odd (unipotent m).index :=
    unipotent_index_odd_of_standard (canonicalLocalBlockInput m)
      (FixedBruhat.standardUnipotent_index_odd (canonicalLocalBlockInput m))
  let U := sylowOfOddIndex m hindex
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model m) (a • U) U
  let b : MulAut (Model m) := MulAut.conj g * a
  have hU : (unipotent m).map b.toMonoidHom = unipotent m := by
    change ((b • U : Sylow 2 (Model m)) : Subgroup (Model m)) = (U : Subgroup (Model m))
    exact congrArg (fun P : Sylow 2 (Model m) => (P : Subgroup (Model m)))
      (show b • U = U from by
        rw [show b = MulAut.conj g * a from rfl,mul_smul]
        change g • (a • U) = U
        exact hg)
  have hgen := seed_sup_eq_top m
  obtain ⟨z,hp,hc⟩ := LocalActions.exists_inner_adjustment_preserving_pair_and_blocks
    hm hindex b hU
  obtain ⟨w,σ,hentries⟩ := LocalActions.Semilinear.exists_common_field m hm hindex hgen
    ((MulAut.conj z)⁻¹ * b) hp hc
  obtain ⟨k,hk⟩ := LocalActions.local_actions_of_two_adjustments m
    (LocalActions.simpleBlocks_generate hm hgen) b z w σ hentries
  have hb := form_of_local_actions m b hgen (z*w) k hk
  refine ⟨g⁻¹*(z*w),k,?_⟩
  have hh := congrArg (fun c : MulAut (Model m) => MulAut.conj g⁻¹ * c) hb
  simpa only [b,map_mul,map_inv,mul_assoc,inv_mul_cancel_left] using hh

/-- The odd field degree bounds the full native automorphism group. -/
theorem card_automorphism_le (m : ℕ) (hm : 0 < m) :
    Nat.card (MulAut (Model m)) ≤ (2*m+1)*Nat.card (Model m) := by
  let f : Model m × zpowers (fieldAutomorphism m) → MulAut (Model m) :=
    fun x => MulAut.conj x.1 * x.2.val
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨g,k,hk⟩ := inner_field m hm a
    exact ⟨(g,⟨fieldAutomorphism m ^ k,pow_mem (mem_zpowers _) _⟩),hk.symm⟩
  have hcard := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod,Nat.card_zpowers] at hcard
  have hfield : orderOf (fieldAutomorphism m) ≤ 2*m+1 := by
    exact Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one (fieldAutomorphism_period m))
  exact hcard.trans ((Nat.mul_le_mul_left _ hfield).trans_eq (Nat.mul_comm _ _))

/-- Any faithful extension action satisfies the same field-factor bound.
The action is on the complete native model, not merely on its parabolics. -/
theorem card_extension_le {m : ℕ} (hm : 0 < m)
    {E : Type*} [Group E] (ρ : E →* MulAut (Model m)) (hρ : Function.Injective ρ) :
    Nat.card E ≤ (2*m+1)*Nat.card (Model m) :=
  (Nat.card_le_card_of_injective ρ hρ).trans (card_automorphism_le m hm)

end ReeF4.SourceCompletion
