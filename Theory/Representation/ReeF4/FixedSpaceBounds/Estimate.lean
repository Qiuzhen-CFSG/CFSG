module

public import Theory.Representation.ReeF4.FixedSpaceBounds
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.ScalarRestriction
public import Theory.Representation.Quotient
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.SchurCodimension

/-!
# Reduction of the Ree involution estimate to binary model representations

Every faithful irreducible representation over a finite characteristic-two
field contains a faithful irreducible binary subrepresentation. Its fixed
codimension is at most the field degree times the original fixed codimension.
A trivial center then identifies a quasisimple cover with its actual Ree
quotient; pullback through that equivalence preserves the cyclic fixed space.

These reductions prove the full coefficient-field and cover transport needed
by `CoverInvolutionBound`. The binary model estimate and center triviality
remain explicit premises, not established model facts. In particular, this
module does not yet prove `CoverInvolutionBound m` unconditionally.

The accompanying Schur-field reduction supplies the exact fixed-codimension
identity used with exceptional tensor factorizations and their Frobenius
periods. The remaining basic-factor ranks, tensor estimate, factorization and
finite-group multiplier must all be discharged in the final assembly.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Theorem 8.1 and
Lemma 8.8, internal pp.52, 57--58; GLS3, Corollary 2.8.6(b), Remark 2.8.8.
-/

@[expose] public section
open Subgroup Representation Theory.GroupTheory
namespace ReeF4.FixedSpaceEstimate
universe u v

/-- The remaining estimate on actual binary irreducibles of the literal model. -/
def BinaryModelInvolutionBound (m : ℕ) : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Model m) V),
    ρ.IsIrreducible → Function.Injective ρ →
    ∀ t : Model m, t ≠ 1 → t ^ 2 = 1 →
      10 * (2 * m + 1) ≤ Module.finrank (ZMod 2) (V ⧸ invariants (ρ.comp (zpowers t).subtype))

/-- Pullback identifies the literal cyclic fixed spaces, for any group homomorphism. -/
theorem invariants_comp_zpowers
    {F G H V : Type*} [Field F] [Group G] [Group H]
    [AddCommGroup V] [Module F V] (σ : Representation F H V) (f : G →* H) (t : G) :
    invariants ((σ.comp f).comp (zpowers t).subtype) =
      invariants (σ.comp (zpowers (f t)).subtype) := by
  ext v
  constructor
  · intro hv z
    obtain ⟨n, hn⟩ := z.property
    have h := hv ⟨t ^ n, ⟨n, rfl⟩⟩
    change σ (f (t ^ n)) v = v at h
    change σ z.val v = v
    simpa only [map_zpow, hn] using h
  · intro hv z
    apply hv ⟨f z.val, ?_⟩
    obtain ⟨n, hn⟩ := z.property
    refine ⟨n, ?_⟩
    change (f t) ^ n = f z.val
    change t ^ n = z.val at hn
    rw [← map_zpow, hn]

/-- Transport of the binary model estimate through an actual group equivalence. -/
theorem binary_bound_of_equiv {m : ℕ} (hbinary : BinaryModelInvolutionBound.{v} m)
    {L : Type u} [Group L] (e : L ≃* Model m)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) L V) (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (t : L) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    10 * (2 * m + 1) ≤ Module.finrank (ZMod 2) (V ⧸ invariants (ρ.comp (zpowers t).subtype)) := by
  have hirr : Representation.IsIrreducible (ρ.comp e.symm.toMonoidHom) :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr hi
  have he : e t ≠ 1 := fun h => ht (e.injective (h.trans e.map_one.symm))
  have h := hbinary V (ρ.comp e.symm.toMonoidHom) hirr (hf.comp e.symm.injective)
    (e t) he (by rw [← map_pow, ht2, map_one])
  have heval : e.symm.toMonoidHom (e t) = t := e.symm_apply_apply t
  rw [invariants_comp_zpowers, heval] at h
  exact h

/-- Scalar and cover descent. The model estimate and multiplier consequence remain inputs. -/
theorem coverInvolutionBound_of_binary_bound {m : ℕ}
    (hcenter : ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L],
      Nonempty (L ⧸ center L ≃* Model m) → center L = ⊥)
    (hbinary : BinaryModelInvolutionBound.{v} m) : CoverInvolutionBound.{u,v} m := by
  intro L _ _ _ he E W _ _ _ _ _ _ _ σ hi hf t ht ht2
  let : σ.IsIrreducible := hi
  let : Module (ZMod 2) W := Module.compHom W (algebraMap (ZMod 2) E)
  let : IsScalarTower (ZMod 2) E W := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  let : FiniteDimensional (ZMod 2) W := Module.Finite.trans (R := ZMod 2) E W
  obtain ⟨e⟩ := he
  let f : L ≃* Model m := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (hcenter L ⟨e⟩).symm).trans e)
  apply fixedCodim_ge_of_scalar_irreducibles σ hf (zpowers t) (10 * (2 * m + 1))
  intro U hU hUf
  exact binary_bound_of_equiv hbinary f U.toRepresentation hU hUf t ht ht2

end ReeF4.FixedSpaceEstimate
