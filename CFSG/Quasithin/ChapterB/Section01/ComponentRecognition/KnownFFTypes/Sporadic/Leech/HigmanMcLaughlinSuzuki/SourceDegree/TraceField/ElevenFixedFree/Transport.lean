module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.Contracts
public import Theory.Representation.CommonFixedSpaceTransport
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.GroupTheory.PrimeCyclicCoverage

/-!
# Transport of the HS order-eleven model calculation

The exact HS carrier has only one factor of eleven in its order. Sylow
conjugacy therefore reduces fixed-point-freeness to one actual element of
order eleven. This reduction uses no representation classification.

For universal transport, extend the arbitrary representation and a binary
model to the same algebraic closure. Absolute irreducibility makes every
nonzero intertwiner out of the former injective. Such an injection carries
fixed vectors into the model's fixed space; flat scalar extension then
recovers the original kernel. No binary field of definition is assumed for
the arbitrary representation.

The concrete model and the existence of the nonzero intertwiners remain
explicit premises. `DegreeTwentyModelComparison` specifies the latter;
it does not assert a classification theorem. The final two theorems consume
these premises in the exact `DegreeTwentyElevenFixedFree` contract used by
`degreeTwentyTraceField_of_powerFusion_of_elevenFixedFree`.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1,
HS paragraph, author-preprint p.16, using the degree-twenty Brauer-character
information in its order-eleven inversion argument. The concrete model is
the separate HSG1-f2r20B0 producer. A computation on that model alone does
not prove the universal comparison required here.
-/

@[expose] public section
open scoped TensorProduct
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField
universe u v

private theorem fixed_by_pow {K H W : Type*} [Field K] [Group H]
    [AddCommGroup W] [Module K W] (ρ : Representation K H W)
    {g : H} {w : W} (h : ρ g w = w) (n : ℕ) : ρ (g ^ n) w = w := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, h, ih]

/-- One order-eleven calculation suffices on the literal HS carrier. -/
theorem elevenFixedFree_of_one {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W]
    (ρ : Representation K KnownSimple.SporadicName.hs.Carrier W)
    (x : KnownSimple.SporadicName.hs.Carrier) (hx : orderOf x = 11)
    (hfree : LinearMap.ker (ρ x - 1) = ⊥)
    (g : KnownSimple.SporadicName.hs.Carrier) (hg : orderOf g = 11) :
    LinearMap.ker (ρ g - 1) = ⊥ := by
  let : Finite KnownSimple.SporadicName.hs.Carrier :=
    inferInstanceAs (Finite _root_.Sporadic.LeechRelated.HS.Carrier)
  obtain ⟨k, c, hc⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (by decide : Nat.Prime 11)
    (by change ¬ 11 ^ 2 ∣ Nat.card _root_.Sporadic.LeechRelated.HS.Carrier
        rw [_root_.Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier]
        decide) hg hx
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  have hgw : ρ g w = w := sub_eq_zero.mp hw
  have hcw : ρ c⁻¹ (ρ c w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  have hfix : (ρ x - 1) (ρ c w) = 0 := by
    rw [LinearMap.sub_apply, Module.End.one_apply, hc, map_mul, map_mul]
    change ρ c (ρ (g ^ k) (ρ c⁻¹ (ρ c w))) - ρ c w = 0
    rw [hcw, fixed_by_pow ρ hgw, sub_self]
  have hz := LinearMap.ker_eq_bot'.mp hfree (ρ c w) hfix
  rw [hz, map_zero] at hcw
  exact hcw.symm

private theorem finrank_fixed_extendScalars
    {F E H V : Type*} [Field F] [Field E] [Algebra F E] [Group H]
    [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) (g : H) :
    Module.finrank E (LinearMap.ker (ρ.extendScalars E g - 1)) =
      Module.finrank F (LinearMap.ker (ρ g - 1)) := by
  have h := LinearMap.FixedSpaceTransport.finrank_ker_baseChange
    (E := E) (ρ g - 1)
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_one] at h
  exact h

private theorem fixedFree_of_injective_intertwiner
    {F H V W : Type*} [Field F] [Group H]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F H V} {σ : Representation F H W}
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (g : H) (hfree : LinearMap.ker (σ g - 1) = ⊥) :
    LinearMap.ker (ρ g - 1) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  have hw' : ρ g w = w := sub_eq_zero.mp hw
  have hf' : σ g (f w) = f w := by
    have he : f (ρ g w) = σ g (f w) :=
      LinearMap.congr_fun (f.isIntertwining' g) w
    exact he.symm.trans (congrArg f hw')
  have hz : f w = 0 := LinearMap.ker_eq_bot'.mp hfree (f w) (sub_eq_zero.mpr hf')
  exact hf (hz.trans (map_zero f).symm)

/-- The remaining universal comparison asks for an actual nonzero module map
only after extending both representations to an algebraic closure. -/
def DegreeTwentyModelComparison {V : Type u} [AddCommGroup V]
    [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) KnownSimple.SporadicName.hs.Carrier V) : Prop :=
  IsSimpleGroup KnownSimple.SporadicName.hs.Carrier →
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K KnownSimple.SporadicName.hs.Carrier W),
    Function.Injective τ → τ.IsAbsolutelyIrreducible → Module.finrank K W = 20 →
      letI : Algebra (ZMod 2) (AlgebraicClosure K) :=
        (ZMod.castHom (dvd_refl 2) (AlgebraicClosure K)).toAlgebra
      ∃ f : (τ.extendScalars (AlgebraicClosure K)).IntertwiningMap
        (σ.extendScalars (AlgebraicClosure K)), f ≠ 0

/-- An actual comparison after algebraic closure transports the binary model's
fixed-space calculation to the exact universal characteristic-two contract. -/
theorem degreeTwentyElevenFixedFree_of_modelComparison
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) KnownSimple.SporadicName.hs.Carrier V)
    (hmodel : ∀ g, orderOf g = 11 → LinearMap.ker (σ g - 1) = ⊥)
    (hcompare : DegreeTwentyModelComparison.{u,v} σ) :
    DegreeTwentyElevenFixedFree.{v} := by
  intro hs K _ _ _ W _ _ _ τ hf hi hd g hg
  let : Algebra (ZMod 2) (AlgebraicClosure K) :=
    (ZMod.castHom (dvd_refl 2) (AlgebraicClosure K)).toAlgebra
  obtain ⟨f, hfn⟩ := hcompare hs K W τ hf hi hd
  let : τ.IsAbsolutelyIrreducible := hi
  let : (τ.extendScalars (AlgebraicClosure K)).IsIrreducible :=
    Representation.IsAbsolutelyIrreducible.irreducible_of_extension τ (AlgebraicClosure K)
  have hfi : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hfn
  have hmodelE : LinearMap.ker (σ.extendScalars (AlgebraicClosure K) g - 1) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rw [finrank_fixed_extendScalars, hmodel g hg, finrank_bot]
  have hτE := fixedFree_of_injective_intertwiner f hfi g hmodelE
  apply Submodule.finrank_eq_zero.mp
  rw [← finrank_fixed_extendScalars (E := AlgebraicClosure K) τ g, hτE, finrank_bot]

/-- The model producer need only check one actual order-eleven element; Sylow
conjugacy and scalar transport then supply the full conditional contract. -/
theorem degreeTwentyElevenFixedFree_of_modelComparison_at_one
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) KnownSimple.SporadicName.hs.Carrier V)
    (x : KnownSimple.SporadicName.hs.Carrier) (hx : orderOf x = 11)
    (hmodel : LinearMap.ker (σ x - 1) = ⊥)
    (hcompare : DegreeTwentyModelComparison.{u,v} σ) :
    DegreeTwentyElevenFixedFree.{v} :=
  degreeTwentyElevenFixedFree_of_modelComparison σ
    (elevenFixedFree_of_one σ x hx hmodel) hcompare

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField
