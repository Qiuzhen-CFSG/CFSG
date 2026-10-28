module
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison.Inputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.BorelComparison.RootGeometry
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.Geometry
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Lifting root intertwiners to the SU₃(5) Borel

The space of root intertwiners is the root-fixed subspace of the linear-map
representation. The literal torus normalizes the root, so it acts on this
subspace. Its eighth powers act trivially when both original representations
kill the SU center. The finite image of this action is therefore a two-group,
which has a nonzero fixed vector in characteristic two. This vector is an
intertwiner for the root and torus, hence for their literal join, the Borel.

This proves the lifting input for the degree-twenty Borel comparison without
any dimension, irreducibility, or root-center assumption. The fixed map need
not be the initially supplied root intertwiner.

Source motivation: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Huppert II.10.12; Aschbacher–Smith K.2, p.453.
The precise local lifting contract is defined in `BorelComparison.Inputs`.
-/

public section

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison

/-- Restrict to the root-fixed space and apply the fixed-vector theorem to
the finite image of the torus action. -/
private theorem fixed_vector_on_join
    {K G V : Type*} [Field K] [CharP K 2] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (τ : Representation K G V) (A T : Subgroup G) [Finite T]
    (hT : T ≤ Subgroup.normalizer (A : Set G))
    (hpow : ∀ t : T, τ t ^ 8 = 1)
    (hne : ∃ v : invariants (τ.comp A.subtype), v ≠ 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ g ∈ A ⊔ T, τ g v = v := by
  let L := invariants (τ.comp A.subtype)
  have hstable (t : T) : L ≤ L.comap (τ t) := by
    intro v hv a
    have ha : (t : G)⁻¹ * a * t ∈ A := by
      simpa only [Subgroup.coe_inv, inv_inv] using
        (Subgroup.mem_normalizer_iff.mp (hT (t⁻¹).property) (a : G)).mp a.property
    have hv' := hv ⟨(t : G)⁻¹ * a * t, ha⟩
    change τ ((t : G)⁻¹ * a * t) v = v at hv'
    change τ (a : G) (τ t v) = τ t v
    have h := congrArg (τ (t : G)) hv'
    simpa only [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul] using h
  let α := Representation.subrepresentation (τ.comp T.subtype) L hstable
  have hα (t : T) : α t ^ 8 = 1 := by
    rw [← map_pow]
    ext v
    change τ ((t ^ 8 : T) : G) (v : V) = (v : V)
    simp only [Subgroup.coe_pow, map_pow, hpow t, Module.End.one_apply]
  let H := α.asGroupHom.range
  let : Finite H := Finite.of_surjective α.asGroupHom.rangeRestrict
    α.asGroupHom.rangeRestrict_surjective
  have hH : IsPGroup 2 H := by
    rintro ⟨g, t, rfl⟩
    refine ⟨3, ?_⟩
    apply Subtype.ext
    apply Units.ext
    change α t ^ 8 = 1
    exact hα t
  let β : Representation K H L := (Units.coeHom _).comp H.subtype
  obtain ⟨v, hv⟩ := hne
  let : Nontrivial L := ⟨⟨v, 0, hv⟩⟩
  have hchar : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨w, hw, hfix⟩ := pGroup_fix_nonzero_vector
    (by omega : ringChar K ≠ 0) (by rwa [hchar]) β
  refine ⟨w, fun hz => hw (Subtype.ext hz), ?_⟩
  let S : Subgroup G :=
    { carrier := {g | τ g (w : V) = (w : V)}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change τ (a * b) (w : V) = (w : V)
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro g hg
        have hh := congrArg (τ g⁻¹) hg
        simpa using hh.symm }
  have hAS : A ≤ S := by
    intro a ha
    exact w.property ⟨a, ha⟩
  have hTS : T ≤ S := by
    intro t ht
    have hh := hfix (α.asGroupHom.rangeRestrict ⟨t, ht⟩)
    exact congrArg Subtype.val hh
  exact fun g hg => (sup_le hAS hTS) hg

open BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus HermitianForm.OddPrimeSylow.NormalizedOuter
open Degrees Degrees.RootEigenline
universe v

/-- Root intertwiners contain a nonzero torus-fixed vector when the SU center
acts trivially. This gives an intertwiner on the literal Borel. -/
theorem borel_intertwiner_lifting : BorelIntertwinerLifting.{v} := by
  intro F _ _ J hc hconj K _ _ _ U W _ _ _ _ _ _ ρ σ hρ hσ hf
  let τ := linHom ρ σ
  let T := specialTorus (FormTransport.standardForm J) rfl
  have hpow (t : T) : τ t ^ 8 = 1 := by
    obtain ⟨k, hk⟩ := t.property
    have ht : (t : standardGroup J) = (principalTorusIn J k : standardGroup J) := hk.symm
    have hz := torus_pow_eight_mem_center J hc hconj k
    have hρ' := hρ hz
    have hσ' := hσ hz
    rw [← map_pow, ht]
    ext f u
    change σ ((principalTorusIn J k : standardGroup J) ^ 8)
      (f (ρ (((principalTorusIn J k : standardGroup J) ^ 8)⁻¹) u)) = f u
    rw [MonoidHom.mem_ker.mp hσ', MonoidHom.mem_ker.mp (ρ.ker.inv_mem hρ')]
    rfl
  obtain ⟨f, hf⟩ := hf
  let e := invariantsEquivIntertwiningMap
    (ρ.comp (standardRoot J).subtype) (σ.comp (standardRoot J).subtype)
  have hne : ∃ f : invariants (τ.comp (standardRoot J).subtype), f ≠ 0 := by
    refine ⟨e.symm f, ?_⟩
    exact fun h => hf (e.symm.injective (h.trans (map_zero e.symm).symm))
  obtain ⟨f, hf, hfix⟩ := fixed_vector_on_join τ (standardRoot J) T
    (specialTorus_normalizes_root (FormTransport.standardForm J) rfl) hpow hne
  let eB := invariantsEquivIntertwiningMap
    (ρ.comp (standardBorel J).subtype) (σ.comp (standardBorel J).subtype)
  have hfB : f ∈ invariants (linHom (ρ.comp (standardBorel J).subtype)
      (σ.comp (standardBorel J).subtype)) := fun b => hfix b b.property
  refine ⟨eB ⟨f, hfB⟩, ?_⟩
  intro hz
  have hh := eB.injective (hz.trans (map_zero eB).symm)
  exact hf (congrArg Subtype.val hh)

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.BorelComparison
