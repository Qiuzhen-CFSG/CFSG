module
public import Theory.SpecificGroups.G2Even.TwoRank.NearMaximum
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.Representation.FiniteSchurIntertwiner

/-!
# Coefficient linearity of large elementary G₂ actors

A faithful irreducible normal G₂ component makes elementary conjugation
injective. An actor of rank at least 3n-1 cannot have a nontrivial field
projection, by the strict bound over the half-degree fixed field. Its action
is inner, and the finite Schur commutant makes it linear over every commuting
coefficient field. All maps refer to the original normal subgroup and actor.

Source: Aschbacher–Smith G.9.3(10), G.11.7, printed pp.354,367–368.
-/

@[expose] public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace Representation.G2LargeActors
variable {D V K : Type*} [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field K] [Finite K] [CharP K 2]

/-- A faithful elementary actor of rank at least 3n-1 on an irreducible normal
G₂ component preserves every coefficient field commuting with that component. -/
theorem coefficient_linear
    [Module K V] [SMulCommClass K (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (H A : Subgroup D) [H.Normal]
    [IsIrreducible (ρ.comp H.subtype)] (hf : Function.Injective ρ)
    [IsElementaryAbelian 2 A] (e : H ≃* Atlas.G2.Model K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hcard : 2 ^ (3*n-1) ≤ Nat.card A)
    (hH : ∀ (h : H) (c : K) (v : V), ρ h (c • v) = c • ρ h v) :
    ∀ (a : A) (c : K) (v : V), ρ a (c • v) = c • ρ a v := by
  classical
  have hAH : A ≤ normalizer (H : Set D) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  let f := H.normalizerMonoidHom.comp (Subgroup.inclusion hAH)
  have hf' : Function.Injective f :=
    BinaryIrreducibleCentralizer.elementary_conjugation_injective ρ H hf A hAH
  have hq : 2 < Nat.card K := by
    rw [hK]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  let j := MulEquiv.ofBijective (Atlas.G2.LieAutomorphismExtensions.semilinearAction (F := K))
    ⟨Atlas.G2.LieAutomorphismExtensions.semilinearAction_injective hq,
      Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective hq⟩
  let π := j.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp f)
  have hπi : Function.Injective π := j.symm.injective.comp ((MulAut.congr e).injective.comp hf')
  have hπ (a : A) : Atlas.G2.LieAutomorphismExtensions.semilinearAction (π a) =
      MulAut.congr e (f a) := j.apply_symm_apply _
  have hfield (a : A) : (π a).right = 1 := by
    by_contra hne
    have he : IsElementaryAbelian 2 π.range :=
      IsElementaryAbelian.of_surjective π.rangeRestrict π.rangeRestrict_surjective
    have hb := Atlas.G2.EvenTwoRank.outer_elementary_card_lt_near_maximum K hn hK
      π.range he ⟨π a, ⟨a,rfl⟩⟩ hne
    rw [← Nat.card_congr (MonoidHom.ofInjective hπi).toEquiv] at hb
    exact not_lt_of_ge hcard hb
  intro a c v
  let h : H := e.symm (π a).left
  have he : f a = MulAut.conj h := by
    apply (MulAut.congr e).injective
    rw [←hπ]
    apply MulEquiv.ext
    intro y
    change (π a).left * Atlas.G2.LieAutomorphismExtensions.fieldAction (π a).right y *
        (π a).left⁻¹ = e (h * e.symm y * h⁻¹)
    rw [hfield, map_one, MulAut.one_apply]
    simp only [map_mul,map_inv,h,e.apply_symm_apply]
  have hc : (h : D)⁻¹ * (a : D) ∈ centralizer (H : Set D) := by
    intro k hk
    have hh := congrArg (fun b : MulAut H => (b ⟨k,hk⟩ : D)) he
    change (a:D)*k*(a:D)⁻¹ = (h:D)*k*(h:D)⁻¹ at hh
    have heq : (h:D)⁻¹*(a:D)*k*((h:D)⁻¹*(a:D))⁻¹ = k := by
      calc
        _ = (h:D)⁻¹*((a:D)*k*(a:D)⁻¹)*(h:D) := by group
        _ = k := by rw [hh]; group
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  have hlin := FiniteSchurIntertwiner.map_smul (ρ.comp H.subtype) hH
    (ρ ((h:D)⁻¹*(a:D))) (fun k w => by
      have heq := congrArg (fun z : D => ρ z w) (hc k k.property)
      simpa only [map_mul,Module.End.mul_apply,MonoidHom.comp_apply,Subgroup.coe_subtype] using heq.symm) c v
  have heq := congrArg (ρ (h:D)) hlin
  rw [hH h] at heq
  simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel_left] using heq
end Representation.G2LargeActors

