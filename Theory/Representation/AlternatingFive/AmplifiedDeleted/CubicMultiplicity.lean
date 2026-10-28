module
public import Theory.Alternating.Aut
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.Representation.AlternatingFive.AmplifiedDeleted.Realization
public import Theory.Representation.AlternatingFive.SeparatedActorRank
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# Cubic bounds for an entire deleted A₅ isotypic module

Faithful conjugation on a normal self-centralizing A₅ gives a compatible
five-point permutation action. For each elementary binary actor, its
projected rank costs at least the same rank times the number of deleted
copies. The amplified bounds permit mixing among these copies. The cubic
ratio of the whole action therefore bounds their multiplicity.

Source application: Aschbacher--Smith 5.1.14(4), 5.1.19 and D.3.21,
refs/quasithin.pdf, printed pp.638,643--644,204--207. The Chapter 12 whole-layer
consumer proves self-centralization for its literal centralizer quotient.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Representation.AlternatingFive
variable {Q W : Type*} [Group Q]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Faithful conjugation on the normal A₅ gives a compatible five-point actor. -/
theorem exists_symmetric_actor_of_centralizer_eq_bot
    (τ : Representation (ZMod 2) Q W) (K : Subgroup Q) [K.Normal]
    (e : K ≃* alternatingGroup (Fin 5)) (hC : centralizer (K : Set Q) = ⊥) :
    ∃ p : Q →* Equiv.Perm (Fin 5), Function.Injective p ∧
      ∀ q g v, τ q (τ (e.symm g).val v) =
        τ (e.symm (MulAut.conjNormal (p q) g)).val (τ q v) := by
  let b := MulEquiv.ofBijective
    (MulAut.conjNormal : Equiv.Perm (Fin 5) →* MulAut (alternatingGroup (Fin 5)))
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
  let α : Q →* MulAut (alternatingGroup (Fin 5)) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : Q →* MulAut K)
  let p := b.symm.toMonoidHom.comp α
  have hp : Function.Injective p := b.symm.injective.comp
    ((MulAut.congr e).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot K hC))
  refine ⟨p,hp,?_⟩
  intro q g v
  have hα : MulAut.conjNormal (p q) = α q := b.apply_symm_apply _
  have he : (e.symm (MulAut.conjNormal (p q) g) : Q) =
      q * (e.symm g : Q) * q⁻¹ := by
    rw [hα]
    change (e.symm (e ((MulAut.conjNormal q) (e.symm g))) : Q) = _
    rw [e.symm_apply_apply]
    rfl
  rw [he]
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
end Representation.AlternatingFive
set_option backward.isDefEq.respectTransparency false

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace Representation.AlternatingFive
open Theory.SpecificGroups.SymmetricFive.ProjectedElementaryRank
variable {Q W : Type*} [Group Q] [Finite Q]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- The same projected elementary actor pays for every deleted summand. -/
theorem deleted_multiplicity_le_two_of_faithful_symmetric_action
    (τ : Representation (ZMod 2) Q W)
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (p : Q →* Equiv.Perm (Fin 5)) (hp : Function.Injective p)
    {k : ℕ} (c : AmplifiedDeleted.Coordinates (ι := Fin k) ρ)
    (hcov : ∀ a g v, τ a (ρ g v) = ρ (MulAut.conjNormal (p a) g) (τ a v))
    (hq : cubicRatio τ ≤ 2) : k ≤ 2 := by
  obtain ⟨A,hA,_,hsmall⟩ := (cubicRatio_le_nat_iff τ 2).mp hq
  let : IsElementaryAbelian 2 A := hA.2
  let f := p.comp A.subtype
  let σ := τ.comp A.subtype
  have hf : Function.Injective f := hp.comp Subtype.val_injective
  have he : primeRank 2 f.range = primeRank 2 A :=
    (primeRank_equiv 2 (MonoidHom.ofInjective hf)).symm
  have hbound := SeparatedActorRank.projected_rank_mul_le_fixedCodim σ f k
    (fun a ha => by
      have horder : f a * f a = 1 := by
        rw [← map_mul, ← pow_two, (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) a), map_one]
      simpa only [σ, MonoidHom.comp_apply, Subgroup.coe_subtype, Fintype.card_fin] using
        c.nontrivial_bound (τ a.val) (f a) horder ha (hcov a.val))
    (fun a ha heven => by
      have horder : f a * f a = 1 := by
        rw [← map_mul, ← pow_two, (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 A) a), map_one]
      simpa only [σ, MonoidHom.comp_apply, Subgroup.coe_subtype, Fintype.card_fin] using
        c.inner_bound (τ a.val) (f a) horder ha heven (hcov a.val))
  rw [he] at hbound
  have hcod : fixedCodim σ ⊤ = fixedCodim τ A := by
    have hh := fixedCodim_map_equivariant σ τ A.subtype (LinearEquiv.refl _ _)
      (fun _ _ => rfl) ⊤
    simpa only [← MonoidHom.range_eq_map,Subgroup.range_subtype] using hh
  rw [hcod] at hbound
  have hr : rank A = primeRank 2 A := IsElementaryAbelian.log_card_eq_primeRank A
  rw [← hr] at hbound
  exact Nat.le_of_mul_le_mul_right (hbound.trans hsmall) hA.rank_pos
end Representation.AlternatingFive
