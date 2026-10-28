module
public import Theory.Representation.BinaryPermutation.FiveCentralExtension.OuterCompatibility
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.CoverAction
public import Theory.Representation.BinaryPermutation.FiveLowRank
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.CommonFixedSpaceTransport

/-!
# Rank-one actors on the marked natural A₅ module

The five-point normalizer realizes every ambient actor as a permutation.
An actor of displacement rank one is a transposition. Sign then shows that
a subgroup consisting of trivial or rank-one actors has at most two actions.
The same natural coordinates transport the trivial A₅ commutant to any
marked copy, allowing intertwiners to extend to normalizing actors.

Source: Aschbacher–Smith, G.11.9(2), printed p.369, applied to the
natural A₅ row; the concrete permutation calculation is FiveLowRank.
-/

public noncomputable section
open Representation
namespace Representation.FivePointActors
open Subgroup Module BinaryPermutation
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem natural_commuting_eq_refl
    (ρ : Representation (ZMod 2) G V) (e : G ≃* alternatingGroup (Fin 5))
    (E : V ≃ₗ[ZMod 2] natural (Fin 5))
    (hE : ∀ g u, E (ρ g u) = alternatingNaturalRepresentation (Fin 5) (e g) (E u))
    (f : V ≃ₗ[ZMod 2] V) (hf : ∀ g u, f (ρ g u) = ρ g (f u)) :
    f = LinearEquiv.refl _ _ := by
  let c := coreEquivNatural (Fin 5) (by decide)
  let D := E.trans c.symm
  have hD (g : G) (u : V) :
      D (ρ g u) = coreRepresentation (Fin 5) (e g).val (D u) := by
    apply c.injective
    change c (c.symm (E (ρ g u))) = _
    rw [c.apply_symm_apply,coreEquivNatural_equivariant]
    change E (ρ g u) = naturalRepresentation (Fin 5) (e g).val (c (c.symm (E u)))
    rw [c.apply_symm_apply]
    exact hE g u
  let t := D.symm.trans (f.trans D)
  have ht := FiveCentralExtension.core_commuting_eq_id t.toLinearMap ?_ t.injective
  · ext u
    apply D.injective
    have hh := ht (D u)
    simpa only [t,LinearEquiv.coe_coe,LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply,LinearEquiv.refl_apply] using hh
  · intro g hg u
    obtain ⟨a,ha⟩ := e.surjective ⟨g,hg⟩
    obtain ⟨w,rfl⟩ := D.surjective u
    have hv : (e a).val = g := congrArg Subtype.val ha
    change D (f (D.symm (coreRepresentation (Fin 5) g (D w)))) = _
    rw [← hv,← hD,D.symm_apply_apply,hf,hD]
    simp only [t,LinearEquiv.coe_coe,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]

variable [FiniteDimensional (ZMod 2) V]
/-- Rank-one actors normalizing a marked natural A₅ module have at most two actions. -/
theorem two_actions_of_rank_one
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G) [H.Normal]
    (e : H ≃* alternatingGroup (Fin 5))
    (E : V ≃ₗ[ZMod 2] natural (Fin 5))
    (hE : ∀ h : H, ∀ u, E (ρ h u) = alternatingNaturalRepresentation (Fin 5) (e h) (E u))
    (hr : ∀ x : X, ρ x ≠ 1 → finrank (ZMod 2) (LinearMap.range (ρ x - 1)) = 1)
    (a : X) (ha : ρ a ≠ 1) :
    ∀ x : X, (∀ u, ρ x u = u) ∨ (∀ u, ρ x u = ρ a u) := by
  obtain ⟨f,hf,hfH⟩ := OrthogonalFourMinus.FivePoint.exists_ambient_permutation_of_cover
    ρ H e.toMonoidHom e.surjective E hE
  have hfid (x : G) : f x = 1 ↔ ρ x = 1 := by
    constructor
    · intro hx
      ext u
      apply E.injective
      rw [hf,hx,map_one,Module.End.one_apply,Module.End.one_apply]
    · intro hx
      apply naturalRepresentation_injective (Fin 5) (by decide)
      ext u
      obtain ⟨v,rfl⟩ := E.surjective u
      rw [← hf,hx,map_one,Module.End.one_apply,Module.End.one_apply]
  have hswap (x : X) (hx : f x ≠ 1) : (f x).IsSwap := by
    let c := coreEquivNatural (Fin 5) (by decide)
    have hc := LinearMap.FixedSpaceTransport.finrank_range_sub_one_equiv c
      (coreRepresentation (Fin 5) (f x)) (naturalRepresentation (Fin 5) (f x))
      (coreEquivNatural_equivariant (Fin 5) (by decide) (f x))
    have hd := LinearMap.FixedSpaceTransport.finrank_range_sub_one_equiv E
      (ρ x) (naturalRepresentation (Fin 5) (f x)) (hf x)
    have hrx := hr x (fun he => hx ((hfid x).mpr he))
    rcases FiveLowRank.low_rank (f x) (hc.trans (hd.symm.trans hrx)).le with h | ⟨i,j,hij,h⟩
    · exact (hx h).elim
    · exact ⟨i,j,hij,h⟩
  have heven (x : X) (hx : (f x).sign = 1) : f x = 1 := by
    by_contra hn
    have hs := (hswap x hn).sign_eq
    rw [hx] at hs
    exact (by decide : (1 : ℤˣ) ≠ -1) hs
  have ha' : f a ≠ 1 := fun he => ha ((hfid a).mp he)
  intro x
  by_cases hx : f x = 1
  · left
    intro u
    rw [(hfid x).mp hx]
    rfl
  · right
    have hax : f (a⁻¹ * x : X) = 1 := by
      apply heven
      change (f ((a : G)⁻¹ * x)).sign = 1
      rw [map_mul,map_inv,map_mul,map_inv,(hswap a ha').sign_eq,(hswap x hx).sign_eq]
      decide
    have hfx : f x = f a := by
      change f ((a : G)⁻¹ * x) = 1 at hax
      rw [map_mul,map_inv] at hax
      exact (inv_mul_eq_one.mp hax).symm
    intro u
    apply E.injective
    rw [hf,hf,hfx]
end Representation.FivePointActors

