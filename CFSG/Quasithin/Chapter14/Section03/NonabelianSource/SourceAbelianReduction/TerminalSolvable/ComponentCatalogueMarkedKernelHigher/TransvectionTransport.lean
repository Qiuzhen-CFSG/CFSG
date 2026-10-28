module
public import Theory.Representation.BinaryPermutation.EightNormalizer
public import Theory.Representation.BinaryPermutation.SymmetricEightTransvections
public import Theory.Representation.CommonFixedSpaceTransport
public import CFSG.Quasithin.ChapterG.Section09.ConstituentAction

/-!
# Transporting rank-one actors between marked natural constituents

The natural A₈ module has trivial invertible commutant. Therefore an
intertwiner of its normal-group action extends to each common normalizing
actor. On the original natural module every nontrivial actor is then a
transposition; its sign distinguishes its action from the identity.

This retains the rank-one orthogonal constituent from G.11.9(2), rather
than trying to exclude A₈ using its fixed line alone.
-/

public noncomputable section
open Subgroup Representation
namespace Representation
variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem marked_equivariant_of_trivial_normal_commutant
    (ρ : Representation K G V) (σ : Representation K G W)
    (H : Subgroup G) [H.Normal] (E : V ≃ₗ[K] W)
    (hE : ∀ (h : H) u, E (ρ h u) = σ h (E u))
    (hC : ∀ F : V ≃ₗ[K] V,
      (∀ (h : H) u, F (ρ h u) = ρ h (F u)) → F = LinearEquiv.refl K V) :
    ∀ g u, E (ρ g u) = σ g (E u) := by
  intro g u
  let A := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  let B := LinearEquiv.ofBijective (σ g⁻¹) (σ.apply_bijective g⁻¹)
  let F := A.trans (E.trans (B.trans E.symm))
  have hF : ∀ (h : H) w, F (ρ h w) = ρ h (F w) := by
    intro h w
    let k : H := ⟨g * h * g⁻¹, (inferInstance : H.Normal).conj_mem h h.property g⟩
    have hρ : ρ g (ρ h w) = ρ k (ρ g w) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 1
      congr 1
      change g * h.val = (g * h.val * g⁻¹) * g
      group
    have hσ (z : W) : σ g⁻¹ (σ k z) = σ h (σ g⁻¹ z) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 1
      congr 1
      change g⁻¹ * (g * h.val * g⁻¹) = h.val * g⁻¹
      group
    change E.symm (σ g⁻¹ (E (ρ g (ρ h w)))) =
      ρ h (E.symm (σ g⁻¹ (E (ρ g w))))
    rw [hρ, hE, hσ]
    apply E.injective
    rw [E.apply_symm_apply, hE, E.apply_symm_apply]
  have he := congrArg (fun f : V ≃ₗ[K] V => f u) (hC F hF)
  change E.symm (σ g⁻¹ (E (ρ g u))) = u at he
  have hh := congrArg (fun w => σ g (E w)) he
  rw [E.apply_symm_apply] at hh
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh
end Representation

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedHigherTransport
open Subgroup Module Representation Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
theorem natural_eight_commuting_eq_refl
    (ρ : Representation (ZMod 2) G V)
    (e : G ≃* alternatingGroup (Fin 8))
    (E : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hE : ∀ g u, E (ρ g u) = BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e g) (E u))
    (f : V ≃ₗ[ZMod 2] V) (hf : ∀ g u, f (ρ g u) = ρ g (f u)) :
    f = LinearEquiv.refl _ _ := by
  let t := E.symm.trans (f.trans E)
  have ht : ∀ g : alternatingGroup (Fin 8), ∀ u,
      t (BinaryPermutation.naturalRepresentation (Fin 8) g.val u) =
        BinaryPermutation.naturalRepresentation (Fin 8) g.val (t u) := by
    intro g u
    obtain ⟨a,rfl⟩ := e.surjective g
    obtain ⟨w,rfl⟩ := E.surjective u
    change E (f (E.symm (BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e a) (E w)))) = _
    rw [← hE,E.symm_apply_apply,hf,hE]
    simp only [t,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
    rfl
  have he := BinaryPermutation.EightCommutant.commuting_eq_refl t ht
  ext u
  apply E.injective
  have hh := congrArg (fun k : BinaryPermutation.natural (Fin 8) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin 8) => k (E u)) he
  simpa only [t,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,LinearEquiv.refl_apply] using hh

omit [FiniteDimensional (ZMod 2) V] in
/-- The displacement rank is unchanged when represented intrinsically on
an invariant subspace instead of in the original ambient space. -/
theorem constituent_displacement_rank
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G)
    (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
    (hX : X ≤ subspaceStabilizer ρ I) (x : X) :
    let σ := ChapterG.Section09.constituentAction ρ H X I hH hX
    let xp : (H ⊔ X : Subgroup G) := ⟨x,(show X ≤ H ⊔ X from le_sup_right) x.property⟩
    finrank (ZMod 2) (LinearMap.range (σ xp - 1)) =
      finrank (ZMod 2) (LinearMap.range ((ρ x - 1).comp I.subtype)) := by
  intro σ xp
  have he := Submodule.finrank_map_subtype_eq I (LinearMap.range (σ xp - 1))
  rw [← LinearMap.range_comp] at he
  have heq : I.subtype.comp (σ xp - 1) = (ρ x - 1).comp I.subtype := by ext u; rfl
  rw [heq] at he
  exact he.symm

/-- If every nontrivial actor on the natural A₈ module has rank one,
then it has the same action as any one fixed nontrivial actor. -/
theorem two_actions_of_natural_eight_rank_one
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G) [H.Normal]
    (e : H ≃* alternatingGroup (Fin 8))
    (E : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hE : ∀ h : H, ∀ u, E (ρ h u) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e h) (E u))
    (hpow : ∀ x : X, x ^ 2 = 1)
    (hr : ∀ x : X, ρ x ≠ 1 → finrank (ZMod 2) (LinearMap.range (ρ x - 1)) = 1)
    (a : X) (ha : ρ a ≠ 1) :
    ∀ x : X, (∀ u, ρ x u = u) ∨ (∀ u, ρ x u = ρ a u) := by
  obtain ⟨f,hfH,hf,hker⟩ := BinaryPermutation.EightNormalizer.exists_ambient_hom
    ρ H e.toMonoidHom e.surjective E hE
  have hfid (x : G) : f x = 1 ↔ ρ x = 1 := by
    change x ∈ f.ker ↔ x ∈ ρ.ker
    rw [hker]
  have hswap (x : X) (hx : f x ≠ 1) : (f x).IsSwap := by
    let τ := BinaryPermutation.naturalRepresentation (Fin 8)
    let φ := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (BinaryPermutation.natural (Fin 8))).toMonoidHom.comp τ.asGroupHom
    have hφ : Function.Injective φ := fun y z he =>
      BinaryPermutation.naturalRepresentation_injective (Fin 8) (by decide)
        (congrArg LinearEquiv.toLinearMap he)
    have hd := (LinearMap.FixedSpaceTransport.finrank_range_sub_one_equiv
      E (ρ x) (τ (f x)) (hf x)).symm.trans (hr x (fun he => hx ((hfid x).mpr he)))
    apply Representation.SymmetricEightTransvections.isSwap_of_transvection φ hφ (f x) hx
    · simpa only [Subgroup.coe_pow,Subgroup.coe_one,map_pow,map_one] using congrArg f
        (congrArg Subtype.val (hpow x))
    · apply Representation.SymmetricEightTransvections.Linear.of_small_displacement
        (φ (f x))
      exact hd.le
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

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedHigherTransport
