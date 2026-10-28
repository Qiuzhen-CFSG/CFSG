module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.Rank.Models
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.Orbit
public import Theory.Representation.FixedQuotientCoprime

/-!
# Rank two for the two S₃ factors

The literal module alternatives identify each quotient summand with the
natural binary plane. Their cubic fixed-point-free elements lie in the
normal subgroup A₃ × A₃ of the internal product. The complementary invariant
quotient images therefore have no common fixed vectors for that subgroup.
Its fixed space upstairs is exactly the global fixed space. Coprime averaging
then makes projection injective on both moved spaces, proving their ranks
are two without assuming a splitting upstairs.

The final adapter supplies the rank premise to the already proved orbit
adapter, producing the actual solvable star factor with no extra rank premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),
printed p.105, and proof of 15.3.49(i), printed pp.1143–1144.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.Rank
private theorem cube_mem_alt : ∀ x : Equiv.Perm (Fin 3), x ^ 3 = 1 →
    x ∈ alternatingGroup (Fin 3) := by
  change ∀ x : Equiv.Perm (Fin 3), x ^ 3 = 1 → Equiv.Perm.sign x = 1
  decide +kernel

private theorem normal_nine {D : Type*} [Group D]
    (e : D ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :
    ∃ N : Subgroup D, N.Normal ∧ Nat.card N = 9 ∧ ∀ x : D, x ^ 3 = 1 → x ∈ N := by
  let K := (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))
  let N := K.comap e.toMonoidHom
  have hmap : N.map e.toMonoidHom = K :=
    map_comap_eq_self_of_surjective e.surjective K
  have hc : Nat.card N = 9 := by
    rw [Nat.card_congr (N.equivMapOfInjective e.toMonoidHom e.injective).toEquiv, hmap,
      Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod,
      Nat.card_eq_fintype_card]
    decide
  refine ⟨N, inferInstance, hc, ?_⟩
  intro x hx
  have he : e x ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  exact ⟨cube_mem_alt (e x).1 (congrArg Prod.fst he),
    cube_mem_alt (e x).2 (congrArg Prod.snd he)⟩

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

private theorem split_fixed_left {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (U X : Subrepresentation σ)
    (hd : Disjoint U.toSubmodule X.toSubmodule)
    {u x : W} (hu : u ∈ U) (hx : x ∈ X) (g : D)
    (hf : σ g (u + x) = u + x) : σ g u = u := by
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp hd _ (U.toSubmodule.sub_mem (U.apply_mem_toSubmodule g hu) hu)
  have he : σ g u - u = x - σ g x := by
    apply eq_sub_iff_add_eq.mpr
    calc
      (σ g u - u) + σ g x = σ g (u + x) - u := by rw [map_add]; abel
      _ = x := by rw [hf]; abel
  rw [he]
  exact X.toSubmodule.sub_mem hx (X.apply_mem_toSubmodule g hx)

private theorem images_fixed_le (U X : Subrepresentation ρ)
    (hs : IsCompl ((fixed ρ).quotientImage U).toSubmodule
      ((fixed ρ).quotientImage X).toSubmodule)
    (N : Subgroup D) (r s : N)
    (hr : ∀ v : ((fixed ρ).quotientImage U).toSubmodule,
      ((fixed ρ).quotientImage U).toRepresentation (r : D) v = v → v = 0)
    (hx : ∀ v : ((fixed ρ).quotientImage X).toSubmodule,
      ((fixed ρ).quotientImage X).toRepresentation (s : D) v = v → v = 0) :
    invariants (ρ.comp N.subtype) ≤ ρ.invariants := by
  intro v hv
  let q := (fixed ρ).toSubmodule.mkQ
  have hm : q v ∈ ((fixed ρ).quotientImage U).toSubmodule ⊔
      ((fixed ρ).quotientImage X).toSubmodule := by rw [hs.sup_eq_top]; trivial
  obtain ⟨u, hu, x, hxmem, he⟩ := Submodule.mem_sup.mp hm
  have hf (g : N) : (reducedAction ρ) (g : D) (u + x) = u + x := by
    rw [he]
    change q (ρ g v) = q v
    rw [show ρ g v = v from hv g]
  have hu0 : u = 0 := by
    have hh := split_fixed_left (reducedAction ρ) _ _ hs.disjoint hu hxmem (r : D) (hf r)
    exact congrArg Subtype.val (hr ⟨u, hu⟩ (Subtype.ext hh))
  have hx0 : x = 0 := by
    have hh := split_fixed_left (reducedAction ρ) _ _ hs.disjoint.symm hxmem hu (s : D)
      (by simpa only [add_comm] using hf s)
    exact congrArg Subtype.val (hx ⟨x, hxmem⟩ (Subtype.ext hh))
  change v ∈ (fixed ρ).toSubmodule
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change q v = 0
  rw [← he, hu0, hx0, add_zero]


private theorem moved_eq_coinvariants (A : Subgroup D) :
    moved ρ A = Coinvariants.ker (ρ.comp A.subtype) := by
  unfold moved subspaceCommutator Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨g, hg, w, _, rfl⟩
    exact ⟨(⟨g, hg⟩, w), rfl⟩
  · rintro ⟨⟨g, w⟩, rfl⟩
    exact ⟨g, g.property, w, Submodule.mem_top, rfl⟩

/-- Each original S₃ factor moves a plane in the original module. -/
theorem twoFactor_rank (c : TwoFactorCase ρ)
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))
    (F : Subgroup D) (hF : F = c.first ∨ F = c.second) :
    Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp F.subtype)) = 2 := by
  obtain ⟨hm₁, hd₁, r, hr, hrf⟩ := factor_quotient_plane ρ c.firstCase e₁
  obtain ⟨hm₂, hd₂, s, hs, hsf⟩ := factor_quotient_plane ρ c.secondCase e₂
  let e := c.product.equiv.symm.trans (e₁.prodCongr e₂)
  let : Finite D := Finite.of_equiv _ e.toEquiv.symm
  obtain ⟨N, hN, hcard, hcube⟩ := normal_nine e
  let : N.Normal := hN
  let : Fintype N := Fintype.ofFinite N
  have hrN : (r : D) ∈ N := hcube r (by exact congrArg Subtype.val hr)
  have hsN : (s : D) ∈ N := hcube s (by exact congrArg Subtype.val hs)
  have hf : invariants (ρ.comp N.subtype) ≤ ρ.invariants :=
    images_fixed_le ρ c.firstSpace c.secondSpace c.decomposition N
      ⟨r, hrN⟩ ⟨s, hsN⟩ hrf hsf
  have hc : (Fintype.card N : ZMod 2) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    decide
  have heq := finrank_moved_eq_quotient_image_of_normal_coprime ρ N hc hf F
  rw [heq]
  rcases hF with rfl | rfl
  · rw [← moved_eq_coinvariants, ← hm₁]
    exact hd₁
  · rw [← moved_eq_coinvariants, ← hm₂]
    exact hd₂

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.Rank

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct
open ComponentReduction FactorGeneration ClassificationCases

universe u
variable {G : Type u} [Group G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y V Y0 T ZS Z E)
    (c : TwoFactorCase (starAction d))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))

include e₁ e₂ in
/-- The rank adapter for the actual contained-offender action and either source factor. -/
theorem factor_rank
    (F : Subgroup (starImage H (localSpan d.selected.carrier H)))
    (hF : F = c.first ∨ F = c.second) :
    Module.finrank (ZMod 2) (Coinvariants.ker ((starAction d).comp F.subtype)) = 2 :=
  Rank.twoFactor_rank (starAction d) c e₁ e₂ F hF

variable [Finite G]

/-- The complete solvable-factor construction for the two-S₃ alternative.
Both the moved rank and the ambient conjugacy-orbit bound are discharged. -/
noncomputable def of_two_symmetricThree :
    SolvableStarFactor H ZS Z d.selected.carrier d.action :=
  of_rank d c e₁ e₂ (factor_rank d c e₁ e₂)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct
