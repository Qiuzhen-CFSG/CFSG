module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct
public import Theory.GroupTheory.SpecificGroups.PermThreeProduct

/-!
# The two-S₃ factor orbit in the contained-offender route

The actual conjugate span J* is normal in H*. Conjugation by H* therefore
sends a normal S₃ factor of J* to another normal S₃ subgroup of J*. The
compatible internal-product equivalence and the classification of normal
S₃ subgroups of S₃ × S₃ show that this is one of the original two factors.
Thus each factor, including the one selected by the actor's projection,
has at most two H*-conjugates.

The final adapter discharges the orbit premise of `of_rank_and_orbit`.
The moved-plane rank remains a separate premise of `of_rank`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),
printed p.105, and proof of 15.3.49(i), printed pp.1143–1144.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct
open ComponentReduction FactorGeneration ClassificationCases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace Product
variable {D : Type*} [Group D] {A B : Subgroup D} (p : InternalProduct A B)
    (eA : A ≃* Equiv.Perm (Fin 3)) (eB : B ≃* Equiv.Perm (Fin 3))

private noncomputable def model : D ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
  p.equiv.symm.trans (eA.prodCongr eB)

private theorem map_model_first : A.map (model p eA eB).toMonoidHom =
    (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    change True ∧ eB (p.equiv.symm a).2 = 1
    rw [inverse_first p ⟨a, ha⟩]
    exact ⟨trivial, eB.map_one⟩
  · intro hx
    refine ⟨(eA.symm x.1 : A), (eA.symm x.1).property, ?_⟩
    change (eA (p.equiv.symm (eA.symm x.1 : A)).1,
      eB (p.equiv.symm (eA.symm x.1 : A)).2) = x
    rw [inverse_first]
    exact Prod.ext (eA.apply_symm_apply x.1) ((map_one eB).trans hx.2.symm)

private theorem map_model_second : B.map (model p eA eB).toMonoidHom =
    (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤ := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    change eA (p.equiv.symm b).1 = 1 ∧ True
    rw [inverse_second p ⟨b, hb⟩]
    exact ⟨eA.map_one, trivial⟩
  · intro hx
    refine ⟨(eB.symm x.2 : B), (eB.symm x.2).property, ?_⟩
    change (eA (p.equiv.symm (eB.symm x.2 : B)).1,
      eB (p.equiv.symm (eB.symm x.2 : B)).2) = x
    rw [inverse_second]
    exact Prod.ext ((map_one eA).trans hx.1.symm) (eB.apply_symm_apply x.2)

include p eA eB in
/-- The coordinate classification respects the original factor inclusions. -/
theorem normal_eq_factor (N : Subgroup D) [N.Normal]
    (eN : N ≃* Equiv.Perm (Fin 3)) : N = A ∨ N = B := by
  let e := model p eA eB
  let : (N.map e.toMonoidHom).Normal :=
    (inferInstance : N.Normal).map _ e.surjective
  let eN' : N.map e.toMonoidHom ≃* Equiv.Perm (Fin 3) :=
    (N.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eN
  rcases Theory.GroupTheory.PermThreeProduct.normal_subgroup_eq_factor _ eN' with h | h
  · exact Or.inl (map_injective e.injective (h.trans (map_model_first p eA eB).symm))
  · exact Or.inr (map_injective e.injective (h.trans (map_model_second p eA eB).symm))

end Product

universe u
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y V Y0 T ZS Z E)
    (c : TwoFactorCase (starAction d))
    (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))

include e₁ e₂ in
/-- Either source S₃ factor has at most two conjugates in H*. -/
theorem factor_orbit_le_two
    (F : Subgroup (starImage H (localSpan d.selected.carrier H)))
    (hF : F = c.first ∨ F = c.second) :
    (Set.range fun h : H ⧸ pCore 2 H =>
      (F.map (starImage H (localSpan d.selected.carrier H)).subtype).map
        (MulAut.conj h).toMonoidHom).ncard ≤ 2 := by
  let J := starImage H (localSpan d.selected.carrier H)
  let : J.Normal :=
    (localSpan_normal d.selected.carrier H d.selected.le_local).map _
      (QuotientGroup.mk'_surjective _)
  have hnormal : F.Normal := by
    rcases hF with rfl | rfl
    · exact Product.first_normal c.product
    · exact Product.first_normal (Product.swap c.product)
  obtain ⟨eF⟩ : Nonempty (F ≃* Equiv.Perm (Fin 3)) := by
    rcases hF with rfl | rfl
    · exact ⟨e₁⟩
    · exact ⟨e₂⟩
  have horbit (h : H ⧸ pCore 2 H) :
      (F.map J.subtype).map (MulAut.conj h).toMonoidHom = c.first.map J.subtype ∨
      (F.map J.subtype).map (MulAut.conj h).toMonoidHom = c.second.map J.subtype := by
    let α : MulAut J := MulAut.conjNormal h
    let : (F.map α.toMonoidHom).Normal := hnormal.map _ α.surjective
    have hm := Product.normal_eq_factor c.product e₁ e₂ (F.map α.toMonoidHom)
      ((F.equivMapOfInjective α.toMonoidHom α.injective).symm.trans eF)
    have he : (F.map J.subtype).map (MulAut.conj h).toMonoidHom =
        (F.map α.toMonoidHom).map J.subtype := by
      rw [map_map, map_map]
      rfl
    rw [he]
    exact hm.imp (congrArg (map J.subtype)) (congrArg (map J.subtype))
  have hs : (Set.range fun h : H ⧸ pCore 2 H =>
      (F.map J.subtype).map (MulAut.conj h).toMonoidHom) ⊆
      {c.first.map J.subtype, c.second.map J.subtype} := by
    rintro _ ⟨h, rfl⟩
    exact horbit h
  calc
    _ ≤ ({c.first.map J.subtype, c.second.map J.subtype} : Set (Subgroup (H ⧸ pCore 2 H))).ncard :=
      Set.ncard_le_ncard hs
    _ ≤ 2 := by
      simpa only [Set.ncard_singleton] using
        Set.ncard_insert_le (c.first.map J.subtype) {c.second.map J.subtype}

include e₁ e₂ in
/-- The chosen factor satisfies the orbit premise of the saturated lift. -/
theorem imageFactor_orbit_le_two :
    (Set.range fun h : H ⧸ pCore 2 H =>
      (imageFactor d c).map (MulAut.conj h).toMonoidHom).ncard ≤ 2 :=
  factor_orbit_le_two d c e₁ e₂ (factor d c) (factor_eq d c)

/-- Assemble the chosen S₃ candidate once its moved-plane rank is supplied. -/
noncomputable def of_rank
    (hrank : ∀ F : Subgroup (starImage H (localSpan d.selected.carrier H)),
      F = c.first ∨ F = c.second → Module.finrank (ZMod 2)
        (Representation.Coinvariants.ker ((starAction d).comp F.subtype)) = 2) :
    SolvableStarFactor H ZS Z d.selected.carrier d.action :=
  of_rank_and_orbit d c e₁ e₂ hrank (factor_orbit_le_two d c e₁ e₂)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct
