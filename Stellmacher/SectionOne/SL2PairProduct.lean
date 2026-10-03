module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# A commuting pair of SL2(2) subgroups gives the full product

Two commuting subgroups isomorphic to SL2(2), whose join is the whole
ambient finite group of order thirty-six, give an isomorphism of that
group with SL2(2) times SL2(2).

The product of the subgroup inclusions is a group homomorphism because
the two factors commute. Its image is their join, hence it is surjective.
Both factors have order six, so the product and target have the same
cardinality. The homomorphism is therefore bijective; composing its
inverse with the given factor isomorphisms yields the displayed model.

This is the final direct-product assembly for the exceptional case of
Stellmacher (1.6), journal p.18, `refs/latex/stellmacher-n-group.tex`.
The concrete matrix model is written explicitly to avoid a dependency on
the later-section shorthand definitions.
-/

namespace Stellmacher.SectionOne

/-- Two commuting SL2(2) subgroups generating a group of order thirty-six
identify it with their external direct product. -/
public theorem mulEquiv_sl2Two_prod_of_commuting_sup_top
    {G : Type*} [Group G] [Finite G]
    (E₁ E₂ : Subgroup G) (hE₁ : IsSL2Two E₁) (hE₂ : IsSL2Two E₂)
    (hcomm : ⁅E₁, E₂⁆ = ⊥) (hsup : E₁ ⊔ E₂ = ⊤)
    (hGcard : Nat.card G = 36) :
    Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  have hpoint (x : E₁) (y : E₂) : Commute (E₁.subtype x) (E₂.subtype y) :=
    ((Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm x.property)) y y.property).symm
  let f : E₁ × E₂ →* G := E₁.subtype.noncommCoprod E₂.subtype hpoint
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    change (E₁.subtype.noncommCoprod E₂.subtype hpoint).range = ⊤
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype, hsup]
  have hcard : Nat.card (E₁ × E₂) = Nat.card G := by
    rw [Nat.card_prod, RankOneThreeGroupAssembly.isSL2Two_card hE₁,
      RankOneThreeGroupAssembly.isSL2Two_card hE₂, hGcard]
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hcard⟩
  obtain ⟨e₁⟩ := hE₁
  obtain ⟨e₂⟩ := hE₂
  exact ⟨(MulEquiv.ofBijective f hbij).symm.trans (MulEquiv.prodCongr e₁ e₂)⟩

end Stellmacher.SectionOne

