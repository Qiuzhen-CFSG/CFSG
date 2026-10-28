module
public import CFSG.Quasithin.ChapterG.Section06.Source
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.BinaryTwo
public import Theory.Representation.BinaryOffender.ComponentSum
/-!
# Matching the two small transvection factors

The involution interchanging the two G.6.4 factors identifies their acting
groups. Consequently a binary plane factor cannot be paired with a five-letter
factor, whose group has a different order. For two binary planes, cross
centralization puts their intersection in the fixed space of GL₂(2), which is
zero; the full moved space therefore has dimension four.

These retain the actual marked actions needed in the model comparison in
Aschbacher--Smith 10.2.1, printed p.743, following G.6.4, printed p.346.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
 {ρ : Representation (ZMod 2) G V} {a : G}

theorem HasModelOn.conjugate_moved {A B : Subgroup G} (t : G)
    (hAB : A.map (MulAut.conj t).toMonoidHom = B)
    {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) K W}
    (h : HasModelOn ρ A (subspaceCommutator ρ ⊤ A) σ) :
    HasModelOn ρ B (subspaceCommutator ρ ⊤ B) σ := by
  obtain ⟨e, E, hs, he⟩ := h
  let f : A ≃* B := ((MulAut.conj t).subgroupMap A).trans (MulEquiv.subgroupCongr hAB)
  let q : V ≃ₗ[ZMod 2] V :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V (ρ.asGroupHom t)
  have hU : (subspaceCommutator ρ ⊤ A).map q.toLinearMap = subspaceCommutator ρ ⊤ B := by
    change (subspaceCommutator ρ ⊤ A).map (ρ t) = _
    rw [moved_map_conjugate, hAB]
  let R := q.ofSubmodules (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B) hU
  have ht (k : A) (v : subspaceCommutator ρ ⊤ A) :
      ρ (f k) (R v) = q (ρ k v) := by
    change ρ (t * k * t⁻¹) (ρ t v) = ρ t (ρ k v)
    simp only [map_mul, Module.End.mul_apply, ρ.inv_self_apply]
  have hsB (k : B) (v : subspaceCommutator ρ ⊤ B) :
      ρ k v ∈ subspaceCommutator ρ ⊤ B := by
    obtain ⟨k, rfl⟩ := f.surjective k
    obtain ⟨v, rfl⟩ := R.surjective v
    rw [ht]
    exact (R ⟨ρ k v, hs k v⟩).property
  refine ⟨f.symm.trans e, R.symm.trans E, hsB, ?_⟩
  intro k v
  obtain ⟨k, rfl⟩ := f.surjective k
  obtain ⟨v, rfl⟩ := R.surjective v
  simp only [MulEquiv.trans_apply, f.symm_apply_apply,
    LinearEquiv.trans_apply, R.symm_apply_apply]
  rw [← he k v]
  congr 1
  apply R.injective
  rw [R.apply_symm_apply]
  exact Subtype.ext (ht k v)


private theorem binary_plane_fixed_eq_zero (v : Fin 2 → ZMod 2)
    (h : ∀ g : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2), g v = v) : v = 0 := by
  by_contra hv
  obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero
    hv (by decide : (![1, 0] : Fin 2 → ZMod 2) ≠ 0)
  obtain ⟨k, hk⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero
    hv (by decide : (![0, 1] : Fin 2 → ZMod 2) ≠ 0)
  exact (by decide : (![1, 0] : Fin 2 → ZMod 2) ≠ ![0, 1])
    (hg.symm.trans ((h g).trans ((h k).symm.trans hk)))

theorem TwoFactorModules.binary_plane_spaces_disjoint (d : TwoFactorModules ρ a)
    (hm : HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first) (binaryLinearAction 2)) :
    Disjoint (subspaceCommutator ρ ⊤ d.first) (subspaceCommutator ρ ⊤ d.second) := by
  obtain ⟨e, E, hs, he⟩ := hm
  apply disjoint_iff.mpr
  apply bot_unique
  rintro v ⟨h₁, h₂⟩
  have hv : E ⟨v, h₁⟩ = 0 := by
    apply binary_plane_fixed_eq_zero
    intro g
    obtain ⟨k, rfl⟩ := e.surjective g
    have hfix : ρ k v = v := by
      apply sub_eq_zero.mp
      apply d.cross_first.le
      exact Submodule.subset_span ⟨k, k.property, v, h₂, rfl⟩
    have ht := he k ⟨v, h₁⟩
    change E ⟨ρ k v, hs k ⟨v, h₁⟩⟩ = e k (E ⟨v, h₁⟩) at ht
    rw [← ht]
    exact congrArg E (Subtype.ext hfix)
  have hz : (⟨v, h₁⟩ : subspaceCommutator ρ ⊤ d.first) = 0 :=
    E.injective (hv.trans E.map_zero.symm)
  exact congrArg Subtype.val hz

theorem TwoFactorModules.binary_planes_finrank [Module.Finite (ZMod 2) V]
    (d : TwoFactorModules ρ a)
    (h₁ : HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first) (binaryLinearAction 2))
    (h₂ : HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second) (binaryLinearAction 2)) :
    Module.finrank (ZMod 2) V = 4 := by
  have hd := d.binary_plane_spaces_disjoint h₁
  obtain ⟨_, E₁, _⟩ := h₁
  obtain ⟨_, E₂, _⟩ := h₂
  have hh := Submodule.finrank_sup_add_finrank_inf_eq
    (subspaceCommutator ρ ⊤ d.first) (subspaceCommutator ρ ⊤ d.second)
  rw [d.space_sum, hd.eq_bot, finrank_top, finrank_bot, add_zero,
    E₁.finrank_eq, E₂.finrank_eq, Module.finrank_fin_fun] at hh
  exact hh

private theorem linearTwo_not_equiv_symmetricFive
    (e : ((Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2)) ≃* Equiv.Perm (Fin 5)) : False := by
  have hc := Nat.card_congr
    (BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree.symm.trans e).toEquiv
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hc

theorem TwoFactors.same_binary_plane_or_five_models (d : TwoFactors ρ a)
    (h₁ : HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first) (binaryLinearAction 2) ∨
      HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first)
        (BinaryPermutation.naturalRepresentation (Fin 5)))
    (h₂ : HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second) (binaryLinearAction 2) ∨
      HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second)
        (BinaryPermutation.naturalRepresentation (Fin 5))) :
    (HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first) (binaryLinearAction 2) ∧
      HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second) (binaryLinearAction 2)) ∨
    (HasModelOn ρ d.first (subspaceCommutator ρ ⊤ d.first)
        (BinaryPermutation.naturalRepresentation (Fin 5)) ∧
      HasModelOn ρ d.second (subspaceCommutator ρ ⊤ d.second)
        (BinaryPermutation.naturalRepresentation (Fin 5))) := by
  obtain ⟨t, _, _, _, ht⟩ := d.extension
  let e : d.first ≃* d.second :=
    ((MulAut.conj t).subgroupMap d.first).trans (MulEquiv.subgroupCongr ht)
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl ⟨h₁, h₂⟩
  · obtain ⟨e₁, _⟩ := h₁
    obtain ⟨e₂, _⟩ := h₂
    exact (linearTwo_not_equiv_symmetricFive (e₁.symm.trans (e.trans e₂))).elim
  · obtain ⟨e₁, _⟩ := h₁
    obtain ⟨e₂, _⟩ := h₂
    exact (linearTwo_not_equiv_symmetricFive (e₂.symm.trans (e.symm.trans e₁))).elim
  · exact Or.inr ⟨h₁, h₂⟩
end CFSG.Quasithin.ChapterG.Section06
