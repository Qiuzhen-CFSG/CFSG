module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Duality.Core
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.Orbits.Basic
public import Theory.Representation.Quotient

/-!
# No irreducible six-dimensional binary SL₅ module

The exterior square is irreducible: a nonzero invariant subspace has an
upper-fixed vector, whose only possible nonzero coordinate is the first
wedge. Elementary transvections then generate every wedge basis vector.
Complementary-wedge duality gives the same assertion for the exterior cube.

For an arbitrary irreducible six-dimensional module, zero-Hecke operators
produce a local highest vector. Empty support forces dimension one,
endpoint support gives dimension at most five, and multiple support gives
at least eleven. Middle singleton support produces a nonzero map from an
irreducible ten-dimensional exterior power, contradicting injectivity.

The actual containing-component application is in Chapter12 Section05's
NaturalSource.Local.Components.Six. Source: Aschbacher--Smith, proof of
12.5.3, printed p.819, using the highest-vector geometry behind I.1.6(7).
-/

public section

open scoped BigOperators
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional Classification

private theorem fixed_coordinates (v : V)
    (h : ∀ i : Fin 4, exteriorAction 2 (simpleUpper i) v = v) :
    v = coordinates v 0 • basis 0 := by
  have he (i : Fin 4) (j : Fin 10) := congrArg (fun w => coordinates w j) (h i)
  simp only [coordinates_action] at he
  have h4 := he 0 1
  have h5 := he 0 2
  have h6 := he 0 3
  have h1 := he 1 0
  have h7 := he 1 5
  have h8 := he 1 6
  have h2 := he 2 1
  have h9 := he 2 8
  have h3 := he 3 2
  simp [actionMatrix, simpleUpper, Matrix.SpecialLinearGroup.transvection_coe,
    pair, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply,
    Matrix.single] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  apply coordinates.injective
  rw [map_smul, coordinates_basis]
  ext i
  fin_cases i <;> simp_all

private theorem basis_mem_of_first (W : Subrepresentation (exteriorAction 2))
    (h : basis 0 ∈ W.toSubmodule) : ∀ i, basis i ∈ W.toSubmodule := by
  have step (i j : Fin 5) (k : Fin 10) (hk : basis k ∈ W.toSubmodule) :
      exteriorAction 2 (elementary i j) (basis k) + basis k ∈ W.toSubmodule :=
    W.toSubmodule.add_mem (W.apply_mem_toSubmodule _ hk) hk
  have action (i j : Fin 5) (k l : Fin 10)
      (he : (actionMatrix (elementary i j)).mulVec (Pi.single k 1) + Pi.single k 1 =
        (Pi.single l 1 : Coordinates)) (hk : basis k ∈ W.toSubmodule) :
      basis l ∈ W.toSubmodule := by
    have heq : exteriorAction 2 (elementary i j) (basis k) + basis k = basis l := by
      apply coordinates.injective
      rw [map_add, coordinates_action, coordinates_basis, coordinates_basis]
      exact he
    exact heq ▸ step i j k hk
  have h1 : basis 1 ∈ W.toSubmodule := action 2 1 0 1 (by decide +kernel) h
  have h2 : basis 2 ∈ W.toSubmodule := action 3 1 0 2 (by decide +kernel) h
  have h3 : basis 3 ∈ W.toSubmodule := action 4 1 0 3 (by decide +kernel) h
  have h4 : basis 4 ∈ W.toSubmodule := action 1 0 1 4 (by decide +kernel) h1
  have h5 : basis 5 ∈ W.toSubmodule := action 1 0 2 5 (by decide +kernel) h2
  have h6 : basis 6 ∈ W.toSubmodule := action 1 0 3 6 (by decide +kernel) h3
  have h7 : basis 7 ∈ W.toSubmodule := action 2 0 2 7 (by decide +kernel) h2
  have h8 : basis 8 ∈ W.toSubmodule := action 2 0 3 8 (by decide +kernel) h3
  have h9 : basis 9 ∈ W.toSubmodule := action 3 0 3 9 (by decide +kernel) h3
  intro i
  fin_cases i <;> assumption

theorem exteriorSquare_isIrreducible : IsIrreducible (exteriorAction 2) := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos
    (finrank_exteriorModule_two ▸ (by decide : 0 < 10))
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro W
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  have hW' : W.toSubmodule ≠ ⊥ := fun he => hW (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hW'
  obtain ⟨v, hv, hfix⟩ := HeckeAction.exists_nonzero_upperFixed W.toRepresentation
  have he : (v : V) = coordinates v 0 • basis 0 := fixed_coordinates v (fun i =>
    congrArg Subtype.val (hfix i.castSucc i.succ (by simp)))
  have hc : coordinates v 0 = 1 := by
    have hn : coordinates v 0 ≠ 0 := by
      intro hz
      apply hv
      apply Subtype.ext
      simpa [hz] using he
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hn
  have hb : basis 0 ∈ W.toSubmodule := by
    have he' : (v : V) = basis 0 := by simpa only [hc, one_smul] using he
    exact he' ▸ v.property
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← basis.span_eq]
  exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact basis_mem_of_first W hb i)

end Representation.SL5ExteriorSquare

namespace Representation.SL5TenDimensional.Classification
open SL5ExteriorSquare

private theorem irreducible_equiv {H W U : Type*} [_root_.Group H]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) H W} {σ : Representation (ZMod 2) H U}
    (e : ρ.Equiv σ) (hs : IsIrreducible σ) : IsIrreducible ρ := by
  let f := IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mpr
    ((Representation.irreducible_iff_isSimpleModule_asModule σ).mp hs)

private theorem model_irreducible (a : Fin 2) : IsIrreducible (exteriorAction (degree a)) := by
  fin_cases a
  · exact exteriorSquare_isIrreducible
  · exact irreducible_equiv Duality.graphTwistEquiv
      ((irreducible_comp_surjective_iff Duality.graph.toMonoidHom
        Duality.graph.surjective (exteriorAction 2)).mpr exteriorSquare_isIrreducible)

theorem exists_localHighestVector_of_finite
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] [Nontrivial W]
    (ρ : Representation (ZMod 2) Group W) :
    ∃ (J : Finset (Fin 4)) (v : W), v ≠ 0 ∧ LocalHighestVector ρ J v := by
  classical
  let : Nontrivial (HeckeAction.upperFixedSubmodule ρ) := HeckeAction.upperFixedSubmodule_nontrivial ρ
  have hrelations : ZeroHecke.TypeA4Relations (HeckeAction.restrictedOperator ρ) :=
    ⟨HeckeAction.restrictedOperator_sq ρ,
      fun i j hij => (HeckeAction.restrictedOperator_commute ρ i j (Or.inl hij)).eq,
      HeckeAction.restrictedOperator_braid ρ⟩
  obtain ⟨v, hv, heigen⟩ :=
    ZeroHecke.exists_common_zero_or_fixed (HeckeAction.restrictedOperator ρ) hrelations
  let J : Finset (Fin 4) := Finset.univ.filter (fun i => HeckeAction.restrictedOperator ρ i v = v)
  refine ⟨J, (v : W), fun h => hv (Subtype.ext h), v.property, ?_, ?_⟩
  · intro i hi
    have hnot : HeckeAction.restrictedOperator ρ i v ≠ v := by simpa [J] using hi
    exact (HeckeAction.restrictedOperator_eq_zero_iff ρ i v).mp ((heigen i).resolve_left hnot)
  · intro i hi
    exact (HeckeAction.restrictedOperator_eq_self_iff ρ i v).mp ((Finset.mem_filter.mp hi).2)

theorem no_irreducible_six
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Group W) [IsIrreducible ρ]
    (hd : Module.finrank (ZMod 2) W = 6) : False := by
  let : FiniteDimensional (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  let : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨J,v,hv,h⟩ := exists_localHighestVector_of_finite ρ
  have hne : J.Nonempty := by
    by_contra hn
    have hJ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hh := (hJ ▸ h).finrank_eq_one_of_empty hv
    omega
  have hcard : J.card = 1 := by
    have hpos := Finset.card_pos.mpr hne
    by_contra hn
    have hh := h.eleven_le_finrank_of_multiple hv (by omega)
    omega
  obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hcard
  have hi : i = 1 ∨ i = 2 := by
    fin_cases i
    · have hh := h.finrank_le_five_of_endpoint hv (Or.inl rfl); omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have hh := h.finrank_le_five_of_endpoint hv (Or.inr rfl); omega
  have hs : ∃ a : Fin 2, ({i} : Finset (Fin 4)) = {boundaryRoot a} := by
    rcases hi with rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
  obtain ⟨a,ha⟩ := hs
  obtain ⟨f,hf⟩ := intertwiner_of_seed ρ a v
    ((ha ▸ h).hasExteriorSeed (mem_seedParabolicClosure_of_fixes_seed a))
  let := model_irreducible a
  have hf0 : f ≠ 0 := by
    intro hz
    exact hv (by simpa [hz] using hf.symm)
  have hi := (IsIrreducible.injective_or_eq_zero f).resolve_right hf0
  have hb := LinearMap.finrank_le_finrank_of_injective hi
  rw [finrank_model, hd] at hb
  omega
end Representation.SL5TenDimensional.Classification
