module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.FieldActors.Centralizer.Descent
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Mathlib.LinearAlgebra.Determinant

/-!
# A fixed root plane for a natural outer field involution

Semilinear descent supplies coordinates in which the actual outer involution
acts coefficientwise, with fixed field of order `2^s`. The genuine elementary
root plane over that field embeds in SL₃(F). Conjugation through the inverse
coordinate change and the marked natural-action equivalence places it inside
`L ∩ C_G(a)`, with order `2^(2*s)`. The fixed-entry matrix criterion and
faithfulness prove commutation with the literal actor `a`.

Adjoining `a`, which lies outside L, gives an elementary abelian subgroup of
`C_G(a)` of order `2^(2*s+1)`. This constructs the attaining subgroup for the
centralizer-rank calculation; its upper bound is a separate argument.

Source: Aschbacher–Smith, K.3.2.1, printed pp.454–455 (PDF pp.465–466),
combined manuscript of 1 March 2004. The root-plane realization and its ATLAS
attribution are in `Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic`.
-/

public section
noncomputable section
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors.Centralizer

variable (F : BinaryField)

private def coordinateSL
    (c : (Fin 3 → F.Carrier) ≃ₗ[F.Carrier] (Fin 3 → F.Carrier)) :
    Matrix.SpecialLinearGroup (Fin 3) F.Carrier →*
      Matrix.SpecialLinearGroup (Fin 3) F.Carrier where
  toFun g := ⟨LinearMap.toMatrix' (c.conjRingEquiv (Matrix.toLin' g.val)), by
    rw [LinearMap.det_toMatrix']
    change LinearMap.det (c.toLinearMap.comp ((Matrix.toLin' g.val).comp
      c.symm.toLinearMap)) = 1
    rw [LinearMap.det_conj, LinearMap.det_toLin']
    exact g.property⟩
  map_one' := by
    apply Subtype.ext
    change LinearMap.toMatrix' (c.conjRingEquiv (Matrix.toLin' 1)) = 1
    rw [Matrix.toLin'_one]
    change LinearMap.toMatrix' (c.conjRingEquiv 1) = 1
    rw [map_one, LinearMap.toMatrix'_one]
  map_mul' g h := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul,
      ← Module.End.mul_eq_comp, map_mul, LinearMap.toMatrix'_mul]
    rfl

private lemma coordinateSL_apply
    (c : (Fin 3 → F.Carrier) ≃ₗ[F.Carrier] (Fin 3 → F.Carrier))
    (g : Matrix.SpecialLinearGroup (Fin 3) F.Carrier) (v : Fin 3 → F.Carrier) :
    (coordinateSL F c g).val.mulVec v = c (g.val.mulVec (c.symm v)) :=
  LinearMap.toMatrix'_mulVec _ _

private lemma coordinateSL_injective
    (c : (Fin 3 → F.Carrier) ≃ₗ[F.Carrier] (Fin 3 → F.Carrier)) :
    Function.Injective (coordinateSL F c) := by
  intro g h he
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply c.conjRingEquiv.injective
  apply LinearMap.toMatrix'.injective
  exact congrArg Subtype.val he

private def fixedSL (σ : F.Carrier ≃+* F.Carrier) :
    U (fixedField F σ) →* Matrix.SpecialLinearGroup (Fin 3) F.Carrier :=
  (Matrix.SpecialLinearGroup.map (fixedField F σ).subtype).comp
    (specialLinear (fixedField F σ))

private lemma fixedSL_injective (σ : F.Carrier ≃+* F.Carrier) :
    Function.Injective (fixedSL F σ) := by
  intro x y he
  apply specialLinear_injective (fixedField F σ)
  apply Subtype.ext
  ext i j
  exact congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F.Carrier => g i j) he

private lemma fixedSL_entry (σ : F.Carrier ≃+* F.Carrier)
    (u : U (fixedField F σ)) (i j : Fin 3) :
    (fixedSL F σ u).val i j ∈ fixedField F σ :=
  ((specialLinear (fixedField F σ) u).val i j).property

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))

/-- The actual fixed root plane in the marked component, with all coordinates constructed. -/
theorem exists_fixed_root_plane (hf : Function.Injective ρ)
    (hs : IsSemilinearExtension ρ L F 3 e) (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hdegree : F.degree = 2 * s) :
    ∃ B : Subgroup G, B ≤ L ⊓ Subgroup.centralizer ({a} : Set G) ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 2 ^ (2 * s) := by
  obtain ⟨c, hc⟩ := exists_fixed_coordinates F ρ L e hf hs a ha haL
  let σ := coefficientAction ρ L F e hs a
  let K := fixedField F σ
  let f : U K →* G := L.subtype.comp (e.groupEquiv.symm.toMonoidHom.comp
    ((coordinateSL F c.symm).comp (fixedSL F σ)))
  have hf' : Function.Injective f := L.subtype_injective.comp
    (e.groupEquiv.symm.injective.comp
      ((coordinateSL_injective F c.symm).comp (fixedSL_injective F σ)))
  let B := (V₁ K).map f
  have hBL : B ≤ L := by
    rintro _ ⟨u, _, rfl⟩
    exact (e.groupEquiv.symm (coordinateSL F c.symm (fixedSL F σ u))).property
  have hBC : B ≤ Subgroup.centralizer ({a} : Set G) := by
    rintro _ ⟨u, _, rfl⟩
    let m := coordinateSL F c.symm (fixedSL F σ u)
    let t := Matrix.toLin' m.val
    have ht : c.conjRingEquiv t = Matrix.toLin' (fixedSL F σ u).val := by
      apply LinearMap.ext
      intro v
      change c (m.val.mulVec (c.symm v)) = (fixedSL F σ u).val.mulVec v
      rw [coordinateSL_apply]
      simp only [LinearEquiv.symm_symm, c.apply_symm_apply]
    have hcomm := (matrix_mem_fixedField_iff_commutes F ρ L e hs a c hc t).mp (by
      rw [ht, LinearMap.toMatrix'_toLin']
      exact fixedSL_entry F σ u)
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply coordinateAction_faithful ρ L F e hf
    apply LinearMap.ext
    intro v
    simp only [map_mul, Module.End.mul_apply]
    have hact (w) : coordinateAction ρ L F e (f u) w = t w := by
      change coordinateAction ρ L F e (e.groupEquiv.symm m : L) w = t w
      rw [coordinateAction_natural, e.groupEquiv.apply_symm_apply]
      rfl
    rw [hact, hact]
    exact hcomm v
  refine ⟨B, le_inf hBL hBC, IsElementaryAbelian.map f, ?_⟩
  change Nat.card ((V₁ K).map f) = _
  rw [Subgroup.card_map_of_injective hf', card_V₁,
    fixedField_card F σ (outer_coefficient_orderOf ρ L F e hf hs a ha haL) s hdegree,
    ← pow_mul, Nat.mul_comm s 2]

/-- Adjoining the actual outer involution to the fixed root plane gives an elementary
subgroup of the literal centralizer of order `2^(2*s+1)`. -/
theorem exists_attaining_elementary_subgroup (hf : Function.Injective ρ)
    (hs : IsSemilinearExtension ρ L F 3 e) (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hdegree : F.degree = 2 * s) :
    ∃ B E : Subgroup G,
      B ≤ L ⊓ Subgroup.centralizer ({a} : Set G) ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 2 ^ (2 * s) ∧
      E = B ⊔ Subgroup.zpowers a ∧ E ≤ Subgroup.centralizer ({a} : Set G) ∧
      a ∈ E ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ (2 * s + 1) := by
  obtain ⟨B, hB, hBE, hcard⟩ := exists_fixed_root_plane F ρ L e hf hs a ha haL s hdegree
  let : IsElementaryAbelian 2 B := hBE
  have hdis := B.disjoint_zpowers_of_prime_order_not_mem a ha
    (fun hm => haL ((hB hm).1))
  obtain ⟨hE, hEcard⟩ := IsElementaryAbelian.fixed_join_card B a ha hdis
    (hB.trans inf_le_right) hcard
  refine ⟨B, B ⊔ Subgroup.zpowers a, hB, hBE, hcard, rfl, ?_,
    (show Subgroup.zpowers a ≤ B ⊔ Subgroup.zpowers a from le_sup_right)
      (Subgroup.mem_zpowers a), hE, hEcard⟩
  apply sup_le (hB.trans inf_le_right)
  exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

/-- Application of the construction to the full natural source input of K.3.2.1.
No fixed basis, root-plane placement, or centralizer model remains assumed. -/
theorem source_outer_attaining_elementary_subgroup {K : GroupClass}
    (h : SourceInput ρ L F 3 K) (a : G) (ha : orderOf a = 2) (haL : a ∉ L)
    (s : ℕ) (hdegree : F.degree = 2 * s) :
    ∃ B E : Subgroup G,
      B ≤ L ⊓ Subgroup.centralizer ({a} : Set G) ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 2 ^ (2 * s) ∧
      E = B ⊔ Subgroup.zpowers a ∧ E ≤ Subgroup.centralizer ({a} : Set G) ∧
      a ∈ E ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ (2 * s + 1) :=
  exists_attaining_elementary_subgroup F ρ L h.natural h.faithful h.semilinear a ha haL s hdegree

end CFSG.Quasithin.ChapterK.Linear.Natural.FieldActors.Centralizer
