module
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ParabolicAction.Torus
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ParabolicAction.CentralMatrix
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ParabolicAction.RankOne

/-!
# Faithful full-parabolic action on the central first root layer

Factor an arbitrary element as radical times central SL₂ times full torus.
Additivity kills the radical factor, and the proved torus formula is
cubic-linear. If the full action is trivial, testing the two coordinate
vectors kills the off-diagonal SL₂ entries. The remaining actor lies in
the torus, where the two computed weights detect it faithfully.

The pinned central SL₂ calculation in `RankOne` discharges the action premise
of the retained conditional assembly theorems. Thus `firstLayer_linear` and
`firstLayer_kernel` require only additivity, the separate input authorized
by the consumer. The genuine order-three actor sends (1,0) to (1,1), even
when q = 2; this calculation needs no additivity or perfectness hypothesis.
The final square-rigidity argument still requires the independent additivity
and elementary-image vanishing calculations.

Source: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), for
Aschbacher–Smith F.1.12(I)(4), printed pp.263–264 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups
open Matrix
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.ConcreteBruhat
namespace Triality.Standard.Parabolics.CentralRootSquare

/-- Assembly for every parabolic element from the single central root-string
calculation. The torus and arbitrary radical factors have been discharged. -/
theorem firstLayer_linear_of_central_calculation (P : Parameters) (hp : P.prime = 2)
    (hadd : ∀ r s, firstLayer P hp (r * s) = firstLayer P hp r + firstLayer P hp s)
    (hcentral : ∀ A r, firstLayer P hp (conjugation P (centralActor P hp A) r) =
      centralLinear P A (firstLayer P hp r))
    (g : parabolic P .central) :
    ∃ A : (ExtensionField P × ExtensionField P) →ₗ[ExtensionField P]
        (ExtensionField P × ExtensionField P),
      ∀ r, firstLayer P hp (conjugation P g r) = A (firstLayer P hp r) := by
  obtain ⟨x, A, a, rfl⟩ := parabolic_factorization P hp g
  refine ⟨(centralLinear P A).comp (torusLinear P a), ?_⟩
  intro r
  simp only [map_mul, MulAut.mul_apply, firstLayer_conjugation_radical P hp hadd,
    hcentral, firstLayer_torusLinear P hp, LinearMap.comp_apply]

private abbrev up {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t
private abbrev dn {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t
private def torusSL {F : Type*} [Field F] (t : Fˣ) : SL(2, F) :=
  (up t.val * dn (-t.val⁻¹) * up t.val) * (up (-1) * dn 1 * up (-1))

private theorem torusSL_val {F : Type*} [Field F] (t : Fˣ) :
    (torusSL t).val = !![t.val, 0; 0, t.val⁻¹] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [torusSL, up, dn, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single_apply, t.ne_zero]

private theorem diagonal_rankOne_mem_torus (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, ExtensionField P)) (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    (pinnedRankOneMaps P hp).hom 1 A ∈ splitTorus P := by
  have hdet : A 0 0 * A 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h01, h10, mul_zero, sub_zero] using A.det_coe
  have hne : A 0 0 ≠ 0 := by intro h; simp [h] at hdet
  let t : (ExtensionField P)ˣ := Units.mk0 (A 0 0) hne
  have he : A = torusSL t := by
    apply Subtype.ext
    rw [torusSL_val]
    have hinv : A 1 1 = (A 0 0)⁻¹ := by
      apply (mul_left_cancel₀ hne)
      rw [hdet, mul_inv_cancel₀ hne]
    ext r s
    fin_cases r <;> fin_cases s <;> simp [t, h01, h10, hinv]
  rw [he]
  have hh : (pinnedRankOneMaps P hp).hom 1 (torusSL t) = torusWord P 1 t := by
    simp only [torusSL, up, dn, map_mul, PinnedRankOneMaps.positive,
      PinnedRankOneMaps.negative]
    simp only [torusWord, weylWord, inv_neg, inv_one, neg_neg]
  rw [hh]
  exact Subgroup.subset_closure ⟨1, t, rfl⟩

/-- A diagonal central matrix descends into the genuine original torus. -/
theorem centralActor_mem_torus_of_diagonal (P : Parameters) (hp : P.prime = 2)
    (A : SL(2, GaloisField P.prime P.exponent)) (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    (centralActor P hp A).val ∈ torus P := by
  refine ⟨centralElementary P hp A, ?_, rfl⟩
  change elementaryInclusion P (centralElementary P hp A) ∈ splitTorus P
  rw [centralElementary_val]
  apply diagonal_rankOne_mem_torus P hp
  · change baseFieldEmbedding P (A 0 1) = 0
    rw [h01, map_zero]
  · change baseFieldEmbedding P (A 1 0) = 0
    rw [h10, map_zero]

private theorem off_diagonal_of_trivial (P : Parameters)
    (A : SL(2, GaloisField P.prime P.exponent))
    (a : TorusCoordinates.OrbitParameters P)
    (h : ∀ v, centralLinear P A (torusLinear P a v) = v) :
    A 0 1 = 0 ∧ A 1 0 = 0 := by
  have h01 : baseFieldEmbedding P (A 0 1) * torusWeight P a 0 = 0 := by
    simpa [centralLinear_apply, torusLinear] using congrArg Prod.snd (h (1,0))
  have h10 : baseFieldEmbedding P (A 1 0) * torusWeight P a 1 = 0 := by
    simpa [centralLinear_apply, torusLinear] using congrArg Prod.fst (h (0,1))
  constructor
  · exact (map_eq_zero (baseFieldEmbedding P)).mp
      ((mul_eq_zero.mp h01).resolve_right (torusWeight_ne_zero P a 0))
  · exact (map_eq_zero (baseFieldEmbedding P)).mp
      ((mul_eq_zero.mp h10).resolve_right (torusWeight_ne_zero P a 1))

/-- The uniform first-layer kernel theorem, reduced only to the central
root-string calculation. It includes q = 2. -/
theorem firstLayer_kernel_of_central_calculation (P : Parameters) (hp : P.prime = 2)
    (hadd : ∀ r s, firstLayer P hp (r * s) = firstLayer P hp r + firstLayer P hp s)
    (hcentral : ∀ A r, firstLayer P hp (conjugation P (centralActor P hp A) r) =
      centralLinear P A (firstLayer P hp r))
    (g : parabolic P .central)
    (hfix : ∀ r, firstLayer P hp (conjugation P g r) = firstLayer P hp r) :
    g.val ∈ radical P .central := by
  obtain ⟨x, A, a, rfl⟩ := parabolic_factorization P hp g
  have h : ∀ v, centralLinear P A (torusLinear P a v) = v := by
    intro v
    obtain ⟨r, rfl⟩ := firstLayer_surjective P hp v
    simpa only [map_mul, MulAut.mul_apply, firstLayer_conjugation_radical P hp hadd,
      hcentral, firstLayer_torusLinear P hp] using hfix r
  obtain ⟨h01, h10⟩ := off_diagonal_of_trivial P A a h
  have hT : ((centralActor P hp A) * torusActor P hp a).val ∈ torus P :=
    (torus P).mul_mem (centralActor_mem_torus_of_diagonal P hp A h01 h10)
      (TorusCoordinates.torusMulEquiv P hp a).property
  obtain ⟨b, hb⟩ := (TorusCoordinates.torusMulEquiv P hp).surjective
    ⟨((centralActor P hp A) * torusActor P hp a).val, hT⟩
  have hb' : torusActor P hp b = centralActor P hp A * torusActor P hp a :=
    Subtype.ext (congrArg (fun t : torus P => t.val) hb)
  have hone : torusActor P hp b = 1 := by
    apply torusActor_eq_one_of_firstLayer P hp b
    intro r
    rw [hb']
    simpa only [map_mul, MulAut.mul_apply, firstLayer_conjugation_radical P hp hadd]
      using hfix r
  have hh : centralActor P hp A * torusActor P hp a = 1 := hb'.symm.trans hone
  change ((⟨x.val, radical_le_parabolic P .central x.property⟩ : parabolic P .central) *
    centralActor P hp A * torusActor P hp a).val ∈ radical P .central
  rw [mul_assoc, hh, mul_one]
  exact x.property

/-- The genuine prime-field u(1)v(1), including in SL₂(2), acts by (x+y,x)
once the central root-string equation is supplied. -/
theorem firstLayer_orderThree_of_central_calculation (P : Parameters) (hp : P.prime = 2)
    (hcentral : ∀ A r, firstLayer P hp (conjugation P (centralActor P hp A) r) =
      centralLinear P A (firstLayer P hp r))
    (r : radical P .central) :
    firstLayer P hp (conjugation P (orderThreeActor P hp) r) =
      ((firstLayer P hp r).1 + (firstLayer P hp r).2, (firstLayer P hp r).1) :=
  (hcentral (orderThreeMatrix P) r).trans (centralLinear_orderThree P hp _)

/-- An explicit moved vector for the genuine central order-three actor.
No perfectness or lower bound q > 2 occurs. -/
theorem orderThreeActor_moves_of_central_calculation (P : Parameters) (hp : P.prime = 2)
    (hcentral : ∀ A r, firstLayer P hp (conjugation P (centralActor P hp A) r) =
      centralLinear P A (firstLayer P hp r)) :
    ∃ r : radical P .central, firstLayer P hp r = (1,0) ∧
      firstLayer P hp (conjugation P (orderThreeActor P hp) r) = (1,1) ∧
      firstLayer P hp (conjugation P (orderThreeActor P hp) r) ≠ firstLayer P hp r := by
  obtain ⟨r, hr⟩ := firstLayer_surjective P hp (1,0)
  have hm : firstLayer P hp (conjugation P (orderThreeActor P hp) r) = (1,1) := by
    rw [firstLayer_orderThree_of_central_calculation P hp hcentral, hr]
    simp only [add_zero]
  refine ⟨r, hr, hm, ?_⟩
  intro he
  have hh := congrArg Prod.snd (hm.symm.trans (he.trans hr))
  exact one_ne_zero hh

/-- Every element of the full central parabolic acts linearly over the cubic
field on the first root layer. Only root-coordinate additivity remains an input. -/
theorem firstLayer_linear (P : Parameters) (hp : P.prime = 2)
    (hadd : ∀ r s, firstLayer P hp (r * s) = firstLayer P hp r + firstLayer P hp s)
    (g : parabolic P .central) :
    ∃ A : (ExtensionField P × ExtensionField P) →ₗ[ExtensionField P]
        (ExtensionField P × ExtensionField P),
      ∀ r, firstLayer P hp (conjugation P g r) = A (firstLayer P hp r) :=
  firstLayer_linear_of_central_calculation P hp hadd (firstLayer_centralActor P hp) g

/-- An element of the full parabolic fixing the first root layer lies in the
radical, uniformly including q = 2. -/
theorem firstLayer_kernel (P : Parameters) (hp : P.prime = 2)
    (hadd : ∀ r s, firstLayer P hp (r * s) = firstLayer P hp r + firstLayer P hp s)
    (g : parabolic P .central)
    (hfix : ∀ r, firstLayer P hp (conjugation P g r) = firstLayer P hp r) :
    g.val ∈ radical P .central :=
  firstLayer_kernel_of_central_calculation P hp hadd (firstLayer_centralActor P hp) g hfix

/-- Actual conjugation by the pinned prime-field u(1)v(1) on every first-layer
vector, including for SL₂(2). -/
theorem firstLayer_orderThree (P : Parameters) (hp : P.prime = 2)
    (r : radical P .central) :
    firstLayer P hp (conjugation P (orderThreeActor P hp) r) =
      ((firstLayer P hp r).1 + (firstLayer P hp r).2, (firstLayer P hp r).1) :=
  firstLayer_orderThree_of_central_calculation P hp (firstLayer_centralActor P hp) r

/-- The genuine order-three actor moves (1,0) to (1,1). Together with
`orderOf_orderThreeActor`, this gives a moving C₃ actor also at q = 2. -/
theorem orderThreeActor_moves (P : Parameters) (hp : P.prime = 2) :
    ∃ r : radical P .central, firstLayer P hp r = (1,0) ∧
      firstLayer P hp (conjugation P (orderThreeActor P hp) r) = (1,1) ∧
      firstLayer P hp (conjugation P (orderThreeActor P hp) r) ≠ firstLayer P hp r :=
  orderThreeActor_moves_of_central_calculation P hp (firstLayer_centralActor P hp)

end Triality.Standard.Parabolics.CentralRootSquare
end
