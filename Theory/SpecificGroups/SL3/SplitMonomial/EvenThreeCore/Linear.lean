module

public import Theory.GroupTheory.PGroup.AbelianIndexThreeAction
public import Theory.Representation.RankThreePGroupIrreducible
public import Theory.Representation.RankThreeThreeGroupWeightBase
public import Theory.SpecificGroups.SL3.SplitMonomial.InvariantBasis

/-!
# Linear inputs for the characteristic-two three-core argument

A nonabelian three-subgroup of SL₃ has absolutely irreducible natural action.
Schur's lemma therefore makes its full linear centralizer scalar. In
particular its intrinsic center embeds in the ambient center, and every
normalizer automorphism fixes it pointwise. This retains the scalar kernel.
The degree-three weight-base theorem also gives a nonempty family of
abelian index-three subgroups.

These are representation-theoretic inputs to GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603. The degree-three structural
argument is Aschbacher–Smith A.3.21(c), printed pp.55–56 of
`refs/quasithin.pdf`. The scalar-centralizer proof adapts the private Schur
argument in `SplitMonomial/SolvableNormal/WeightKernel.lean`; that shared
module is left unchanged.
-/

open Subgroup Representation
open scoped TensorProduct
namespace Matrix.SL3.SplitMonomial

private theorem exists_scalar_of_mem_centralizer_three
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hp : 3 ≠ p) (Q : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q)
    (d : SpecialLinearGroup (Fin 3) F) (hd : d ∈ centralizer (Q : Set _)) :
    ∃ a : F, (d : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) a := by
  let R := Q.map SpecialLinearGroup.toGL
  let e := Q.equivMapOfInjective SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective
  have hRn : ¬ IsMulCommutative R := by
    intro hc
    let : IsMulCommutative R := hc
    apply hn
    refine ⟨⟨fun x y => e.injective ?_⟩⟩
    simpa only [map_mul] using mul_comm' (e x : R) (e y : R)
  let ρ := (generalLinearNatural (F := F) 3).comp R.subtype
  let : IsAbsolutelyIrreducible ρ :=
    generalLinearNatural_three_isAbsolutelyIrreducible_of_isPGroup (by decide : Odd 3)
      hp R (hQ.map SpecialLinearGroup.toGL) hRn
  let : IsIrreducible ρ :=
    IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible ρ
  let f : Representation.End ρ := {
    toLinearMap := generalLinearNatural 3 (SpecialLinearGroup.toGL d)
    isIntertwining' := by
      intro g
      change generalLinearNatural 3 (SpecialLinearGroup.toGL d) * generalLinearNatural 3 g.val =
        generalLinearNatural 3 g.val * generalLinearNatural 3 (SpecialLinearGroup.toGL d)
      rw [← map_mul, ← map_mul]
      apply congrArg (generalLinearNatural 3)
      obtain ⟨x, hx, he⟩ := g.property
      rw [← he, ← map_mul, ← map_mul, hd x hx] }
  obtain ⟨a, ha⟩ := (isAbsolutelyIrreducible_iff_surjective ρ).mp inferInstance f
  have hlin : generalLinearNatural 3 (SpecialLinearGroup.toGL d) = a • LinearMap.id :=
    (congrArg IntertwiningMap.toLinearMap ha).symm
  refine ⟨a, ?_⟩
  have hmatrix := congrArg LinearMap.toMatrix' hlin
  simpa [generalLinearNatural, Matrix.GeneralLinearGroup.coe_toLin,
    ← Matrix.toLin'_apply', Matrix.smul_one_eq_diagonal] using hmatrix


variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every ambient centralizer element is scalar. -/
public theorem centralizer_le_center_of_nonabelian_three
    (Q : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q) :
    centralizer (Q : Set _) ≤ center (SpecialLinearGroup (Fin 3) F) := by
  intro d hd
  obtain ⟨a, ha⟩ := exists_scalar_of_mem_centralizer_three (by decide : 3 ≠ 2) Q hQ hn d hd
  apply SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨a, ?_, ha.symm⟩
  simpa [ha, Matrix.scalar_apply, Matrix.det_diagonal] using d.det_coe

/-- The intrinsic center embeds in the full special-linear center. -/
public theorem center_map_le_center_of_nonabelian_three
    (Q : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q) :
    (center Q).map Q.subtype ≤ center (SpecialLinearGroup (Fin 3) F) := by
  apply le_trans _ (centralizer_le_center_of_nonabelian_three Q hQ hn)
  rintro _ ⟨z, hz, rfl⟩ x hx
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩)

/-- The literal conjugation automorphism fixes the intrinsic center pointwise. -/
public theorem normalizerAut_fixes_center_of_nonabelian_three
    (Q : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q)
    (g : normalizer (Q : Set (SpecialLinearGroup (Fin 3) F))) (z : Q) (hz : z ∈ center Q) :
    Q.normalizerMonoidHom g z = z := by
  apply Subtype.ext
  change (g : SpecialLinearGroup (Fin 3) F) * z.val * (g : SpecialLinearGroup (Fin 3) F)⁻¹ = z.val
  have hc := center_map_le_center_of_nonabelian_three Q hQ hn (mem_map_of_mem Q.subtype hz)
  have he : (g : SpecialLinearGroup (Fin 3) F) * z.val = z.val * (g : SpecialLinearGroup (Fin 3) F) :=
    mem_center_iff.mp hc g.val
  rw [he]
  simp [mul_assoc]

/-- The weight-base construction provides an actual abelian index-three subgroup. -/
public theorem nonempty_abelianIndexThree_of_nonabelian_three
    (Q : Subgroup (SpecialLinearGroup (Fin 3) F))
    (hQ : IsPGroup 3 Q) (hn : ¬ IsMulCommutative Q) :
    Nonempty (AbelianIndexThree Q) := by
  let E := AlgebraicClosure F
  let rho := (specialLinearNatural (k := F) 3).extendScalars E
  have hrho : Function.Injective rho :=
    (extendScalars_faithful_iff E _).mp (specialLinearNatural_injective 3)
  have hdim : Module.finrank E (E ⊗[F] (Fin 3 → F)) = 3 := by
    rw [Module.finrank_baseChange, Module.finrank_pi, Fintype.card_fin]
  have h3 : (3 : F) ≠ 0 := by
    change (↑(3 : ℕ) : F) ≠ 0
    rw [ne_eq, CharP.cast_eq_zero_iff F 2]
    decide
  have horderF : (Nat.card Q : F) ≠ 0 := by
    obtain ⟨n, hncard⟩ := hQ.exists_card_eq
    rw [hncard, Nat.cast_pow]
    exact pow_ne_zero n h3
  have horder : (Nat.card Q : E) ≠ 0 := by
    intro hz
    apply horderF
    apply (algebraMap F E).injective
    simpa using hz
  obtain ⟨A, _, hAc, hAi, _⟩ :=
    exists_normal_abelian_index_three_ambient_centralizer rho hrho hdim Q hQ hn horder
  exact ⟨⟨A, hAc, hAi⟩⟩
end Matrix.SL3.SplitMonomial
