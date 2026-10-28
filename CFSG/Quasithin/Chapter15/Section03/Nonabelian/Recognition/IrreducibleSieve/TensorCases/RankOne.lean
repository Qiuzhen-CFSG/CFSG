module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases.Models
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases.Placement
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases.Linear
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.Representation.Quotient
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Imprimitive.Split
public import Theory.Representation.ScalarDescent
public import Theory.Representation.SL2.BinarySmallInvolution.Hermitian
public import Theory.Representation.SL2.BinarySmallInvolution.Triple

/-!
# Rank-one involution exclusions for the tensor sieve

The marked involution centralizes the intersection of the ambient Sylow subgroup
with the normal component join. The genuine binary PSL₂ pointwise Sylow-fixer
calculation makes its induced automorphism inner, and the faithful irreducible
binary centralizer argument places the involution in the component itself.

For the minus case, pull the component action back along the canonical SL₂/PSL₂
isomorphism and apply the proved small-degree classification. The invariant
quadratic form excludes the natural action, and the even field exponent excludes
the exceptional triple. The remaining actual Hermitian intertwiner transports
both the involution and its displacement rank. Its half-field exponent is at
least two. This route does not require identifying Hermitian matrices with the
literal minus Omega model.

For the triple case, flat scalar extension preserves the displacement rank by
kernel transport and rank-nullity. The specified representation equivalence
then gives a rank-two involution on the literal three-factor Frobenius tensor.
The intrinsic model bounds give binary displacement at least four in the
Hermitian case and displacement at least three over GF(8) in the triple case.
Both contradict the transported rank two, excluding cases (7) and (16).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.9.3(7),(16),
printed pp.353–357, and the proof of 15.3.58, printed p.1149.
-/

public section

open Subgroup Representation
open scoped MatrixGroups TensorProduct MonoidAlgebra
open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
open Representation.SL2

attribute [local instance] BinarySmall.fixedBinaryAlgebra BinarySmall.spaceBinaryModule

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- A genuine PSL₂ component contains the marked central Sylow involution.
Normality, Sylow restriction, innerness and binary faithfulness are all discharged. -/
theorem marked_mem_rankOne_component {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (e : K ≃* PSL(2,F)) : v ∈ K := by
  apply MathieuCases.marked_mem_component_of_pointwise_fixers h hK e
  intro a S ha
  obtain ⟨x, _, hx⟩ := Theory.PSL2.aut_fixing_sylow_inner S a ha
  exact ⟨x, hx⟩

/-- Transport the placement statement through the canonical binary SL₂ quotient. -/
theorem marked_mem_sl2_component {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (e : K ≃* SL(2,F)) : v ∈ K :=
  marked_mem_rankOne_component h hK (e.trans (Theory.PSL2.sl2QuotientEquiv F))

private theorem transported_involution {F : Type*} [Field F]
    (h : SourceData ρ X T v s) (e : K ≃* SL(2,F)) (hv : v ∈ K) :
    ∃ g : SL(2,F), orderOf g = 2 ∧
      Module.finrank (ZMod 2)
        (LinearMap.range (((ρ.comp K.subtype).comp e.symm.toMonoidHom) g - LinearMap.id)) = 2 := by
  refine ⟨e ⟨v, hv⟩, ?_, ?_⟩
  · rw [e.orderOf_eq, ← Subgroup.orderOf_coe]
    exact h.involution
  · change Module.finrank (ZMod 2) (displacement ρ (e.symm (e ⟨v, hv⟩))) = 2
    rw [e.symm_apply_apply]
    exact h.displacement_rank

set_option backward.isDefEq.respectTransparency false in
/-- The minus case produces a rank-two involution on the actual Hermitian
module with half-field exponent at least two, retaining its genuine intertwiner. -/
theorem minusCase_hermitian_involution (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hc : MinusCase ρ K (s + 1)) :
    ∃ r : ℕ, ∃ hr : 0 < r, letI : NeZero r := ⟨hr.ne'⟩
      2 ≤ r ∧ ∃ g : SL(2,OrthogonalFourMinus.FiniteModel.Field r),
        orderOf g = 2 ∧
        Module.finrank (ZMod 2)
          (RankTwo.movedSpace (BinarySmall.hermitian r) g) = 2 := by
  obtain ⟨n, hn, hneven, ⟨e₀⟩, _, hd, _⟩ := hc
  have hn3 : 3 ≤ n := by have := h.six_le_degree; omega
  let : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ _
  let e := e₀.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n)).symm
  let σ : Representation (ZMod 2) _ W := (ρ.comp K.subtype).comp e.symm.toMonoidHom
  let : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp K.subtype)).mpr hK.irreducible
  have hf : Function.Injective σ := h.faithful.comp (K.subtype_injective.comp e.symm.injective)
  obtain ⟨g, hg, hgdim⟩ := transported_involution h e (marked_mem_rankOne_component h hK e₀)
  change Module.finrank (ZMod 2) (LinearMap.range (σ g - LinearMap.id)) = 2 at hgdim
  rcases binary_small_faithful_classification σ hf n (by omega)
    (GaloisField.card 2 n hn.ne') (by omega) with hnat | hherm | htriple
  · obtain ⟨f⟩ := hnat.2.2
    apply False.elim
    apply h.not_natural_rankOne K (F := GaloisField 2 n)
    refine ⟨e, f.toLinearEquiv, ?_⟩
    intro k w
    have he := congrArg (fun t => t w) (f.isIntertwining' (e k))
    change f.toLinearEquiv (σ (e k) w) =
      BinarySmall.natural (e k) (f.toLinearEquiv w) at he
    change f.toLinearEquiv (ρ (e.symm (e k) : H) w) = _ at he
    rw [e.symm_apply_apply] at he
    exact he

  · obtain ⟨hrn, _, hr, φ, ⟨f⟩⟩ := hherm
    let r := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,GaloisField 2 n)] σ.asModule)
    let : NeZero r := ⟨hr.ne'⟩
    have hm_inj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) φ.toRingHom) := by
      intro a b hab
      apply Subtype.ext
      ext i j
      apply φ.injective
      exact congrArg (fun c : SL(2,OrthogonalFourMinus.FiniteModel.Field r) => c.val i j) hab
    refine ⟨r, hr, by dsimp [r]; omega, Matrix.SpecialLinearGroup.map φ.toRingHom g, ?_, ?_⟩
    · exact (orderOf_injective _ hm_inj g).trans hg
    · have ht := (RankTwo.Imprimitive.displacementRangeEquiv f.toLinearEquiv (σ g)
        ((BinarySmall.hermitian r).comp (Matrix.SpecialLinearGroup.map φ.toRingHom) g)
        (fun w => ((congrArg (fun t => t w) (f.isIntertwining' g))).symm)).finrank_eq
      exact ht.symm.trans hgdim
  · have hn3' := htriple.2.1
    obtain ⟨k, hk⟩ := hneven
    omega

private theorem finrank_range_baseChange {F E V : Type*} [Field F] [Field E]
    [Algebra F E] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : V →ₗ[F] V) :
    Module.finrank E (LinearMap.range (f.baseChange E)) =
      Module.finrank F (LinearMap.range f) := by
  have hk : Module.finrank E (LinearMap.ker (f.baseChange E)) =
      Module.finrank F (LinearMap.ker f) := by
    rw [← LinearMap.baseChange_ker_eq]
    rw [← (Submodule.toBaseChange.toLinearEquiv E (LinearMap.ker f)).finrank_eq]
    exact Module.finrank_baseChange
  have h₁ := LinearMap.finrank_range_add_finrank_ker f
  have h₂ := LinearMap.finrank_range_add_finrank_ker (f.baseChange E)
  rw [hk, Module.finrank_baseChange] at h₂
  omega

set_option backward.isDefEq.respectTransparency false in
/-- The triple case produces a rank-two involution on the literal GF(8)
Frobenius tensor, after preserving the rank under the specified scalar extension. -/
theorem tripleCase_tensor_involution (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hc : TripleCase ρ K (s + 1)) :
    ∃ g : SL(2,GaloisField 2 3), orderOf g = 2 ∧
      Module.finrank (GaloisField 2 3)
        (RankTwo.movedSpace (k := GaloisField 2 3)
          (V := BinarySmall.TripleSpace (GaloisField 2 3)) BinarySmall.triple g) = 2 := by
  let : Algebra (ZMod 2) (GaloisField 2 3) := ZMod.algebra _ _
  obtain ⟨e, ⟨f⟩, _, _⟩ := hc
  obtain ⟨g, hg, hgdim⟩ := transported_involution h e (marked_mem_sl2_component h hK e)
  let σ : Representation (ZMod 2) _ W := (ρ.comp K.subtype).comp e.symm.toMonoidHom
  have hb : Module.finrank (GaloisField 2 3)
      (LinearMap.range ((extendScalars (GaloisField 2 3) σ) g - LinearMap.id)) = 2 := by
    rw [extendScalars_apply, ← LinearMap.baseChange_id, ← LinearMap.baseChange_sub,
      finrank_range_baseChange]
    exact hgdim
  refine ⟨g, hg, ?_⟩
  have ht := (RankTwo.Imprimitive.displacementRangeEquiv
    (k := GaloisField 2 3) (V := GaloisField 2 3 ⊗[ZMod 2] W)
    (W := BinarySmall.TripleSpace (GaloisField 2 3)) f.toLinearEquiv
    ((extendScalars (GaloisField 2 3) σ) g) ((BinarySmall.triple (K := GaloisField 2 3)) g)
    (fun w => ((congrArg (fun t => t w) (f.isIntertwining' g))).symm)).finrank_eq
  exact ht.symm.trans hb

/-- Case (7) is impossible: its actual Hermitian involution has binary
displacement at least four, contradicting the marked displacement plane. -/
theorem not_minusCase (h : SourceData ρ X T v s) (hK : ComponentData ρ K) :
    ¬ MinusCase ρ K (s + 1) := by
  intro hc
  obtain ⟨r, hr, hr2, g, hg, hdim⟩ := minusCase_hermitian_involution h hK hc
  let : NeZero r := ⟨hr.ne'⟩
  have hbound := BinarySmall.HermitianInvolution.rank_ge r g hg
  omega

/-- Case (16) is impossible: the actual triple tensor has involution
displacement at least three, whereas scalar extension preserves rank two. -/
theorem not_tripleCase (h : SourceData ρ X T v s) (hK : ComponentData ρ K) :
    ¬ TripleCase ρ K (s + 1) := by
  intro hc
  obtain ⟨g, hg, hdim⟩ := tripleCase_tensor_involution h hK hc
  have hbound := BinarySmall.TripleInvolution.rank_ge g hg
  omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases
