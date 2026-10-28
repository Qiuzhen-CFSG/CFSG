module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.ProjectiveData
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.TensorStep.PolynomialExpansion
public import Theory.AlgebraicGroup.Semisimple.Versions

/-!
# Rational lifting of an actual simple differential quotient

The given rational factor allows a direct version of Steinberg's lifting
argument. Conjugation preserves the root-operator algebra. The basic rank-one
strings therefore make the infinitesimal cyclic submodule stable under the
signed simple root groups, which generate the actual F₄ carrier. Ordinary
group irreducibility makes this cyclic submodule the whole factor.

For each group element `g`, an implementer from `ConjugationData` converts the
twisted quotient projection into a homomorphism over the root algebra. Every
such homomorphism sends the original highest vector into the quotient's full
positive primitive line. Cyclicity makes it a scalar multiple of the original
projection. Thus the projection kernel is group-invariant, and ordinary group
irreducibility makes the projection an isomorphism.

Transporting the original action along this proved isomorphism supplies all
group relations, regular matrix coefficients, and polynomial root expansions.
The isomorphism sends the specified vector to `Q.highestVector` and respects
the actual root algebra, so the first coefficients and integral coroot weights
are preserved. No differential irreducibility or rational lift is assumed.
The construction works even at weight zero and does not use universality;
the final theorem retains the requested universal-version and nonzero-weight
parameters. No inverse or section of an isogeny is involved.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), Curtis 2.7 and §§4.1–4.9, especially the rank-one strings of 4.3;
DOI 10.1017/S0027763000011016. This proof specializes the lifting problem to a
quotient of the supplied rational highest-weight factor.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
local instance (B : AlgebraicFactor F) : Ring (rootAlgebra B) := (rootAlgebra B).toRing

open ZeroAndMiddle RootPairing.IntegralGeckConstruction in
private theorem subgroup_eq_top_of_signed_simple
    (K : Subgroup (PointGroup F))
    (hpos : ∀ i : Fin 4, ∀ t : F, algebraicRootElement (typeF4SimpleRootIndex i) t ∈ K)
    (hneg : ∀ i : Fin 4, ∀ t : F, algebraicRootElement (-typeF4SimpleRootIndex i) t ∈ K) :
    K = ⊤ := by
  have hs : RootPairing.SimpleGeckGroup.subgroup typeF4RootPairing_base F ≤
      K.map carrierMatrix := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨s, i⟩, a, rfl⟩
    have hp := hpos (typeF4RootPairing_baseEquiv.symm i) a
    have hn := hneg (typeF4RootPairing_baseEquiv.symm i) a
    rw [← typeF4RootPairing_baseEquiv_val, Equiv.apply_symm_apply] at hp hn
    cases s
    · refine ⟨algebraicRootElement (-i : F4Chevalley.Root) a, hn, ?_⟩
      simp only [carrierMatrix_root, F4Chevalley.rootCurve, F4Chevalley.integralOperators,
        rootCurveUnit_neg_simple]
      rfl
    · refine ⟨algebraicRootElement i a, hp, ?_⟩
      simp only [carrierMatrix_root, F4Chevalley.rootCurve, F4Chevalley.integralOperators,
        rootCurveUnit_simple]
      rfl
  have hroot (r : F4Chevalley.Root) (t : F) : algebraicRootElement r t ∈ K := by
    have hm : carrierMatrix (algebraicRootElement r t) ∈ K.map carrierMatrix := by
      rw [carrierMatrix_root]
      exact hs (rootCurveUnit_mem_simpleSubgroup r t)
    obtain ⟨g, hg, he⟩ := hm
    exact carrierMatrix_injective he ▸ hg
  apply top_unique
  rw [← algebraicRootElements_generate]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨r, t⟩, rfl⟩
  exact hroot r t

private theorem invariant_of_signed_simple (B : AlgebraicFactor F) (W : Submodule F B.Space)
    (hpos : ∀ (i : Fin 4) (t : F) w, w ∈ W →
      (B.action.action (algebraicRootElement (typeF4SimpleRootIndex i) t)).val w ∈ W)
    (hneg : ∀ (i : Fin 4) (t : F) w, w ∈ W →
      (B.action.action (algebraicRootElement (-typeF4SimpleRootIndex i) t)).val w ∈ W) :
    IsInvariantSubmodule B.action W := by
  let K : Subgroup (PointGroup F) :=
    { carrier := {g | (∀ w ∈ W, (B.action.action g).val w ∈ W) ∧
        (∀ w ∈ W, (B.action.action g⁻¹).val w ∈ W)}
      one_mem' := by simp
      mul_mem' := by
        rintro g h ⟨hg, hgi⟩ ⟨hh, hhi⟩
        constructor
        · intro w hw
          simpa only [map_mul, Units.val_mul, Module.End.mul_apply] using hg _ (hh w hw)
        · intro w hw
          simpa only [mul_inv_rev, map_mul, Units.val_mul, Module.End.mul_apply] using
            hhi _ (hgi w hw)
      inv_mem' := by
        rintro g ⟨hg, hgi⟩
        exact ⟨hgi, by simpa only [inv_inv] using hg⟩ }
  have hK : K = ⊤ := by
    apply subgroup_eq_top_of_signed_simple
    · intro i t
      exact ⟨hpos i t, by simpa only [ZeroAndMiddle.root_inv] using hpos i (-t)⟩
    · intro i t
      exact ⟨hneg i t, by simpa only [ZeroAndMiddle.root_inv] using hneg i (-t)⟩
  intro g
  exact (show g ∈ K from hK.symm ▸ Subgroup.mem_top g).1

namespace SimpleCyclicQuotient
variable {B : AlgebraicFactor F} {v : B.Space} {Q : SimpleCyclicQuotient B v}

private theorem conjugate_smul (D : Q.ConjugationData) (g : PointGroup F)
    (a : rootAlgebra B) (w : B.Space) :
    (B.action.action g).val (a • w) = D.conjugate g a • (B.action.action g).val w := by
  change (B.action.action g).val ((a : Module.End F B.Space) w) =
    (D.conjugate g a : Module.End F B.Space) ((B.action.action g).val w)
  rw [D.conjugate_eq]
  simp only [Module.End.mul_apply]
  have hi : (B.action.action g⁻¹).val ((B.action.action g).val w) = w := by
    simp [← Module.End.mul_apply, ← Units.val_mul]
  rw [hi]

private theorem cyclic_action_mem (D : Q.ConjugationData) (g : PointGroup F)
    (hg : (B.action.action g).val v ∈ cyclicSubmodule B v)
    {w : B.Space} (hw : w ∈ cyclicSubmodule B v) :
    (B.action.action g).val w ∈ cyclicSubmodule B v := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [conjugate_smul D]
  exact (cyclicSubmodule B v).smul_mem _ hg

/-- Conjugation stability and the restricted rank-one strings make the actual
infinitesimal cyclic submodule equal to the original irreducible factor. -/
public theorem cyclicSubmodule_eq_top [CharP F 2] (D : Q.ConjugationData)
    {b : BasicWeight} (hv : B.IsBasicHighestWeightVector b v) :
    cyclicSubmodule B v = ⊤ := by
  obtain ⟨p⟩ := rootExpansion_nonempty B.action B.irreducible.1
  let W := (cyclicSubmodule B v).restrictScalars F
  have hvW : v ∈ W := Submodule.mem_span_singleton_self v
  have hW : IsInvariantSubmodule B.action W := by
    apply invariant_of_signed_simple
    · intro i t w hw
      apply cyclic_action_mem D _ _ hw
      have hpos : typeF4RootPairing_base.IsPos (typeF4SimpleRootIndex i) :=
        typeF4RootPairing_base.isPos_of_mem_support (typeF4RootPairing_baseEquiv i).property
      rw [hv.2.1 _ hpos]
      exact hvW
    · intro i t w hw
      apply cyclic_action_mem D _ _ hw
      rw [negative_simple_action_basic p hv, p.coeff_one_eq_rootOperator]
      apply W.add_mem hvW
      apply W.smul_mem
      exact (cyclicSubmodule B v).smul_mem (rootGenerator B _) hvW
  rcases B.irreducible.2 W hW with hbot | htop
  · exact False.elim (hv.1 (by simpa only [hbot, Submodule.mem_bot] using hvW))
  · apply top_unique
    intro w _
    exact (show w ∈ W from htop.symm ▸ Submodule.mem_top)

private def fullProjection (Q : SimpleCyclicQuotient B v)
    (hc : cyclicSubmodule B v = ⊤) : B.Space →ₗ[rootAlgebra B] Q.Space :=
  Q.projection.comp (LinearMap.id.codRestrict (cyclicSubmodule B v)
    (fun _ => hc.symm ▸ Submodule.mem_top))

private theorem fullProjection_highest (hc : cyclicSubmodule B v = ⊤) :
    fullProjection Q hc v = Q.highestVector := rfl

private theorem fullProjection_surjective (hc : cyclicSubmodule B v = ⊤) :
    Function.Surjective (fullProjection Q hc) := by
  intro w
  obtain ⟨x, hx⟩ := Q.surjective w
  exact ⟨x.val, hx⟩

private theorem hom_scalar (D : Q.ConjugationData) {b : BasicWeight}
    (hv : B.IsBasicHighestWeightVector b v) (hc : cyclicSubmodule B v = ⊤)
    (f : B.Space →ₗ[rootAlgebra B] Q.Space) :
    ∃ c : F, ∀ w : B.Space, f w = c • fullProjection Q hc w := by
  have hp : ∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r →
      Q.operator r (f v) = 0 := by
    intro r hr
    change rootGenerator B r • f v = 0
    rw [← f.map_smul]
    have hz : rootGenerator B r • v = 0 :=
      EndNode.Multiplicity.rootOperator_eq_zero_of_fixed B r v (hv.2.1 r hr)
    rw [hz, map_zero]
  obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp (D.primitive_line (f v) hp)
  refine ⟨c, ?_⟩
  intro w
  have hw : w ∈ cyclicSubmodule B v := hc.symm ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [f.map_smul, (fullProjection Q hc).map_smul, fullProjection_highest, ← hc', smul_comm]

/-- The primitive line forces the kernel of the actual quotient projection to
be group-stable. Ordinary group irreducibility then makes this projection an
isomorphism, without assuming differential irreducibility. -/
public theorem exists_quotient_equiv [CharP F 2] (D : Q.ConjugationData)
    {b : BasicWeight} (hv : B.IsBasicHighestWeightVector b v) :
    ∃ e : B.Space ≃ₗ[F] Q.Space, e v = Q.highestVector ∧
      ∀ (a : rootAlgebra B) (w : B.Space), e (a • w) = a • e w := by
  have hc := cyclicSubmodule_eq_top D hv
  let P := fullProjection Q hc
  have hker : IsInvariantSubmodule B.action (LinearMap.ker (P.restrictScalars F)) := by
    intro g w hw
    obtain ⟨T, hT⟩ := D.implementer g
    let f : B.Space →ₗ[rootAlgebra B] Q.Space :=
      { toFun := fun x => T.symm (P ((B.action.action g).val x))
        map_add' := by intros; simp only [map_add]
        map_smul' := by
          intro a x
          apply T.injective
          rw [T.apply_symm_apply]
          change P ((B.action.action g).val (a • x)) =
            T (a • T.symm (P ((B.action.action g).val x)))
          rw [conjugate_smul D, P.map_smul, hT, T.apply_symm_apply] }
    obtain ⟨c, hscalar⟩ := hom_scalar D hv hc f
    have hz : f w = 0 := by
      rw [hscalar]
      change c • P w = 0
      rw [show P w = 0 from hw, smul_zero]
    change P ((B.action.action g).val w) = 0
    exact T.symm.injective (hz.trans T.symm.map_zero.symm)
  have hinj : Function.Injective (P.restrictScalars F) := by
    rcases B.irreducible.2 _ hker with hbot | htop
    · exact LinearMap.ker_eq_bot.mp hbot
    · have hz : v ∈ LinearMap.ker (P.restrictScalars F) := htop.symm ▸ Submodule.mem_top
      exact False.elim (Q.highestVector_ne_zero hz)
  refine ⟨LinearEquiv.ofBijective (P.restrictScalars F)
    ⟨hinj, fullProjection_surjective hc⟩, rfl, ?_⟩
  intro a w
  exact P.map_smul a w

private def transportedAction (e : B.Space ≃ₗ[F] Q.Space) :
    RationalRepresentation (F4Chevalley.Carrier (k := F)) Q.Space :=
  ⟨(LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom.comp B.action.action⟩

private theorem transportedAction_apply (e : B.Space ≃ₗ[F] Q.Space)
    (g : PointGroup F) (w : Q.Space) :
    ((transportedAction e).action g).val w = e ((B.action.action g).val (e.symm w)) := rfl

private theorem transportedAction_rational (e : B.Space ≃ₗ[F] Q.Space) :
    IsRationalRepresentation (transportedAction e) := by
  obtain ⟨b₀, f₀, hf₀⟩ := B.irreducible.1
  let b := Module.finBasis F Q.Space
  let c := fun i j => rationalRepresentationLinearMatrixCoefficient B.action b₀ f₀
    ((b.coord i).comp e.toLinearMap) (e.symm (b j))
  have hc : ∀ i j g, c i j g = b.repr (((transportedAction e).action g).val (b j)) i := by
    intro i j g
    rw [show c i j = rationalRepresentationLinearMatrixCoefficient B.action b₀ f₀
      ((b.coord i).comp e.toLinearMap) (e.symm (b j)) from rfl,
      rationalRepresentationLinearMatrixCoefficient_apply B.action b₀ f₀ hf₀]
    rfl
  let ci := fun i j => Variety.PolynomialFunction.pullback
    (Theory.AlgebraicGroup.invMorphism (F4Chevalley.Carrier (k := F))) (c i j)
  have hci : ∀ i j g, ci i j g =
      b.repr ((((transportedAction e).action g)⁻¹).val (b j)) i := by
    intro i j g
    change c i j g⁻¹ = _
    rw [hc, map_inv]
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient b
    (transportedAction e).action c ci hc hci
  refine ⟨b, f, ?_⟩
  intro g
  exact glPointEquivOf_generalLinearRepresentationPoint b ((transportedAction e).action g)

private def transportedExpansion (e : B.Space ≃ₗ[F] Q.Space)
    (p : RootExpansion B.action) : RootExpansion (transportedAction e) where
  coeff r := (p.coeff r).mapRange e.conj (map_zero e.conj)
  eval_eq r t := by
    rw [Finsupp.sum_mapRange_index (fun n => smul_zero (t ^ n))]
    have h := congrArg e.conj (p.eval_eq r t)
    calc
      _ = e.conj (B.action.action (algebraicRootElement r t)).val := by
        simpa only [Finsupp.sum, map_sum, map_smul] using h
      _ = _ := by ext w; rfl

/-- A simple differential quotient with the explicit conjugation data has an
ordinary rational action with its actual coefficients and integral basic
highest weight. The action is transported along the proved quotient
isomorphism, so every group relation and every regular matrix coefficient is
inherited from the original rational factor. -/
public theorem nonempty_rationalLift_of_conjugation [CharP F 2]
    (_hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    {b : BasicWeight} (_hb : b ≠ (0, 0)) (hv : B.IsBasicHighestWeightVector b v)
    (Q : SimpleCyclicQuotient B v) (D : Q.ConjugationData) :
    Nonempty (Q.RationalLift b) := by
  obtain ⟨e, he, ha⟩ := exists_quotient_equiv D hv
  obtain ⟨p⟩ := rootExpansion_nonempty B.action B.irreducible.1
  refine ⟨{ action := transportedAction e
            rational := transportedAction_rational e
            expansion := transportedExpansion e p
            coeff_one := ?_
            positive_fixed := ?_
            coroot_weight := ?_ }⟩
  · intro r
    change e.conj (p.coeff r 1) = Q.operator r
    rw [p.coeff_one_eq_rootOperator]
    ext w
    change e (rootGenerator B r • e.symm w) = rootGenerator B r • w
    rw [ha, e.apply_symm_apply]
  · intro r hr t
    rw [← he, transportedAction_apply, e.symm_apply_apply, hv.2.1 r hr]
  · intro i t
    rw [← he, transportedAction_apply, e.symm_apply_apply, hv.2.2 i t, map_smul]

end SimpleCyclicQuotient
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
