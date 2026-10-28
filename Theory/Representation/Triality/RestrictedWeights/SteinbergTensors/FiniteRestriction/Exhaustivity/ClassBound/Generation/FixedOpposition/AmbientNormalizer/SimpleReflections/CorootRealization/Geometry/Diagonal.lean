module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Comparison
public import Theory.AlgebraicGroup.Tori.Character.Image
public import Theory.AlgebraicGroup.Tori.Product

/-!
# Diagonal containment from compatible root curves

The diagonal of a compatible SL₂ point map centralizes the ambient torus.
Indeed, torus conjugation scales the two root parameters reciprocally, and
`n(a)⁻¹ n(at) = diag(t⁻¹,t)` is independent of `a`. This argument uses only
matrix identities and the actual root-weight equations.

For a regular map, its diagonal image is a torus. Multiplying it with the
commuting ambient maximal torus again gives a torus, so maximality places the
entire diagonal image in the original torus. Thus diagonal containment is not
an additional premise in constructing a chart from a compatible morphism.

Sources: GLS3, Theorem 1.9.5(d), Remarks 1.9.6, and the defining formulas of
Theorem 1.12.1, `refs/KGroup/GLS3/Chapter1.tex`; the torus-image result is
Proposition 1.4.2(d). No rank-one existence or coroot comparison is used.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.AlgebraicGroup
noncomputable section
universe u
variable {k : Type u} [Field k] [hk : IsAlgClosed k]

include hk in
/-- A cocharacter centralizing a maximal torus has image in that torus. -/
theorem cocharacter_mem_maximalTorus_of_commute
    {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
    (hT : IsMaximalTorus T) (h : Morphism (KMult k) G)
    (hc : ∀ t s, Commute (T.inclusion.onPoints t) (h.onPoints s))
    (s : Variety.Point (KMult k)) : h.onPoints s ∈ T := by
  let : AlgebraicGroup (Variety.prod T.carrierVariety (KMult k)) :=
    AlgebraicGroup.prod _ _
  let f := T.inclusion.comp (Morphism.fst T.carrierVariety (KMult k))
  let g := h.comp (Morphism.snd T.carrierVariety (KMult k))
  let p : Morphism (Variety.prod T.carrierVariety (KMult k)) G :=
    { toVariety := (mulMorphism G).comp (f.toVariety.pair g.toVariety)
      map_one := by
        change f.onPoints 1 * g.onPoints 1 = 1
        simp only [map_one, one_mul]
      map_mul := by
        intro x y
        change f.onPoints (x * y) * g.onPoints (x * y) =
          (f.onPoints x * g.onPoints x) * (f.onPoints y * g.onPoints y)
        rw [map_mul, map_mul]
        have hc' : f.onPoints y * g.onPoints x = g.onPoints x * f.onPoints y :=
          (hc _ _).eq
        calc
          _ = f.onPoints x * (f.onPoints y * g.onPoints x) * g.onPoints y := by
            simp only [mul_assoc]
          _ = _ := by rw [hc']; simp only [mul_assoc] }
  have hp : IsTorus (Variety.prod T.carrierVariety (KMult k)) := by
    obtain ⟨n, ⟨e⟩⟩ := hT.1
    exact ⟨n + 1, ⟨(Iso.prod e (Iso.id (KMult k))).comp (dVarietySuccProdIso n)⟩⟩
  have hle : T ≤ p.imageClosedSubgroup := by
    intro x hx
    obtain ⟨t, rfl⟩ : ∃ t, T.inclusion.onPoints t = x := by
      rw [← Set.mem_range, T.range_inclusion]
      exact hx
    refine ⟨(Variety.prodPointEquiv T.carrierVariety (KMult k)).symm (t, 1), ?_⟩
    change T.inclusion.onPoints ((Variety.prodPointEquiv T.carrierVariety (KMult k))
      ((Variety.prodPointEquiv T.carrierVariety (KMult k)).symm (t, 1))).1 *
      h.onPoints ((Variety.prodPointEquiv T.carrierVariety (KMult k))
      ((Variety.prodPointEquiv T.carrierVariety (KMult k)).symm (t, 1))).2 = _
    simp only [Equiv.apply_symm_apply, map_one, mul_one]
  have heq := hT.2 p.imageClosedSubgroup (morphism_image_isTorus p hp) hle
  rw [← heq]
  refine ⟨(Variety.prodPointEquiv T.carrierVariety (KMult k)).symm (1, s), ?_⟩
  change T.inclusion.onPoints ((Variety.prodPointEquiv T.carrierVariety (KMult k))
    ((Variety.prodPointEquiv T.carrierVariety (KMult k)).symm (1, s))).1 *
    h.onPoints ((Variety.prodPointEquiv T.carrierVariety (KMult k))
    ((Variety.prodPointEquiv T.carrierVariety (KMult k)).symm (1, s))).2 = _
  simp only [Equiv.apply_symm_apply, map_one, one_mul]

variable [CharP k 2]

private def nSL2 (a : kˣ) : Variety.Point (slVariety k 2) :=
  standardSL2UpperMorphism.onPoints (kPlusPoint (a : k)) *
  standardSL2LowerMorphism.onPoints (kPlusPoint (a : k)⁻¹) *
  standardSL2UpperMorphism.onPoints (kPlusPoint (a : k))

private lemma nSL2_matrix (a : kˣ) :
    slPointMatrix 2 (nSL2 a) = !![0, (a : k); (a : k)⁻¹, 0] := by
  change Matrix.transvection (0 : Fin 2) 1 (a : k) *
    Matrix.transvection (1 : Fin 2) 0 (a : k)⁻¹ *
    Matrix.transvection (0 : Fin 2) 1 (a : k) = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transvection,
      Matrix.single_apply, Matrix.one_apply, a.ne_zero, CharTwo.add_self_eq_zero]

private lemma nSL2_inv (a : kˣ) : (nSL2 a)⁻¹ = nSL2 a := by
  have hu (s : k) : (kPlusPoint s)⁻¹ = kPlusPoint s := by
    apply (additiveGroupPointEquiv k).injective
    change Multiplicative.ofAdd (-s) = Multiplicative.ofAdd s
    rw [CharTwo.neg_eq]
  simp only [nSL2, mul_inv_rev, ← map_inv, hu]
  group

private lemma nSL2_ratio (a : kˣ) (t : Variety.Point (KMult k)) :
    (nSL2 a)⁻¹ * nSL2 (a * dPointEquiv 1 t 0) = binarySL2Coroot.onPoints t := by
  apply (slPointEquiv (k := k) 2).injective
  apply Subtype.ext
  change slPointMatrix 2 ((nSL2 a)⁻¹ * nSL2 (a * dPointEquiv 1 t 0)) =
    slPointMatrix 2 (binarySL2Coroot.onPoints t)
  rw [nSL2_inv]
  have hm (x y : Variety.Point (slVariety k 2)) :
      slPointMatrix 2 (x * y) = slPointMatrix 2 x * slPointMatrix 2 y := rfl
  rw [hm, nSL2_matrix, nSL2_matrix, binarySL2Coroot_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal,
      a.ne_zero, mul_comm, mul_left_comm]

/-- A point homomorphism carrying the SL₂ curves to opposite actual root
curves sends every diagonal point to the centralizer of the ambient torus. -/
theorem sl2_diagonal_commute_of_root_equations
    {G : Variety k} [AlgebraicGroup G] (T X Y : ClosedSubgroup G)
    (χ : TorusWeight T) (hp : RootWeightEquation T X χ)
    (hm : RootWeightEquation T Y χ⁻¹)
    (xp : OneParameterParametrization X.carrierVariety)
    (xm : OneParameterParametrization Y.carrierVariety)
    (f : Variety.Point (slVariety k 2) →* Variety.Point G)
    (hfU : ∀ s, f (standardSL2UpperMorphism.onPoints (kPlusPoint s)) =
      X.inclusion.onPoints (xp.value s))
    (hfL : ∀ s, f (standardSL2LowerMorphism.onPoints (kPlusPoint s)) =
      Y.inclusion.onPoints (xm.value s))
    (s : Variety.Point T.carrierVariety) (t : Variety.Point (KMult k)) :
    Commute (T.inclusion.onPoints s) (f (binarySL2Coroot.onPoints t)) := by
  let c : kˣ := torusPointEval T.carrierVariety s χ
  let z := T.inclusion.onPoints s
  have hc : χ.pointCharacter s = (c : k) := rfl
  have hci : (χ⁻¹).pointCharacter s = (c : k)⁻¹ := by
    change ((torusPointEval T.carrierVariety s (χ⁻¹) : kˣ) : k) = _
    rw [map_inv]
    exact Units.val_inv_eq_inv_val _
  have hn (a : kˣ) : z⁻¹ * f (nSL2 a) * z = f (nSL2 (c * a)) := by
    have hp' := hp xp (a : k) s
    have hm' := hm xm (a : k)⁻¹ s
    change z⁻¹ * X.inclusion.onPoints (xp.value (a : k)) * z = _ at hp'
    change z⁻¹ * Y.inclusion.onPoints (xm.value (a : k)⁻¹) * z = _ at hm'
    rw [hc] at hp'
    rw [hci] at hm'
    simp only [nSL2, map_mul, hfU, hfL, Units.val_mul]
    calc
      _ = (z⁻¹ * X.inclusion.onPoints (xp.value (a : k)) * z) *
          (z⁻¹ * Y.inclusion.onPoints (xm.value (a : k)⁻¹) * z) *
          (z⁻¹ * X.inclusion.onPoints (xp.value (a : k)) * z) := by group
      _ = _ := by
        rw [hp', hm']
        rw [show ((c : k) * (a : k))⁻¹ = (c : k)⁻¹ * (a : k)⁻¹ from mul_inv _ _]
        rfl
  have hn1 := hn 1
  simp only [mul_one] at hn1
  have hnq := hn (dPointEquiv 1 t 0)
  have hcoroot : (nSL2 (1 : kˣ))⁻¹ * nSL2 (dPointEquiv 1 t 0) =
      binarySL2Coroot.onPoints t := by simpa only [one_mul] using nSL2_ratio 1 t
  have hz : z⁻¹ * f (binarySL2Coroot.onPoints t) * z =
      f (binarySL2Coroot.onPoints t) := by
    conv_lhs => rw [← hcoroot, map_mul, map_inv]
    calc
      _ = (z⁻¹ * f (nSL2 1) * z)⁻¹ *
          (z⁻¹ * f (nSL2 (dPointEquiv 1 t 0)) * z) := by group
      _ = (f (nSL2 c))⁻¹ * f (nSL2 (c * dPointEquiv 1 t 0)) := by rw [hn1, hnq]
      _ = _ := by rw [← map_inv, ← map_mul, nSL2_ratio]
  have hz' := congrArg (fun v => z * v) hz
  exact (show z * f (binarySL2Coroot.onPoints t) =
    f (binarySL2Coroot.onPoints t) * z by
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hz'.symm)

/-- Curve compatibility supplies the diagonal-containment clause of an SL₂
chart whenever the two root weights are inverse and the torus is maximal. -/
theorem OppositePairSL2Compatible.diagonal_mem_of_maximalTorus
    {G : Variety k} [AlgebraicGroup G] (T X Y : ClosedSubgroup G)
    (hT : IsMaximalTorus T) (χ : TorusWeight T)
    (hp : RootWeightEquation T X χ) (hm : RootWeightEquation T Y χ⁻¹)
    (xp : OneParameterParametrization X.carrierVariety)
    (xm : OneParameterParametrization Y.carrierVariety)
    (f : Morphism (slVariety k 2) (oppositePairGeneratedSubgroup X Y).carrierVariety)
    (hf : OppositePairSL2Compatible X Y xp xm f)
    (t : Variety.Point (KMult k)) :
    (oppositePairGeneratedSubgroup X Y).inclusion.onPoints
      (f.onPoints (binarySL2Coroot.onPoints t)) ∈ T := by
  let q := (oppositePairGeneratedSubgroup X Y).inclusion.comp f
  have hu (s : k) : q.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)) =
      X.inclusion.onPoints (xp.value s) := by
    have h := congrArg (fun p : Morphism (KPlus k)
      (oppositePairGeneratedSubgroup X Y).carrierVariety => p.onPoints (kPlusPoint s)) hf.1
    change (oppositePairPlusMorphism X Y).onPoints (xp.value s) =
      f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s)) at h
    change (oppositePairGeneratedSubgroup X Y).inclusion.onPoints
      (f.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint s))) = _
    rw [← h]
    exact oppositePairPlusMorphism_inclusion_apply X Y (xp.value s)
  have hl (s : k) : q.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint s)) =
      Y.inclusion.onPoints (xm.value s) := by
    have h := congrArg (fun p : Morphism (KPlus k)
      (oppositePairGeneratedSubgroup X Y).carrierVariety => p.onPoints (kPlusPoint s)) hf.2
    change (oppositePairMinusMorphism X Y).onPoints (xm.value s) =
      f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint s)) at h
    change (oppositePairGeneratedSubgroup X Y).inclusion.onPoints
      (f.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint s))) = _
    rw [← h]
    exact oppositePairMinusMorphism_inclusion_apply X Y (xm.value s)
  exact cocharacter_mem_maximalTorus_of_commute hT (q.comp binarySL2Coroot)
    (sl2_diagonal_commute_of_root_equations T X Y χ hp hm xp xm q.onPoints hu hl) t

end
end Theory.AlgebraicGroup
