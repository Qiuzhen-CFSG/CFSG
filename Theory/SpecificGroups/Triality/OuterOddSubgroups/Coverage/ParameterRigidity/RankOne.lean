module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootFrame
public import Theory.SpecificGroups.Triality.LeviIdentification

/-!
# Field automorphisms recovered from the two triality rank-one frames

The central rank-one map uses the actual q-Frobenius fixed subfield; the arm
map uses the full cubic extension. The pinned SL₂ maps descend faithfully
through elementary fixed points and the central quotient. Preservation of
each signed root group therefore induces an additive parameter equivalence.

The SL₂ braid relation determines the negative parameter at an inverse.
Multiplication of diagonal Weyl words then proves that the positive parameter
map, divided by its value at one, is a field automorphism. The negative map
has the reciprocal scalar and the same field automorphism. No simplicity,
perfectness, global generation, or automorphism coverage is used.

The two node field automorphisms still have to be compared across the folded
edge, and their scalars must be realized in the descended torus.

Source: Steinberg, Theorem 30, steps (2) and (4), and Theorem 36
(`refs/KGroup/GLS3/Chapter2St1.tex`, pp.162–164 and 197–198);
GLS3 §§2.4–2.5 (`refs/KGroup/GLS3/chapter2.tex`). Includes q = 2.
-/

public section
open Matrix
open scoped MatrixGroups
namespace Triality.Standard.OuterOdd.Coverage.ParameterRigidity
open Parabolics ConcreteBruhat ElementaryCentralKernel
noncomputable section

private def splitRankOneWith (P : Parameters) (D : PinnedRankOneMaps P)
    (C : ArmRootCommutation P) :
    (a : Node) → SL(2, RootField P a) →* SplitGroup P
  | .arms => D.armsFixedEmbedding C
  | .central => (D.hom 1).comp
      (SpecialLinearGroup.map (fixedField P).subtype)

private theorem map_transvection {F K : Type*} [Field F] [Field K]
    (f : F →+* K) {i j : Fin 2} (hij : i ≠ j) (t : F) :
    SpecialLinearGroup.map f (SpecialLinearGroup.transvection hij t) =
      SpecialLinearGroup.transvection hij (f t) := by
  apply Subtype.ext
  change Matrix.map (1 + Matrix.single i j t) f = 1 + Matrix.single i j (f t)
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, map_add]
  split_ifs <;> simp only [map_one, map_zero]

private theorem splitRankOneWith_positive (P : Parameters) (D : PinnedRankOneMaps P)
    (C : ArmRootCommutation P) (hp : P.prime = 2) (a : Node) (t : RootField P a) :
    splitRankOneWith P D C a (SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := 1) (by decide) t) = elementaryInclusion P (rootElementary P hp true a t) := by
  cases a with
  | central =>
    change D.hom 1 (SpecialLinearGroup.map (fixedField P).subtype
      (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t)) =
        positiveRoot P 1 t.val
    rw [map_transvection, D.positive]
    rfl
  | arms =>
    change D.hom 0 (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t) * D.hom 2 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t)) *
      D.hom 3 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t))) =
        positiveRoot P 0 t * positiveRoot P 2 (fieldFrobenius P t) *
          positiveRoot P 3 (fieldFrobenius P (fieldFrobenius P t))
    simp only [map_transvection, D.positive]
    rfl
private theorem splitRankOneWith_negative (P : Parameters) (D : PinnedRankOneMaps P)
    (C : ArmRootCommutation P) (hp : P.prime = 2) (a : Node) (t : RootField P a) :
    splitRankOneWith P D C a (SpecialLinearGroup.transvection (i := (1 : Fin 2))
      (j := 0) (by decide) t) = elementaryInclusion P (rootElementary P hp false a t) := by
  cases a with
  | central =>
    change D.hom 1 (SpecialLinearGroup.map (fixedField P).subtype
      (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t)) =
        negativeRoot P 1 t.val
    rw [map_transvection, D.negative]
    rfl
  | arms =>
    change D.hom 0 (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t) * D.hom 2 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t)) *
      D.hom 3 (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.map (fieldFrobenius P).toRingHom (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t))) =
        negativeRoot P 0 t * negativeRoot P 2 (fieldFrobenius P t) *
          negativeRoot P 3 (fieldFrobenius P (fieldFrobenius P t))
    simp only [map_transvection, D.negative]
    rfl

theorem rootField_charTwo (P : Parameters) (hp : P.prime = 2) (i : Node) :
    CharP (RootField P i) 2 := by
  let := rankOneExtensionCharTwo P hp
  cases i <;> dsimp [RootField] <;> infer_instance

private def rankOneSplit (P : Parameters) (hp : P.prime = 2) (i : Node) :
    SL(2, RootField P i) →* SplitGroup P :=
  splitRankOneWith P (pinnedRankOneMaps P hp) (armRootCommutation P hp) i

private theorem rankOneSplit_injective (P : Parameters) (hp : P.prime = 2) (i : Node) :
    Function.Injective (rankOneSplit P hp i) := by
  let := rankOneExtensionCharTwo P hp
  cases i with
  | arms => exact (pinnedRankOneMaps P hp).armsFixedEmbedding_injective _
  | central =>
    intro g h he
    have he' := (pinnedRankOneMaps P hp).injective 1 he
    ext i j
    exact congrArg (fun m : SL(2, ExtensionField P) => m i j) he'

private theorem rankOneSplit_mem_fixed (P : Parameters) (hp : P.prime = 2) (i : Node)
    (g : SL(2, RootField P i)) : rankOneSplit P hp i g ∈ fixedSubgroup P := by
  apply sl2_root_induction (fun g => rankOneSplit P hp i g ∈ fixedSubgroup P) ?_ ?_ ?_ g
  · intro t
    rw [rankOneSplit, splitRankOneWith_positive P _ _ hp]
    exact (rootElementary P hp true i t).val.property
  · intro t
    rw [rankOneSplit, splitRankOneWith_negative P _ _ hp]
    exact (rootElementary P hp false i t).val.property
  · intro g h hg hh
    rw [map_mul]
    exact (fixedSubgroup P).mul_mem hg hh

private def rankOneFixed (P : Parameters) (hp : P.prime = 2) (i : Node) :
    SL(2, RootField P i) →* fixedSubgroup P :=
  (rankOneSplit P hp i).codRestrict _ (rankOneSplit_mem_fixed P hp i)

/-- The faithful rank-one homomorphism uses the actual root field and central quotient. -/
def rankOne (P : Parameters) (hp : P.prime = 2) (i : Node) :
    SL(2, RootField P i) →* Carrier P :=
  letI := rootField_charTwo P hp i
  (toCarrier P).comp (sl2ElementaryLift P hp (rankOneFixed P hp i))

theorem rankOne_injective (P : Parameters) (hp : P.prime = 2) (i : Node) :
    Function.Injective (rankOne P hp i) := by
  let := rootField_charTwo P hp i
  exact sl2_toCarrier_injective P hp _ (fun _ _ h =>
    rankOneSplit_injective P hp i (congrArg Subtype.val h))

@[expose] def upper {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t

@[expose] def lower {F : Type*} [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) t

@[expose] def signed {F : Type*} [Field F] (s : Bool) (t : F) : SL(2, F) :=
  if s then upper t else lower t

theorem rankOne_signed (P : Parameters) (hp : P.prime = 2) (s : Bool)
    (i : Node) (t : RootField P i) :
    rankOne P hp i (signed s t) = rootElement P hp s i t := by
  apply congrArg (toCarrier P)
  apply Subtype.ext
  apply Subtype.ext
  cases s
  · exact splitRankOneWith_negative P _ _ hp i t
  · exact splitRankOneWith_positive P _ _ hp i t

theorem signed_injective {F : Type*} [Field F] (s : Bool) :
    Function.Injective (signed (F := F) s) := by
  intro t u h
  cases s
  · have := congrArg (fun m : SL(2, F) => m 1 0) h
    simpa [signed, lower, SpecialLinearGroup.transvection_coe] using this
  · have := congrArg (fun m : SL(2, F) => m 0 1) h
    simpa [signed, upper, SpecialLinearGroup.transvection_coe] using this

theorem signed_add {F : Type*} [Field F] (s : Bool) (t u : F) :
    signed s (t + u) = signed s t * signed s u := by
  cases s <;> exact SpecialLinearGroup.transvection_add (by decide) t u

theorem rootElement_injective (P : Parameters) (hp : P.prime = 2) (s : Bool) (i : Node) :
    Function.Injective (rootElement P hp s i) := by
  intro t u h
  rw [← rankOne_signed, ← rankOne_signed] at h
  exact signed_injective s (rankOne_injective P hp i h)

theorem rootElement_add (P : Parameters) (hp : P.prime = 2) (s : Bool) (i : Node)
    (t u : RootField P i) :
    rootElement P hp s i (t + u) = rootElement P hp s i t * rootElement P hp s i u := by
  simp only [← rankOne_signed, signed_add, map_mul]

private theorem exists_parameter (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P)) (ha : PreservesRootFrame P hp a) (s : Bool) (i : Node)
    (t : RootField P i) : ∃ u, rootElement P hp s i u = a (rootElement P hp s i t) := by
  exact (ha s i).le ⟨rootElement P hp s i t, Set.mem_range_self t, rfl⟩

/-- The actual additive parameter permutation induced on each signed root group. -/
def rootParameter (P : Parameters) (hp : P.prime = 2) (a : MulAut (Carrier P))
    (ha : PreservesRootFrame P hp a) (s : Bool) (i : Node) : RootField P i ≃+ RootField P i := by
  let f : RootField P i → RootField P i := fun t => (exists_parameter P hp a ha s i t).choose
  have hf (t) : rootElement P hp s i (f t) = a (rootElement P hp s i t) :=
    (exists_parameter P hp a ha s i t).choose_spec
  let h : AddHom (RootField P i) (RootField P i) :=
    { toFun := f
      map_add' := fun t u => rootElement_injective P hp s i (by
        rw [hf, rootElement_add, map_mul, rootElement_add, hf, hf]) }
  refine AddEquiv.ofBijective h ?_
  constructor
  · intro t u h
    exact rootElement_injective P hp s i (a.injective ((hf t).symm.trans
      ((congrArg (rootElement P hp s i) h).trans (hf u))))
  · intro u
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := (ha s i).ge (Set.mem_range_self u)
    exact ⟨t, rootElement_injective P hp s i ((hf t).trans ht)⟩

theorem rootParameter_spec (P : Parameters) (hp : P.prime = 2) (a : MulAut (Carrier P))
    (ha : PreservesRootFrame P hp a) (s : Bool) (i : Node) (t : RootField P i) :
    a (rootElement P hp s i t) = rootElement P hp s i (rootParameter P hp a ha s i t) :=
  (exists_parameter P hp a ha s i t).choose_spec.symm


section MatrixIdentities
variable {F : Type*} [Field F] [CharP F 2]

@[expose] def weyl (t : F) : SL(2, F) := upper t * lower t⁻¹ * upper t

theorem weyl_val (t : F) (ht : t ≠ 0) :
    (weyl t).val = !![0, t; t⁻¹, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upper, lower, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single_apply, ht, CharTwo.add_self_eq_zero]

theorem braid (t : F) (ht : t ≠ 0) :
    upper t * lower t⁻¹ * upper t = lower t⁻¹ * upper t * lower t⁻¹ := by
  apply Subtype.ext
  rw [← weyl, weyl_val t ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upper, lower, SpecialLinearGroup.coe_mul,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.single_apply, ht, CharTwo.add_self_eq_zero]

theorem inverse_of_braid (t u : F) (ht : t ≠ 0)
    (h : upper t * lower u * upper t = lower u * upper t * lower u) : u = t⁻¹ := by
  have he := congrArg (fun m : SL(2, F) => m 0 1) h
  simp [upper, lower, SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.single_apply] at he
  have hprod : t * u = 1 := (CharTwo.add_eq_zero.mp (he.resolve_right ht)).symm
  calc
    u = t⁻¹ * (t * u) := by rw [← mul_assoc, inv_mul_cancel₀ ht, one_mul]
    _ = t⁻¹ := by rw [hprod, mul_one]



theorem weyl_product (t u : F) (ht : t ≠ 0) (hu : u ≠ 0) :
    weyl t * weyl 1 * (weyl u * weyl 1) = weyl (t * u) * weyl 1 := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, weyl_val t ht, weyl_val u hu,
    weyl_val (1 : F) one_ne_zero, weyl_val (t * u) (mul_ne_zero ht hu)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, _root_.mul_inv_rev, mul_comm]

end MatrixIdentities

section RankOneParameters
variable {F G : Type*} [Field F] [CharP F 2] [Group G]
variable (j : SL(2, F) →* G) (hj : Function.Injective j) (a : MulAut G)
variable (u v : F ≃+ F)
variable (hu : ∀ t, a (j (upper t)) = j (upper (u t)))
variable (hv : ∀ t, a (j (lower t)) = j (lower (v t)))

include j hj a u v hu hv

theorem parameter_inverse (t : F) (ht : t ≠ 0) : v t⁻¹ = (u t)⁻¹ := by
  apply inverse_of_braid _ _ (by simpa using (u.injective.ne ht))
  apply hj
  have h := congrArg (fun m => a (j m)) (braid t ht)
  simpa only [map_mul, hu, hv] using h

theorem map_weyl (t : F) (ht : t ≠ 0) : a (j (weyl t)) = j (weyl (u t)) := by
  simp only [weyl, map_mul, hu, hv, parameter_inverse j hj a u v hu hv t ht]

theorem parameter_mul_scaled (t r : F) :
    u (t * r) * (u 1)⁻¹ = (u t * (u 1)⁻¹) * (u r * (u 1)⁻¹) := by
  by_cases ht : t = 0
  · simp [ht]
  by_cases hr : r = 0
  · simp [hr]
  have h := congrArg (fun m => a (j m)) (weyl_product t r ht hr)
  have hw := map_weyl j hj a u v hu hv
  have h' : j (weyl (u t) * weyl (u 1) * (weyl (u r) * weyl (u 1))) =
      j (weyl (u (t * r)) * weyl (u 1)) := by
    simpa only [map_mul, hw t ht, hw r hr, hw 1 one_ne_zero,
      hw (t*r) (mul_ne_zero ht hr)] using h
  have he := congrArg (fun m : SL(2, F) => m 0 0) (hj h')
  have unz {x : F} (hx : x ≠ 0) : u x ≠ 0 := by simpa using u.injective.ne hx
  simpa [SpecialLinearGroup.coe_mul, weyl_val (u t) (unz ht),
    weyl_val (u r) (unz hr), weyl_val (u 1) (unz one_ne_zero),
    weyl_val (u (t*r)) (unz (mul_ne_zero ht hr)),
    Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] using he.symm


/-- Rank-one braid and torus relations force scalar-semilinear root coordinates. -/
theorem exists_rankOne_field : ∃ (c : Fˣ) (e : F ≃+* F),
    (∀ t, u t = c.val * e t) ∧ (∀ t, v t = (c.val)⁻¹ * e t) := by
  have hc : u 1 ≠ 0 := by simp
  let e : F ≃+* F :=
    { toFun := fun t => u t * (u 1)⁻¹
      invFun := fun t => u.symm (t * u 1)
      left_inv := fun t => by simp [hc]
      right_inv := fun t => by simp [hc]
      map_add' := fun t r => by rw [map_add, add_mul]
      map_mul' := parameter_mul_scaled j hj a u v hu hv }
  have hpos (t : F) : u t = (u 1) * e t := by
    change u t = u 1 * (u t * (u 1)⁻¹)
    rw [mul_left_comm, mul_inv_cancel₀ hc, mul_one]
  refine ⟨Units.mk0 (u 1) hc, e, hpos, ?_⟩
  intro t
  by_cases ht : t = 0
  · simp [ht]
  have hv' := parameter_inverse j hj a u v hu hv t⁻¹ (inv_ne_zero ht)
  rw [inv_inv, hpos, map_inv₀, _root_.mul_inv_rev, inv_inv] at hv'
  exact hv'.trans (mul_comm _ _)

end RankOneParameters

/-- Each literal triality rank-one frame recovers its field automorphism and one unit.
The two fields are not yet identified across the folded edge. -/
theorem exists_node_parameters (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P)) (ha : PreservesRootFrame P hp a) (i : Node) :
    ∃ (c : (RootField P i)ˣ) (e : RootField P i ≃+* RootField P i),
      (∀ r, a (rootElement P hp true i r) = rootElement P hp true i (c.val * e r)) ∧
      (∀ r, a (rootElement P hp false i r) = rootElement P hp false i (c.val⁻¹ * e r)) := by
  let := rootField_charTwo P hp i
  let u := rootParameter P hp a ha true i
  let v := rootParameter P hp a ha false i
  have hu (t) : a (rankOne P hp i (upper t)) = rankOne P hp i (upper (u t)) := by
    change a (rankOne P hp i (signed true t)) = rankOne P hp i (signed true (u t))
    simpa only [rankOne_signed] using rootParameter_spec P hp a ha true i t
  have hv (t) : a (rankOne P hp i (lower t)) = rankOne P hp i (lower (v t)) := by
    change a (rankOne P hp i (signed false t)) = rankOne P hp i (signed false (v t))
    simpa only [rankOne_signed] using rootParameter_spec P hp a ha false i t
  obtain ⟨c, e, hpos, hneg⟩ := exists_rankOne_field (rankOne P hp i)
    (rankOne_injective P hp i) a u v hu hv
  refine ⟨c, e, ?_, ?_⟩
  · intro r
    exact (rootParameter_spec P hp a ha true i r).trans
      (congrArg (rootElement P hp true i) (hpos r))
  · intro r
    exact (rootParameter_spec P hp a ha false i r).trans
      (congrArg (rootElement P hp false i) (hneg r))


end
end Triality.Standard.OuterOdd.Coverage.ParameterRigidity
