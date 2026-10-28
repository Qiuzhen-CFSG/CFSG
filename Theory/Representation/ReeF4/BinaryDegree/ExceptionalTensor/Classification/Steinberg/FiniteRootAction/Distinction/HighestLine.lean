module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.SourceSupport
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.FrobeniusSeparation

/-!
# Intrinsic highest line under the actual positive Ree elements

The same positive finite root-word elements act on every basic family. Their
fixed vectors are exactly the source highest tensor line: Frobenius coefficient
separation and the actual positive filtration lower the degree of any fixed
vector until it reaches degree zero. This characterization is preserved by
finite representation equivalences, independently of algebraic weight labels.

Source: Steinberg (1963), proof of 5.1(1),(4) and its application in 12.2.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction
open Theory.AlgebraicGroup StandardRootSystem AlgebraicTensor
open scoped TensorProduct
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- An original Ree element expressed as an ordered word in positive split roots. -/
@[expose] def PositiveElement (m : ℕ) (g : Model m) : Prop :=
  ∃ w : RootCurves.RootWord m, (∀a∈w, typeF4RootPairing_base.IsPos a.1) ∧
    toSplitGroup m g = RootCurves.splitWord w

private theorem higherWord_hasLeadingTerm (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n : ℕ)
    (p : ∀ i : ℕ, AlgebraicTensor.RootExpansion (basicFactor m B i).action)
    (η : ℕ → EndNode.Weight) (f : CoefficientField m →+* F)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r)
    (w : RootCurves.RootWord m) (hw : RootCurves.HigherSupport true r w) :
    HasLeadingTerm (tensorFiltration m B η n) (weightDegree (rootWeight r))
      (ordinaryPointAction m B n (RootCurves.algebraicWord f w)) 0 := by
  induction w with
  | nil =>
    simp only [RootCurves.algebraicWord, List.map_nil, List.prod_nil, map_one,
      HasLeadingTerm, sub_self]
    exact ⟨(loweringOperators _ _).zero_mem, (loweringOperators _ _).zero_mem⟩
  | cons a w ih =>
    have ha := hw a List.mem_cons_self
    have ha' : typeF4RootPairing_base.IsPos a.1 ∧
        RootCurves.rootDegree r < RootCurves.rootDegree a.1 := by
      simpa only [RootCurves.signedDegree, if_true] using ha
    have hd : weightDegree (rootWeight r) < weightDegree (rootWeight a.1) := by
      have hd' := ha'.2
      rw [← weightDegree_rootWeight, ← weightDegree_rootWeight] at hd'
      exact_mod_cast hd'
    have hroot := (ordinaryPointAction_root_hasLeadingTerm m B n p η a.1 ha'.1 (f a.2)).sub_one
      (tensorFiltration_mono m B η n)
    have hroot' : HasLeadingTerm (tensorFiltration m B η n) (weightDegree (rootWeight r))
        (ordinaryPointAction m B n (algebraicRootElement a.1 (f a.2))) 0 := by
      refine ⟨(loweringOperators _ _).zero_mem, ?_⟩
      simpa only [sub_zero] using loweringOperators_antitone _ (tensorFiltration_mono m B η n)
        (show weightDegree (rootWeight r) + 1 ≤ weightDegree (rootWeight a.1) by omega) hroot
    have htail := ih (fun a ha => hw a (List.mem_cons_of_mem _ ha))
    simpa only [RootCurves.algebraicWord, List.map_cons, List.prod_cons, map_mul, add_zero] using
      hroot'.mul (tensorFiltration_mono m B η n) (weightDegree_rootWeight_pos hr) htail

private theorem positive_curve_leading (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F) (n : ℕ)
    (p : ∀i, RootExpansion (basicFactor m B i).action)
    (η : ℕ → EndNode.Weight) (f : CoefficientField m →+* F)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r)
    (hs : IsShortRoot r) (t : CoefficientField m) :
    ∃ g : Model m, PositiveElement m g ∧
      HasLeadingTerm (tensorFiltration m B η n) (weightDegree (rootWeight r))
        (ordinaryAction m B f n g)
        (((List.range n).map fun i => (f t) ^ (2 ^ i) •
          coordinateMap m B n i ((p i).coeff r 1)).sum) := by
  obtain ⟨g,left,right,hhigh,hg⟩ := RootCurves.exists_positive_root_curve m hr hs t
  have hpos (a) (ha : a ∈ left ++ right) : typeF4RootPairing_base.IsPos a.1 := (hhigh a ha).1
  refine ⟨g, ⟨left ++ (r,t) :: right, ?_, ?_⟩, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hpos a (List.mem_append_left _ h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact hr
      · exact hpos a (List.mem_append_right _ h)
  · simpa only [RootCurves.splitWord,List.map_append,List.prod_append,List.map_cons,
      List.prod_cons,mul_assoc] using hg
  · have hl := higherWord_hasLeadingTerm m B n p η f r hr left
      (fun a ha => hhigh a (List.mem_append_left _ ha))
    have hh := ordinaryPointAction_root_hasLeadingTerm m B n p η r hr (f t)
    have hrr := higherWord_hasLeadingTerm m B n p η f r hr right
      (fun a ha => hhigh a (List.mem_append_right _ ha))
    have h := (hl.mul (tensorFiltration_mono m B η n) (weightDegree_rootWeight_pos hr) hh).mul
      (tensorFiltration_mono m B η n) (weightDegree_rootWeight_pos hr) hrr
    have he : ordinaryAction m B f n g = ordinaryPointAction m B n (modelEmbedding f g) :=
      (DFunLike.congr_fun (ordinaryPointAction_restrict m B f n) g).symm
    have hg' : modelEmbedding f g = RootCurves.algebraicWord f left *
        algebraicRootElement r (f t) * RootCurves.algebraicWord f right := by
      change splitEmbedding f (toSplitGroup m g) = _
      rw [hg,map_mul,map_mul,RootCurves.splitEmbedding_splitWord,
        RootCurves.splitEmbedding_splitWord,splitEmbedding_rootGenerator]
    rw [he,hg',map_mul,map_mul]
    simpa only [zero_add,add_zero] using h

private theorem root_fixes_highest (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F) (b : ℕ → BasicWeight)
    (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (n : ℕ) (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) (t : F) :
    ordinaryPointAction m B n (algebraicRootElement r t) (highestTensor m B v n) =
      highestTensor m B v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (ordinaryPointAction m B n (algebraicRootElement r t) (highestTensor m B v n)) ⊗ₜ[F]
      (((basicFactor m B n).action.action ((Geometry.frobeniusEnd ^ n)
        (algebraicRootElement r t))).val (v n)) = highestTensor m B v n ⊗ₜ[F] v n
    rw [ih]
    congr 1
    have hfr : ∀j : ℕ, (Geometry.frobeniusEnd ^ j) (algebraicRootElement r t) =
        algebraicRootElement r (t ^ (2 ^ j)) := by
      intro j
      induction j with
      | zero => simp
      | succ j hj =>
        rw [pow_succ']
        change Geometry.frobeniusEnd ((Geometry.frobeniusEnd ^ j) (algebraicRootElement r t)) = _
        rw [hj,Geometry.frobeniusEnd_root,←pow_mul,pow_succ]
    change ((basicFactor m B n).action.action ((Geometry.frobeniusEnd ^ n)
      (algebraicRootElement r t))).val (v n) = v n
    rw [hfr]
    exact (hv n).2.1 r hr _

/-- Every actual positive-word Ree element fixes the source highest tensor. -/
theorem positiveElement_fixes_highest (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F) (b : ℕ → BasicWeight)
    (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (f : CoefficientField m →+* F) (n : ℕ) {g : Model m} (hg : PositiveElement m g) :
    ordinaryAction m B f n g (highestTensor m B v n) = highestTensor m B v n := by
  obtain ⟨w,hpos,hg⟩ := hg
  have he : ordinaryAction m B f n g = ordinaryPointAction m B n (modelEmbedding f g) :=
    (DFunLike.congr_fun (ordinaryPointAction_restrict m B f n) g).symm
  have hw : modelEmbedding f g = RootCurves.algebraicWord f w := by
    change splitEmbedding f (toSplitGroup m g) = _
    rw [hg,RootCurves.splitEmbedding_splitWord]
  rw [he,hw]
  clear g he hw hg
  induction w with
  | nil => simp [RootCurves.algebraicWord]
  | cons a w ih =>
    rw [show RootCurves.algebraicWord f (a :: w) =
      algebraicRootElement a.1 (f a.2) * RootCurves.algebraicWord f w from rfl,
      map_mul,Module.End.mul_apply]
    rw [ih (fun a ha => hpos a (List.mem_cons_of_mem _ ha))]
    exact root_fixes_highest m B b v hv n a.1 (hpos a List.mem_cons_self) (f a.2)

omit [IsAlgClosed F] [CharP F 2] in
private theorem rangeSum_apply {V : Type*} [AddCommGroup V] [Module F V]
    (T : ℕ → Module.End F V) (n : ℕ) (x : V) :
    ((List.range n).map T).sum x = ∑j : Fin n, T j.val x := by
  have he : List.ofFn (fun j : Fin n => T j.val) = (List.range n).map T := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      rw [List.getElem_ofFn,List.getElem_map,List.getElem_range]
  rw [←he,List.sum_ofFn,LinearMap.sum_apply]

private theorem fixed_vector_lowers (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F)
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (p : ∀i, RootExpansion (basicFactor m B i).action)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (f : CoefficientField m →+* F) (k : ℤ) (hk : 0 < k)
    (x : basicTensorSpace m B (2*m+1))
    (hx : x ∈ tensorFiltration m B (sourceTensorWeights b) (2*m+1) k)
    (hfix : ∀g, PositiveElement m g → ordinaryAction m B f (2*m+1) g x = x) :
    x ∈ tensorFiltration m B (sourceTensorWeights b) (2*m+1) (k-1) := by
  apply source_tensorFiltration_primitive m B hU p b v hv _ k hk x hx
  intro i hi r
  have hc := coefficients_mem f
    (tensorFiltration m B (sourceTensorWeights b) (2*m+1) (k-weightDegree (rootWeight r.val)-1))
    (fun j : Fin (2*m+1) => coordinateMap m B (2*m+1) j.val ((p j.val).coeff r.val 1) x) (by
      intro t
      obtain ⟨g,hg,hexp⟩ := positive_curve_leading m B (2*m+1) p (sourceTensorWeights b) f
        r.val r.property.2 r.property.1 t
      have he := hexp.2 k x hx
      have hsum : (((List.range (2*m+1)).map fun j => (f t) ^ (2 ^ j) •
          coordinateMap m B (2*m+1) j ((p j).coeff r.val 1)).sum) x =
          ∑ j : Fin (2*m+1), f (t ^ (2 ^ j.val)) •
            coordinateMap m B (2*m+1) j.val ((p j.val).coeff r.val 1) x := by
        rw [rangeSum_apply]
        simp only [map_pow,LinearMap.smul_apply]
      simp only [LinearMap.sub_apply,Module.End.one_apply,hfix g hg,sub_self,zero_sub,
        hsum,sub_add_eq_sub_sub] at he
      exact (Submodule.neg_mem_iff _).mp he)
  exact hc ⟨i,hi⟩

omit [IsAlgClosed F] [CharP F 2] in
private theorem descend_to_zero {V : Type*} [AddCommGroup V] [Module F V]
    (C : ℤ → Submodule F V) (x : V)
    (hlower : ∀k : ℤ, 0 < k → x ∈ C k → x ∈ C (k-1))
    (N : ℕ) (hx : x ∈ C N) : x ∈ C 0 := by
  induction N with
  | zero => exact hx
  | succ N ih =>
    apply ih
    have hh := hlower ((N : ℤ)+1) (by omega) (by simpa only [Nat.cast_add,Nat.cast_one] using hx)
    simpa only [add_sub_cancel_right] using hh

/-- Positive fixed vectors form the intrinsic highest line of the actual finite tensor. -/
theorem positive_fixed_iff_highest (m : ℕ)
    (B : ZMod (2*m+1) → AlgebraicFactor F)
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (p : ∀i, RootExpansion (basicFactor m B i).action)
    (b : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (f : CoefficientField m →+* F) (x : basicTensorSpace m B (2*m+1)) :
    (∀g, PositiveElement m g → ordinaryAction m B f (2*m+1) g x = x) ↔
      x ∈ Submodule.span F {highestTensor m B v (2*m+1)} := by
  constructor
  · intro hfix
    obtain ⟨N,hN⟩ := source_tensorFiltration_exists_top m B hU p b v hv (2*m+1)
    rw [←source_tensorFiltration_zero m B hU p b v hv (2*m+1)]
    apply descend_to_zero (tensorFiltration m B (sourceTensorWeights b) (2*m+1)) x
      (fun k hk hx => fixed_vector_lowers m B hU p b v hv f k hk x hx hfix) N
    rw [hN]
    trivial
  · intro hx g hg
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul,positiveElement_fixes_highest m B b v hv f (2*m+1) hg]

/-- A finite intertwining equivalence takes the actual highest tensor to a
nonzero scalar multiple of the other family's highest tensor. -/
theorem equiv_highest_tensor (m : ℕ)
    (B C : ZMod (2*m+1) → AlgebraicFactor F)
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (q : ∀i, RootExpansion (basicFactor m C i).action)
    (b c : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (w : ∀i, (basicFactor m C i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (hw : ∀i, (basicFactor m C i).IsBasicHighestWeightVector (c i) (w i))
    (f : CoefficientField m →+* F)
    (e : Representation.Equiv (ordinaryAction m B f (2*m+1)) (ordinaryAction m C f (2*m+1))) :
    ∃ a : F, a ≠ 0 ∧ e.toLinearEquiv (highestTensor m B v (2*m+1)) =
      a • highestTensor m C w (2*m+1) := by
  have hmem : e.toLinearEquiv (highestTensor m B v (2*m+1)) ∈
      Submodule.span F {highestTensor m C w (2*m+1)} := by
    apply (positive_fixed_iff_highest m C hU q c w hw f _).mp
    intro g hg
    have he := congrArg (fun A : basicTensorSpace m B (2*m+1) →ₗ[F] basicTensorSpace m C (2*m+1) =>
      A (highestTensor m B v (2*m+1))) (e.toIntertwiningMap.2 g)
    have hh := positiveElement_fixes_highest m B b v hv f (2*m+1) hg
    replace he := he.symm
    change ordinaryAction m C f (2*m+1) g (e.toLinearEquiv (highestTensor m B v (2*m+1))) =
      e.toLinearEquiv (ordinaryAction m B f (2*m+1) g (highestTensor m B v (2*m+1))) at he
    rw [hh] at he
    exact he
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨a, ?_, ha.symm⟩
  intro hz
  have he : e.toLinearEquiv (highestTensor m B v (2*m+1)) = 0 := by simpa only [hz,zero_smul] using ha.symm
  have hn := highestTensor_ne_zero m B v (fun i => (hv i).1) (2*m+1)
  exact hn (e.toLinearEquiv.map_eq_zero_iff.mp he)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction
