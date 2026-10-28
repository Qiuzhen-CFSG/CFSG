module
public import Theory.SpecificGroups.G2.TernaryLeviCocycle
public import Theory.SpecificGroups.G2.TernaryBorelCoordinates

/-!
# Extending the two central ternary Borel shifts

The determinant cocycle extends F ↦ AʲF across the short parabolic and
E ↦ CᵏE across the long parabolic. Each automorphism fixes its whole radical
pointwise and its split torus pointwise. The central cubic transforms by the
full Levi determinant, so the cocycle identity proves multiplicativity on
the actual semidirect endpoint, with inverse the negative shift.

The six-root formulas determine each restriction on every element of the
whole Borel. The two extensions then give an explicit isomorphism from the
normalized twisted amalgam to the untwisted one, with both commuting squares.
MaximalRecognition applies it to the original I.4.5 configuration.
Source: Aschbacher–Smith I.4.5, p.417, via F.4.26, p.288. The imported
ATLAS coordinates retain LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
namespace Atlas.G2.TernaryLevi

private def determinantAction : GL23 →* MulAut (Multiplicative (ZMod 3)) where
  toFun a := (LinearEquiv.smulOfUnit (R:=ZMod 3) (M:=ZMod 3)
    (Matrix.GeneralLinearGroup.det a)).toAddEquiv.toMultiplicative
  map_one' := by ext x; change Multiplicative.ofAdd (_*x.toAdd)=x; simp
  map_mul' a b := by
    ext x
    change Multiplicative.ofAdd ((Matrix.GeneralLinearGroup.det (a*b):ZMod 3)*x.toAdd)=
      Multiplicative.ofAdd ((Matrix.GeneralLinearGroup.det a:ZMod 3)*
        ((Matrix.GeneralLinearGroup.det b:ZMod 3)*x.toAdd))
    simp [mul_assoc]

/-- The distinguished central cubic, with its literal root parameter. -/
def centralRoot (side : Bool) (k : ZMod 3) : radical side :=
  match side with
  | false => TernaryCore.short k 1
  | true => TernaryCore.long k 1

@[simp] theorem centralRoot_zero (side : Bool) : centralRoot side 0=1 := by
  cases side
  · exact TernaryCore.short_one
  · exact TernaryCore.long_one

theorem centralRoot_add (side : Bool) (k l : ZMod 3) :
    centralRoot side (k+l)=centralRoot side k*centralRoot side l := by
  cases side
  · change TernaryCore.short (k+l) 1=TernaryCore.short k 1*TernaryCore.short l 1
    rw [TernaryCore.short_mul]
    simp [TernaryCore.shortForm]
  · change TernaryCore.long (k+l) 1=TernaryCore.long k 1*TernaryCore.long l 1
    rw [TernaryCore.long_mul]
    simp [TernaryCore.longForm]

theorem centralRoot_central (side : Bool) (k : ZMod 3) : centralRoot side k∈center (radical side) := by
  cases side
  · apply TernaryCore.shortExtension.central
    exact TernaryCore.shortQuotient_apply k 1
  · apply TernaryCore.longExtension.central
    exact TernaryCore.longQuotient_apply k 1

private theorem centralRoot_generator (side b : Bool) (k : ZMod 3) :
    coreAction side (generator b) (centralRoot side k)=
      centralRoot side ((generator b).val.det*k) := by
  apply Subtype.ext
  change embedding side (generator b)*(centralRoot side k:Model (ZMod 3))*
    (embedding side (generator b))⁻¹=_
  rw [embedding_generator]
  cases side <;> cases b
  · simpa [rootGenerator,centralRoot,generator,show TernaryCore.shortRoot 1=1 from by decide +kernel] using TernaryCore.short_root k 1
  · simpa [rootGenerator,centralRoot,generator,show TernaryCore.shortWeyl 1=1 from by decide +kernel] using TernaryCore.short_weyl k 1
  · simpa [rootGenerator,centralRoot,generator,show TernaryCore.longRoot 1=1 from by decide +kernel] using TernaryCore.long_root k 1
  · simpa [rootGenerator,centralRoot,generator,show TernaryCore.longWeyl 1=1 from by decide +kernel] using TernaryCore.long_weyl k 1

/-- The full Levi acts on the cubic by its determinant, on the same coordinates. -/
theorem coreAction_centralRoot (side : Bool) (a : GL23) (k : ZMod 3) :
    coreAction side a (centralRoot side k)=centralRoot side (a.val.det*k) := by
  have h := equivariant_of_generators determinantAction (coreAction side)
    (fun x : Multiplicative (ZMod 3)=>centralRoot side x.toAdd)
    (fun b x=>(centralRoot_generator side b x.toAdd).symm) a (Multiplicative.ofAdd k)
  exact h.symm

/-- Extend a scalar multiple of the determinant cocycle through the entire
semidirect endpoint, fixing its radical pointwise. -/
def splitShift (side : Bool) (k : ZMod 3) : MulAut ((radical side) ⋊[coreAction side] GL23) where
  toFun x := ⟨x.left*centralRoot side (k*shiftCocycle x.right),x.right⟩
  invFun x := ⟨x.left*centralRoot side (-k*shiftCocycle x.right),x.right⟩
  left_inv x := by
    apply SemidirectProduct.ext
    rotate_left
    · rfl
    change x.left*centralRoot side (k*shiftCocycle x.right)*
      centralRoot side (-k*shiftCocycle x.right)=x.left
    rw [mul_assoc,←centralRoot_add]
    simp
  right_inv x := by
    apply SemidirectProduct.ext
    rotate_left
    · rfl
    change x.left*centralRoot side (-k*shiftCocycle x.right)*
      centralRoot side (k*shiftCocycle x.right)=x.left
    rw [mul_assoc,←centralRoot_add]
    simp
  map_mul' x y := by
    apply SemidirectProduct.ext
    rotate_left
    · rfl
    change (x.left*coreAction side x.right y.left)*centralRoot side (k*shiftCocycle (x.right*y.right))=
      (x.left*centralRoot side (k*shiftCocycle x.right))*
        coreAction side x.right (y.left*centralRoot side (k*shiftCocycle y.right))
    rw [map_mul,coreAction_centralRoot,shiftCocycle_mul,mul_add,centralRoot_add]
    have hc := (mem_center_iff.mp (centralRoot_central side (k*shiftCocycle x.right)))
      (coreAction side x.right y.left)
    rw [show k*(x.right.val.det*shiftCocycle y.right)=
      x.right.val.det*(k*shiftCocycle y.right) by ring]
    calc
      _=x.left*((coreAction side x.right y.left)*centralRoot side (k*shiftCocycle x.right))*
          centralRoot side (x.right.val.det*(k*shiftCocycle y.right)) := by simp only [mul_assoc]
      _=_ := by rw [hc]; simp only [mul_assoc]

noncomputable def endpointShift (side : Bool) (k : ZMod 3) : MulAut (endpoint side) :=
  ((splitEquiv side).symm.trans (splitShift side k)).trans (splitEquiv side)

@[simp] theorem endpointShift_core (side : Bool) (k : ZMod 3) (v : radical side) :
    endpointShift side k (inclusion (radical_le_endpoint side) v)=
      inclusion (radical_le_endpoint side) v := by
  have hi : splitEquiv side (SemidirectProduct.inl v)=inclusion (radical_le_endpoint side) v :=
    Subtype.ext (splitEquiv_inl side v)
  rw [←hi]
  change splitEquiv side (splitShift side k ((splitEquiv side).symm (splitEquiv side _)))=_
  rw [MulEquiv.symm_apply_apply]
  congr 1
  apply SemidirectProduct.ext
  rotate_left
  · rfl
  change v*centralRoot side (k*shiftCocycle 1)=v
  simp

theorem endpointShift_actor (side : Bool) (k : ZMod 3) (a : GL23) :
    endpointShift side k (endpointEmbedding side a)=
      inclusion (radical_le_endpoint side) (centralRoot side (k*shiftCocycle a))*endpointEmbedding side a := by
  have hi : splitEquiv side (SemidirectProduct.inr a)=endpointEmbedding side a :=
    Subtype.ext (splitEquiv_inr side a)
  rw [←hi]
  change splitEquiv side (splitShift side k ((splitEquiv side).symm (splitEquiv side _)))=_
  rw [MulEquiv.symm_apply_apply]
  have hh : splitShift side k (SemidirectProduct.inr a)=
      SemidirectProduct.inl (centralRoot side (k*shiftCocycle a))*SemidirectProduct.inr a := by
    apply SemidirectProduct.ext
    · simp [splitShift]
    · simp [splitShift]
  rw [hh,map_mul]
  congr 1
  exact Subtype.ext (splitEquiv_inl side _)

end Atlas.G2.TernaryLevi

namespace Atlas.G2.TernaryLevi
open TernaryBorel

private theorem shiftCocycle_of_embedding_torus (side : Bool) (a : GL23)
    (l m : (ZMod 3)ˣ) (ha : embedding side a=torus l m) : shiftCocycle a=0 := by
  have h := embedding_matrix side a
  rw [ha] at h
  have hz (i j : Fin 8) (hij : i≠j) :
      LinearMap.toMatrix' (torus l m).val.toLinearMap i j=0 := by
    rw [LinearMap.toMatrix'_apply]
    change (torusWeights l m i:ZMod 3)*(Pi.single j (1:ZMod 3):Fin 8 → ZMod 3) i=0
    simp only [Pi.single_apply,if_neg hij,mul_zero]
  apply shiftCocycle_diagonal
  all_goals cases side
  · have hh := congrArg (fun M=>M 0 1) h
    change _=a.val 0 1 at hh
    rw [hz _ _ (by decide)] at hh
    exact hh.symm
  · have hh := congrArg (fun M=>M 1 2) h
    change _=a.val 0 1 at hh
    rw [hz _ _ (by decide)] at hh
    exact hh.symm
  · have hh := congrArg (fun M=>M 1 0) h
    change _=a.val 1 0 at hh
    rw [hz _ _ (by decide)] at hh
    exact hh.symm
  · have hh := congrArg (fun M=>M 2 1) h
    change _=a.val 1 0 at hh
    rw [hz _ _ (by decide)] at hh
    exact hh.symm

/-- Each shift fixes the full original split torus pointwise. -/
theorem endpointShift_diagonal (side : Bool) (k : ZMod 3) (l m : (ZMod 3)ˣ) :
    endpointShift side k (inclusion (borel_le_endpoint side) (diagonal l m))=
      inclusion (borel_le_endpoint side) (diagonal l m) := by
  obtain ⟨a,ha⟩ := torus_mem_range side l m
  have he : endpointEmbedding side a=inclusion (borel_le_endpoint side) (diagonal l m) :=
    Subtype.ext ha
  rw [←he,endpointShift_actor,shiftCocycle_of_embedding_torus side a l m ha]
  simp

/-- Coordinates for the single shift associated to one endpoint. -/
@[expose] def shiftCoordinates (side : Bool) (k : ZMod 3) (v : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  twistCoordinates 1 1 (if side then 0 else k) (if side then k else 0) v

private theorem endpointShift_root_one (side : Bool) (k : ZMod 3) (i : Fin 6) :
    endpointShift side k (inclusion (borel_le_endpoint side) (root i 1))=
      inclusion (borel_le_endpoint side) (positive (shiftCoordinates side k (axis i 1))) := by
  by_cases hi : i=(if side then 4 else 5)
  · subst i
    have he : endpointEmbedding side (generator false)=
        inclusion (borel_le_endpoint side) (root (if side then 4 else 5) 1) := by
      apply Subtype.ext
      change embedding side (generator false)=_
      rw [embedding_generator]
      cases side <;> simp [rootGenerator,root,positive,axis,unipotentProduct]
    rw [←he,endpointShift_actor,shiftCocycle_generator]
    simp only [Bool.false_eq_true,ite_false,mul_one]
    rw [he]
    apply Subtype.ext
    change (centralRoot side k:Model (ZMod 3))*(root (if side then 4 else 5) 1:Model (ZMod 3))=_
    cases side <;> simp [centralRoot,TernaryCore.short,TernaryCore.long,root,positive,axis,
      shiftCoordinates,twistCoordinates,unipotentProduct]
  · have hr : (root i 1:Model (ZMod 3))∈radical side := by
      change root i 1∈middleRadical side
      change positive (axis i 1)∈middleRadical side
      rw [positive_mem_radical]
      cases side <;> fin_cases i <;> simp_all [axis]
    have he : inclusion (radical_le_endpoint side) ⟨(root i 1:Model (ZMod 3)),hr⟩=
        inclusion (borel_le_endpoint side) (root i 1) := rfl
    rw [←he,endpointShift_core,he]
    apply congrArg (inclusion (borel_le_endpoint side))
    change positive (axis i 1)=positive _
    apply congrArg positive
    cases side <;> fin_cases i <;> simp_all [shiftCoordinates,twistCoordinates,axis]

private theorem shifted_axis_pow (side : Bool) (k : ZMod 3) (i : Fin 6) (n : ℕ) :
    positive (shiftCoordinates side k (axis i 1))^n=
      positive (shiftCoordinates side k (axis i (n:ZMod 3))) := by
  induction n with
  | zero => apply Subtype.ext; simp [shiftCoordinates,twistCoordinates,axis,positive,unipotentProduct]
  | succ n ih =>
    rw [pow_succ,ih,positive_mul]
    congr 1
    ext j
    cases side <;> fin_cases i <;> fin_cases j <;>
      simp [shiftCoordinates,twistCoordinates,axis,unipotentProductParameters,Nat.cast_add,Nat.cast_one]
    all_goals ring

private theorem endpointShift_root (side : Bool) (k : ZMod 3) (i : Fin 6) (a : ZMod 3) :
    endpointShift side k (inclusion (borel_le_endpoint side) (root i a))=
      inclusion (borel_le_endpoint side) (positive (shiftCoordinates side k (axis i a))) := by
  have he : root i a=root i 1^a.val := by rw [root_pow]; simp
  rw [he,map_pow,map_pow,endpointShift_root_one,←map_pow,shifted_axis_pow]
  simp

/-- Exact action on every element of the entire positive root group. -/
theorem endpointShift_positive (side : Bool) (k : ZMod 3) (v : Fin 6 → ZMod 3) :
    endpointShift side k (inclusion (borel_le_endpoint side) (positive v))=
      inclusion (borel_le_endpoint side) (positive (shiftCoordinates side k v)) := by
  rw [positive_roots]
  simp only [map_mul,endpointShift_root]
  simp only [←map_mul,positive_mul]
  apply congrArg (inclusion (borel_le_endpoint side))
  apply congrArg positive
  ext i
  cases side <;> fin_cases i <;> simp [shiftCoordinates,twistCoordinates,axis,unipotentProductParameters,
      show (3:ZMod 3)=0 from by decide,add_comm]

/-- The single-endpoint correction is known on the whole order-2916 middle. -/
theorem endpointShift_middle (side : Bool) (k : ZMod 3) (v : Fin 6 → ZMod 3)
    (l m : (ZMod 3)ˣ) :
    endpointShift side k (inclusion (borel_le_endpoint side) (positive v*diagonal l m))=
      inclusion (borel_le_endpoint side) (positive (shiftCoordinates side k v)*diagonal l m) := by
  simp only [map_mul,endpointShift_positive,endpointShift_diagonal]

end Atlas.G2.TernaryLevi

namespace Atlas.G2.TernaryLevi
open TernaryBorel

@[simp] theorem endpointShift_neg_apply (side : Bool) (k : ZMod 3) (x : endpoint side) :
    endpointShift side (-k) (endpointShift side k x)=x := by
  change splitEquiv side (splitShift side (-k) ((splitEquiv side).symm
    (splitEquiv side (splitShift side k ((splitEquiv side).symm x)))))=x
  rw [MulEquiv.symm_apply_apply]
  change splitEquiv side ((splitShift side k).symm (splitShift side k ((splitEquiv side).symm x)))=x
  simp only [MulEquiv.symm_apply_apply,MulEquiv.apply_symm_apply]

private theorem endpointShift_mem_middle (side : Bool) (k : ZMod 3) (b : B) :
    (endpointShift side k (inclusion (borel_le_endpoint side) b):Model (ZMod 3))∈B := by
  obtain ⟨v,l,m,rfl⟩ := exists_positive_diagonal b
  rw [endpointShift_middle]
  exact (positive (shiftCoordinates side k v)*diagonal l m).property

/-- The restriction of the actual endpoint automorphism to the entire Borel. -/
noncomputable def middleShift (side : Bool) (k : ZMod 3) : MulAut B where
  toFun b := ⟨endpointShift side k (inclusion (borel_le_endpoint side) b),endpointShift_mem_middle side k b⟩
  invFun b := ⟨endpointShift side (-k) (inclusion (borel_le_endpoint side) b),endpointShift_mem_middle side (-k) b⟩
  left_inv b := by
    apply Subtype.ext
    change (endpointShift side (-k) (endpointShift side k (inclusion (borel_le_endpoint side) b)):
      Model (ZMod 3))=(b:Model (ZMod 3))
    exact congrArg (fun x : endpoint side=>(x:Model (ZMod 3)))
      (endpointShift_neg_apply side k (inclusion (borel_le_endpoint side) b))
  right_inv b := by
    apply Subtype.ext
    change (endpointShift side k (endpointShift side (-k) (inclusion (borel_le_endpoint side) b)):
      Model (ZMod 3))=(b:Model (ZMod 3))
    have hh := endpointShift_neg_apply side (-k) (inclusion (borel_le_endpoint side) b)
    rw [neg_neg] at hh
    exact congrArg (fun x : endpoint side=>(x:Model (ZMod 3))) hh
  map_mul' a b := by apply Subtype.ext; simp only [map_mul]; rfl

theorem middleShift_commutes (side : Bool) (k : ZMod 3) (b : B) :
    endpointShift side k (inclusion (borel_le_endpoint side) b)=
      inclusion (borel_le_endpoint side) (middleShift side k b) := by rfl

/-- Whole-middle formula for the restricted automorphism. -/
theorem middleShift_coordinates (side : Bool) (k : ZMod 3) (v : Fin 6 → ZMod 3)
    (l m : (ZMod 3)ˣ) :
    middleShift side k (positive v*diagonal l m)=
      positive (shiftCoordinates side k v)*diagonal l m := by
  apply Subtype.ext
  change (endpointShift side k (inclusion (borel_le_endpoint side) (positive v*diagonal l m)):
    Model (ZMod 3))= _
  exact congrArg (fun x : endpoint side=>(x:Model (ZMod 3))) (endpointShift_middle side k v l m)

end Atlas.G2.TernaryLevi

namespace Atlas.G2.TernaryBorel
open Theory.GroupTheory TernaryLevi

private theorem shift_compatibility (δ : MulAut B) (j k : ZMod 3)
    (hδ : ∀ (v : Fin 6 → ZMod 3) (l m : (ZMod 3)ˣ),
      δ (positive v*diagonal l m)=positive (twistCoordinates 1 1 j k v)*diagonal l m)
    (b : B) : middleShift true (-k) (δ b)=middleShift false j b := by
  obtain ⟨v,l,m,rfl⟩ := exists_positive_diagonal b
  rw [hδ,middleShift_coordinates,middleShift_coordinates]
  congr 2
  ext i
  fin_cases i <;> simp [shiftCoordinates,twistCoordinates]

/-- The precise two-shift discrepancy factors through actual endpoint
 automorphisms, with both entire-middle commuting squares. -/
@[expose] noncomputable def shiftUntwistIso (δ : MulAut B) (j k : ZMod 3)
    (hδ : ∀ (v : Fin 6 → ZMod 3) (l m : (ZMod 3)ˣ),
      δ (positive v*diagonal l m)=positive (twistCoordinates 1 1 j k v)*diagonal l m) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.twistRight (RankTwoAmalgam.ofSubgroups (P false) B (P true)
        (borel_le_endpoint false) (borel_le_endpoint true)) δ)
      (RankTwoAmalgam.ofSubgroups (P false) B (P true)
        (borel_le_endpoint false) (borel_le_endpoint true)) where
  left := endpointShift false j
  right := endpointShift true (-k)
  middle := middleShift false j
  left_commutes := middleShift_commutes false j
  right_commutes b := by
    change endpointShift true (-k) (inclusion (borel_le_endpoint true) (δ b))=_
    rw [middleShift_commutes,shift_compatibility δ j k hδ]
    rfl

end Atlas.G2.TernaryBorel

namespace Atlas.G2.TernaryLevi
/-- The shift fixes the radical after any original endpoint-inner correction. -/
theorem endpointShift_conjugate_core (side : Bool) (k : ZMod 3)
    (g : endpoint side) (v : radical side) :
    endpointShift side k (g*inclusion (radical_le_endpoint side) v*g⁻¹)=
      g*inclusion (radical_le_endpoint side) v*g⁻¹ := by
  let w : radical side := ⟨(g:Model (ZMod 3))*(v:Model (ZMod 3))*(g:Model (ZMod 3))⁻¹,
    (mem_normalizer_iff.mp (endpoint_normalizes side g.property) v.val).mp v.property⟩
  change endpointShift side k (inclusion (radical_le_endpoint side) w)=
    inclusion (radical_le_endpoint side) w
  exact endpointShift_core side k w
end Atlas.G2.TernaryLevi
