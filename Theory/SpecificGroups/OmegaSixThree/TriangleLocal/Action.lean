module
public import Theory.SpecificGroups.OmegaSixThree.OrthogonalityGraph.UniquenessSystem
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.GroupTheory.Perm.Sign

/-!
# The two four-line actions of the F.5 triangle stabilizer

The standard projective triangle spans the coordinates 0, 1, 5. Its setwise
stabilizer preserves that space and its orthogonal complement. Each ternary
three-space has four singular lines; their literal actions give a homomorphism
to S₄ × S₄, with the triangle-span factor first. Fixing all four lines forces
scalar action on each block. Determinant one makes the scalars agree, and
faithfulness of the actual Omega action removes the common scalar.

Only the 27 possible vectors in a three-space and 16 possible sign patterns
are enumerated. There is no orthogonal-group order computation.
Source: Aschbacher--Smith, F.5.1--F.5.3 and F.5.7, printed pp.300--303.
-/

@[expose] public section

open SixTernaryCoordinates
namespace OmegaSixThree.TriangleLocal
open OrthogonalityGraph
abbrev H := triangleStabilizer

def negative (v : Space) : Prop := v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0
def positive (v : Space) : Prop := v 0 = 0 ∧ v 1 = 0 ∧ v 5 = 0

def negativeBasis (i : Fin 3) : Space := ![e 5, e 0-e 1, e 0+e 1] i

theorem negativeBasis_norm (i : Fin 3) : quadratic (negativeBasis i) = -1 := by
  fin_cases i <;> simp [negativeBasis,quadratic,e] <;> decide

def negativePoint (i : Fin 3) : Point := point (negativeBasis i) (negativeBasis_norm i)

theorem negativePoint_mem (i : Fin 3) : negativePoint i ∈ standardTriangle := by
  fin_cases i <;> simp [negativePoint, negativeBasis, standardTriangle,
    standardFirst, standardSecond, standardThird]

theorem mem_standardTriangle_iff (p : Point) :
    p ∈ standardTriangle ↔ ∃ i, p = negativePoint i := by
  constructor
  · intro h
    simp only [standardTriangle, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  · rintro ⟨i,rfl⟩
    exact negativePoint_mem i

theorem negativeBasis_image (g : H) (i : Fin 3) :
    ∃ j, g.val.val (negativeBasis i) = negativeBasis j ∨
      g.val.val (negativeBasis i) = -negativeBasis j := by
  obtain ⟨j,hj⟩ := (mem_standardTriangle_iff _).mp
    (triangleStabilizer_smul_mem g.property (negativePoint_mem i))
  exact ⟨j, (point_eq_iff _ _ _ _).mp hj⟩

private theorem negativeBasis_negative (i : Fin 3) : negative (negativeBasis i) := by
  fin_cases i <;> simp [negative,negativeBasis,e]

private theorem negative_add {v w : Space} (hv : negative v) (hw : negative w) :
    negative (v+w) := by rcases hv with ⟨h0,h1,h2⟩; rcases hw with ⟨k0,k1,k2⟩; simp [negative,h0,h1,h2,k0,k1,k2]
private theorem negative_smul (c : ZMod 3) {v : Space} (hv : negative v) :
    negative (c • v) := by rcases hv with ⟨h0,h1,h2⟩; simp [negative,h0,h1,h2]
private theorem negative_neg {v : Space} (hv : negative v) : negative (-v) := by
  simpa using negative_smul (-1) hv

private theorem negative_expansion (v : Space) (hv : negative v) :
    v = v 5 • negativeBasis 0 + (-v 0+v 1) • negativeBasis 1 +
      (-v 0-v 1) • negativeBasis 2 := by
  rcases hv with ⟨h2,h3,h4⟩
  ext i
  fin_cases i <;> simp [negativeBasis,e,h2,h3,h4] <;> ring_nf <;>
    simp [show (2 : ZMod 3) = -1 by decide]

theorem negative_image (g : H) (v : Space) (hv : negative v) : negative (g.val.val v) := by
  have hb (i : Fin 3) : negative (g.val.val (negativeBasis i)) := by
    obtain ⟨j,hj | hj⟩ := negativeBasis_image g i
    · rw [hj]; exact negativeBasis_negative j
    · rw [hj]; exact negative_neg (negativeBasis_negative j)
  rw [negative_expansion v hv, map_add, map_add, map_smul, map_smul, map_smul]
  exact negative_add (negative_add (negative_smul _ (hb 0))
    (negative_smul _ (hb 1))) (negative_smul _ (hb 2))

private theorem pairing_positive_negative (v w : Space) (hv : positive v) (hw : negative w) :
    pairing v w = 0 := by
  rcases hv with ⟨h0,h1,h5⟩; rcases hw with ⟨k2,k3,k4⟩
  simp [pairing,h0,h1,h5,k2,k3,k4]

private theorem positive_iff (v : Space) :
    positive v ↔ ∀ i : Fin 3, pairing v (negativeBasis i) = 0 := by
  constructor
  · intro hv i
    exact pairing_positive_negative v _ hv (negativeBasis_negative i)
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    simp [pairing,negativeBasis,e] at h0 h1 h2
    have hv0 : v 0 = 0 := by
      have hh : (2 : ZMod 3) * v 0 = 0 := by linear_combination h1 + h2
      exact (mul_eq_zero.mp hh).resolve_left (by decide)
    exact ⟨hv0, by simpa [hv0] using h2, h0⟩

theorem positive_image (g : H) (v : Space) (hv : positive v) : positive (g.val.val v) := by
  apply (positive_iff _).mpr
  intro i
  have hn := negative_image g⁻¹ (negativeBasis i) (negativeBasis_negative i)
  have he := pairing_orthogonal
    (Subgroup.inclusion omegaPlusSixThree_le_orthogonalGroup g.val)
    v ((g⁻¹).val.val (negativeBasis i))
  change pairing (g.val.val v) (g.val.val (g.val.val⁻¹ (negativeBasis i))) = _ at he
  change pairing (g.val.val v) (g.val.val (g.val.val.symm (negativeBasis i))) = _ at he
  rw [g.val.val.apply_symm_apply] at he
  exact he.trans (pairing_positive_negative _ _ hv hn)

/-- Four singular lines in the triangle span and four in its complement.
The first coordinate is normalized to one in the respective ternary basis. -/
def tetra (side : Bool) (i : Fin 4) : Space :=
  if side then ![![0,0,1,1,1,0],![0,0,1,1,-1,0],![0,0,1,-1,1,0],![0,0,1,-1,-1,0]] i
  else ![![1,0,0,0,0,1],![-1,0,0,0,0,1],![0,1,0,0,0,1],![0,-1,0,0,0,1]] i

def signed (v w : Space) : Prop := v = w ∨ v = -w

theorem signed_refl (v : Space) : signed v v := Or.inl rfl

theorem signed_symm {v w : Space} (h : signed v w) : signed w v := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h]; simp)

theorem signed_trans {u v w : Space} (h : signed u v) (k : signed v w) : signed u w := by
  rcases h with h | h <;> rcases k with k | k
  · exact Or.inl (h.trans k)
  · exact Or.inr (h.trans k)
  · exact Or.inr (by rw [h,k])
  · exact Or.inl (by rw [h,k]; simp)

theorem signed_map (g : LinearGroup) {v w : Space} (h : signed v w) : signed (g v) (g w) := by
  rcases h with h | h
  · exact Or.inl (congrArg g h)
  · exact Or.inr (by rw [h,map_neg])

theorem tetra_ne_zero (side : Bool) (i : Fin 4) : tetra side i ≠ 0 := by
  revert side i
  decide +kernel

theorem tetra_norm (side : Bool) (i : Fin 4) : quadratic (tetra side i) = 0 := by
  revert side i
  decide +kernel

theorem tetra_distinct (side : Bool) (i j : Fin 4) : signed (tetra side i) (tetra side j) ↔ i = j := by
  revert side i j
  unfold signed
  decide +kernel

theorem tetra_negative (i : Fin 4) : negative (tetra false i) := by
  revert i; unfold negative; decide +kernel

theorem tetra_positive (i : Fin 4) : positive (tetra true i) := by
  revert i; unfold positive; decide +kernel

private theorem negative_tetra (v : Space) (hv : negative v) (hq : quadratic v = 0) (hne : v ≠ 0) :
    ∃ i, signed v (tetra false i) := by
  have htable : ∀ a b c : ZMod 3, a^2+b^2-c^2 = 0 →
      (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ∃ i, signed ![a,b,0,0,0,c] (tetra false i) := by unfold signed; decide +kernel
  have he : v = ![v 0,v 1,0,0,0,v 5] := by
    rcases hv with ⟨h2,h3,h4⟩
    ext i; fin_cases i <;> simp [h2,h3,h4]
  rw [he] at hq hne ⊢
  apply htable
  · simpa [quadratic] using hq
  · contrapose! hne
    rcases hne with ⟨h0,h1,h5⟩
    simp [h0,h1,h5]

private theorem positive_tetra (v : Space) (hv : positive v) (hq : quadratic v = 0) (hne : v ≠ 0) :
    ∃ i, signed v (tetra true i) := by
  have htable : ∀ a b c : ZMod 3, a^2+b^2+c^2 = 0 →
      (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      ∃ i, signed ![0,0,a,b,c,0] (tetra true i) := by unfold signed; decide +kernel
  have he : v = ![0,0,v 2,v 3,v 4,0] := by
    rcases hv with ⟨h0,h1,h5⟩
    ext i; fin_cases i <;> simp [h0,h1,h5]
  rw [he] at hq hne ⊢
  apply htable
  · simpa [quadratic] using hq
  · contrapose! hne
    rcases hne with ⟨h2,h3,h4⟩
    simp [h2,h3,h4]

theorem tetra_image (g : H) (side : Bool) (i : Fin 4) :
    ∃ j, signed (g.val.val (tetra side i)) (tetra side j) := by
  have hq : quadratic (g.val.val (tetra side i)) = 0 :=
    (omegaPlusSixThree_le_orthogonalGroup g.val.property _).trans (tetra_norm side i)
  have hn : g.val.val (tetra side i) ≠ 0 := by
    intro hz
    exact tetra_ne_zero side i (g.val.val.injective (hz.trans (map_zero g.val.val).symm))
  cases side
  · exact negative_tetra _ (negative_image g _ (tetra_negative i)) hq hn
  · exact positive_tetra _ (positive_image g _ (tetra_positive i)) hq hn

noncomputable def imageIndex (g : H) (side : Bool) (i : Fin 4) : Fin 4 :=
  (tetra_image g side i).choose

theorem imageIndex_spec (g : H) (side : Bool) (i : Fin 4) :
    signed (g.val.val (tetra side i)) (tetra side (imageIndex g side i)) :=
  (tetra_image g side i).choose_spec

theorem imageIndex_eq (g : H) (side : Bool) (i j : Fin 4)
    (h : signed (g.val.val (tetra side i)) (tetra side j)) : imageIndex g side i = j :=
  (tetra_distinct side _ _).mp (signed_trans (signed_symm (imageIndex_spec g side i)) h)

@[simp] theorem imageIndex_one (side : Bool) (i : Fin 4) : imageIndex 1 side i = i :=
  imageIndex_eq 1 side i i (signed_refl _)

theorem imageIndex_mul (g h : H) (side : Bool) (i : Fin 4) :
    imageIndex (g*h) side i = imageIndex g side (imageIndex h side i) := by
  apply imageIndex_eq
  exact signed_trans (signed_map g.val.val (imageIndex_spec h side i))
    (imageIndex_spec g side (imageIndex h side i))

noncomputable def permutation (g : H) (side : Bool) : Equiv.Perm (Fin 4) where
  toFun := imageIndex g side
  invFun := imageIndex g⁻¹ side
  left_inv i := by rw [←imageIndex_mul,inv_mul_cancel,imageIndex_one]
  right_inv i := by rw [←imageIndex_mul,mul_inv_cancel,imageIndex_one]

/-- The two literal actions on the singular lines of the orthogonal summands.
The triangle-span factor comes first. -/
noncomputable def toProduct : H →* Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) where
  toFun g := (permutation g false,permutation g true)
  map_one' := by apply Prod.ext <;> apply Equiv.ext <;> intro i <;> exact imageIndex_one _ _
  map_mul' g h := by apply Prod.ext <;> apply Equiv.ext <;> intro i <;> exact imageIndex_mul g h _ _


private def signedValue (b : Bool) (v : Space) : Space := if b then -v else v

private theorem tetra_relation (side : Bool) :
    tetra side 0 + tetra side (if side then 3 else 1) =
      tetra side 2 + tetra side (if side then 1 else 3) := by
  revert side; decide +kernel

private theorem tetra_signs_equal (side : Bool) (s : Fin 4 → Bool)
    (h : signedValue (s 0) (tetra side 0) +
        signedValue (s (if side then 3 else 1)) (tetra side (if side then 3 else 1)) =
      signedValue (s 2) (tetra side 2) +
        signedValue (s (if side then 1 else 3)) (tetra side (if side then 1 else 3))) :
    ∀ i, s i = s 0 := by
  have hh : ∀ (side : Bool) (s : Fin 4 → Bool),
      signedValue (s 0) (tetra side 0) +
        signedValue (s (if side then 3 else 1)) (tetra side (if side then 3 else 1)) =
      signedValue (s 2) (tetra side 2) +
        signedValue (s (if side then 1 else 3)) (tetra side (if side then 1 else 3)) →
      ∀ i, s i = s 0 := by decide +kernel
  exact hh side s h

private theorem tetra_expansion (side : Bool) (v : Space)
    (hv : if side then positive v else negative v) :
    ∃ a b c : ZMod 3, v = a • tetra side 0 + b • tetra side 1 + c • tetra side 2 := by
  cases side
  · refine ⟨-v 0+v 1-v 5,v 0+v 1-v 5,v 1,?_⟩
    rcases hv with ⟨h2,h3,h4⟩
    ext i
    fin_cases i <;> simp [tetra,h2,h3,h4] <;> ring_nf <;>
      simp [show (2 : ZMod 3) = -1 by decide, show (3 : ZMod 3) = 0 by decide]
  · refine ⟨-v 3-v 4,-v 2+v 4,-v 2+v 3,?_⟩
    rcases hv with ⟨h0,h1,h5⟩
    ext i
    fin_cases i <;> simp [tetra,h0,h1,h5] <;> ring_nf <;>
      simp [show (2 : ZMod 3) = -1 by decide]

/-- A linear map fixing the four singular lines is scalar on that three-space. -/
private theorem scalar_on_block (g : LinearGroup) (side : Bool)
    (h : ∀ i, signed (g (tetra side i)) (tetra side i)) :
    ∃ b : Bool, ∀ v, (if side then positive v else negative v) →
      g v = signedValue b v := by
  have hh (i : Fin 4) : ∃ b : Bool, g (tetra side i) = signedValue b (tetra side i) := by
    rcases h i with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  choose s hs using hh
  have hr := congrArg g (tetra_relation side)
  simp only [map_add,hs] at hr
  have he := tetra_signs_equal side s hr
  refine ⟨s 0,?_⟩
  intro v hv
  obtain ⟨a,b,c,rfl⟩ := tetra_expansion side v hv
  simp only [map_add,map_smul,hs,he]
  cases s 0 <;> simp only [signedValue,ite_true,ite_false,Bool.false_eq_true,smul_neg]
  abel

private theorem omega_det (g : omegaPlusSixThree) : LinearEquiv.det g.val = 1 := by
  have hle : omegaPlusSixThree ≤ (LinearEquiv.det : LinearGroup →* (ZMod 3)ˣ).ker := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨a,b,_,_,rfl⟩
    change LinearEquiv.det (commutatorWord a b) = 1
    simp [commutatorWord,map_mul,map_inv]
  exact hle g.property

private theorem signChange_det (J : Finset (Fin 6)) :
    (LinearEquiv.det (signChange J) : ZMod 3) = ∏ i : Fin 6, (if i ∈ J then -1 else 1 : ZMod 3) := by
  rw [LinearEquiv.coe_det, ←LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' (signChange J).toLinearMap =
      Matrix.diagonal (fun i : Fin 6 => if i ∈ J then -1 else 1 : Fin 6 → ZMod 3) := by
    ext i j
    simp only [LinearMap.toMatrix'_apply,LinearEquiv.coe_coe,signChange_apply,
      Matrix.diagonal_apply,Pi.single_apply]
    by_cases h : i = j <;> by_cases hi : i ∈ J <;> simp [h,hi]
  rw [hm,Matrix.det_diagonal]

private def negativePart (v : Space) : Space := ![v 0,v 1,0,0,0,v 5]
private def positivePart (v : Space) : Space := ![0,0,v 2,v 3,v 4,0]
private theorem parts_sum (v : Space) : negativePart v + positivePart v = v := by
  ext i; fin_cases i <;> simp [negativePart,positivePart]
private theorem negativePart_mem (v : Space) : negative (negativePart v) := by
  simp [negative,negativePart]
private theorem positivePart_mem (v : Space) : positive (positivePart v) := by
  simp [positive,positivePart]

/-- The simultaneous four-line actions have no kernel in the actual Omega group. -/
theorem toProduct_injective : Function.Injective toProduct := by
  apply (MonoidHom.ker_eq_bot_iff toProduct).mp
  apply bot_unique
  intro g hg
  have hf (side : Bool) (i : Fin 4) : signed (g.val.val (tetra side i)) (tetra side i) := by
    have he : imageIndex g side i = i := by
      cases side
      · exact congrArg (fun p : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) => p.1 i) hg
      · exact congrArg (fun p : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) => p.2 i) hg
    simpa only [he] using imageIndex_spec g side i
  obtain ⟨b,hb⟩ := scalar_on_block g.val.val false (hf false)
  obtain ⟨c,hc⟩ := scalar_on_block g.val.val true (hf true)
  have ha (v : Space) : g.val.val v =
      signedValue b (negativePart v) + signedValue c (positivePart v) := by
    calc
      g.val.val v = g.val.val (negativePart v + positivePart v) := congrArg g.val.val (parts_sum v).symm
      _ = _ := by rw [map_add,hb _ (negativePart_mem v),hc _ (positivePart_mem v)]
  have hbc : b = c := by
    cases b <;> cases c
    · rfl
    · have he : g.val.val = signChange {2,3,4} := by
        ext v i; fin_cases i <;> simp [ha,signedValue,negativePart,positivePart]
      have hd := congrArg (fun x : (ZMod 3)ˣ => (x : ZMod 3)) (omega_det g.val)
      rw [he,signChange_det] at hd
      exact (show ¬ ((∏ i : Fin 6, (if i ∈ ({2,3,4} : Finset (Fin 6)) then -1 else 1 : ZMod 3)) = 1) by decide) hd |>.elim
    · have he : g.val.val = signChange {0,1,5} := by
        ext v i; fin_cases i <;> simp [ha,signedValue,negativePart,positivePart]
      have hd := congrArg (fun x : (ZMod 3)ˣ => (x : ZMod 3)) (omega_det g.val)
      rw [he,signChange_det] at hd
      exact (show ¬ ((∏ i : Fin 6, (if i ∈ ({0,1,5} : Finset (Fin 6)) then -1 else 1 : ZMod 3)) = 1) by decide) hd |>.elim
    · rfl
  have hall (v : Space) : signed (g.val.val v) v := by
    rw [ha,←hbc]
    cases b
    · exact Or.inl (parts_sum v)
    · exact Or.inr (by simpa only [signedValue,Bool.false_eq_true,ite_false,ite_true,←neg_add] using congrArg Neg.neg (parts_sum v))
  have hgone : g.val = 1 := omega_faithful g.val (by
    intro p
    induction p using Quotient.inductionOn with | h v =>
      exact (point_eq_iff _ _ _ _).mpr (hall v.val))
  exact Subgroup.mem_bot.mpr (Subtype.ext hgone)

end OmegaSixThree.TriangleLocal
