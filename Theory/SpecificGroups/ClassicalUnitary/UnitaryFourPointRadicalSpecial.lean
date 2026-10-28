module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
public import Theory.Frattini.BinarySquares

/-!
# The special structure of the unitary-four point radical

The middle-block kernel in the isotropic vector stabilizer has Hermitian
Heisenberg coordinates. Its center consists of the coordinates x = y = 0,
and is isomorphic to the additive fixed field when the field involution is
nontrivial. The trace map is then surjective, so each central element is a
single commutator of root elements. Squares are central; the standard finite
two-group Frattini formula consequently identifies the Frattini subgroup
with this same center.

These results supply the special-group structure in Aschbacher--Smith,
F.1.11 and F.1.12(I)(6), printed pp. 262--263 of `refs/quasithin.pdf`.
The standard finite-field specialization must establish nontriviality of the
involution. No special-group assertion is made for the identity involution.
-/

open scoped commutatorElement
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "R" => radical F σ hσ
local notation "κ" => coordinatesOfRadical F σ hσ

private theorem coord_ext (a b : R) (hx : (κ a).x = (κ b).x)
    (hy : (κ a).y = (κ b).y) (hz : (κ a).z = (κ b).z) : a = b := by
  apply (radicalCoordinatesEquiv F σ hσ).symm.injective
  change κ a = κ b
  cases hca : κ a
  cases hcb : κ b
  simp_all

private theorem coord_mul (a b : R) :
    (κ (a*b)).x = (κ a).x + (κ b).x ∧
    (κ (a*b)).y = (κ a).y + (κ b).y ∧
    (κ (a*b)).z = (κ a).z + (κ b).z + σ (κ a).y * (κ b).x +
      σ (κ a).x * (κ b).y := by
  obtain ⟨c, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective a
  obtain ⟨d, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective b
  exact radical_mul_coordinates F σ hσ c d

private def rootX (x : F) : R := radicalOfCoordinates F σ hσ ⟨x,0,0,by simp⟩
private def rootY (y : F) : R := radicalOfCoordinates F σ hσ ⟨0,y,0,by simp⟩

/-- The central coordinate is an element of the actual fixed subfield. -/
def centralElement (t : FixedBy.subfield F σ) : R :=
  radicalOfCoordinates F σ hσ ⟨0,0,t,by
    have ht : σ (t : F) = t := t.property
    simp [ht, CharTwo.add_self_eq_zero]⟩

private theorem mem_center_of_xy_zero (a : R) (hx : (κ a).x = 0)
    (hy : (κ a).y = 0) : a ∈ Subgroup.center R := by
  rw [Subgroup.mem_center_iff]
  intro b
  apply coord_ext F σ hσ
  · simp [(coord_mul F σ hσ _ _).1, hx]
  · simp [(coord_mul F σ hσ _ _).2.1, hy]
  · simp [(coord_mul F σ hσ _ _).2.2, hx, hy, add_comm]

omit [CharP F 2] in
private theorem vanishing_of_pairings (hnt : ∃ u, σ u ≠ u) (x : F)
    (h : ∀ t, σ x * t = σ t * x) : x = 0 := by
  obtain ⟨u, hu⟩ := hnt
  have hx : σ x = x := by simpa using h 1
  have he : (σ u - u) * x = 0 := by
    have := h u
    rw [hx] at this
    linear_combination -this
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hu)

/-- Nontriviality of the involution makes the alternating commutator pairing
nondegenerate: the center consists precisely of the last coordinate. -/
theorem mem_center_radical_iff (hnt : ∃ u, σ u ≠ u) (a : R) :
    a ∈ Subgroup.center R ↔ (κ a).x = 0 ∧ (κ a).y = 0 := by
  refine ⟨fun ha => ?_, fun ha => mem_center_of_xy_zero F σ hσ a ha.1 ha.2⟩
  have hp := Subgroup.mem_center_iff.mp ha
  constructor
  · apply vanishing_of_pairings F σ hnt
    intro t
    have he := congrArg (fun b : R => (κ b).z) (hp (rootY F σ hσ t))
    simp only [(coord_mul F σ hσ _ _).2.2] at he
    change 0 + (κ a).z + σ t * (κ a).x + σ 0 * (κ a).y =
      (κ a).z + 0 + σ (κ a).y * 0 + σ (κ a).x * t at he
    simpa using he.symm
  · apply vanishing_of_pairings F σ hnt
    intro t
    have he := congrArg (fun b : R => (κ b).z) (hp (rootX F σ hσ t))
    simp only [(coord_mul F σ hσ _ _).2.2] at he
    change 0 + (κ a).z + σ 0 * (κ a).x + σ t * (κ a).y =
      (κ a).z + 0 + σ (κ a).y * t + σ (κ a).x * 0 at he
    simpa using he.symm

/-- The center is the additive group of the fixed field. -/
def centerEquivFixedField (hnt : ∃ u, σ u ≠ u) :
    Subgroup.center R ≃* Multiplicative (FixedBy.subfield F σ) where
  toFun a := Multiplicative.ofAdd ⟨(κ a.val).z, by
    obtain ⟨hx,hy⟩ := (mem_center_radical_iff F σ hσ hnt a.val).mp a.property
    have he := (κ a.val).trace_eq
    rw [hx,hy] at he
    change σ (κ a.val).z = (κ a.val).z
    have hz : (κ a.val).z + σ (κ a.val).z = 0 := by simpa using he
    exact (eq_neg_of_add_eq_zero_right hz).trans (CharTwo.neg_eq _)⟩
  invFun t := ⟨centralElement F σ hσ t.toAdd, by
    exact mem_center_of_xy_zero F σ hσ _ rfl rfl⟩
  left_inv a := by
    apply Subtype.ext
    apply coord_ext F σ hσ
    · exact ((mem_center_radical_iff F σ hσ hnt a.val).mp a.property).1.symm
    · exact ((mem_center_radical_iff F σ hσ hnt a.val).mp a.property).2.symm
    · rfl
  right_inv t := by rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change (κ (a.val*b.val)).z = (κ a.val).z + (κ b.val).z
    rw [(coord_mul F σ hσ _ _).2.2]
    obtain ⟨hx,hy⟩ := (mem_center_radical_iff F σ hσ hnt a.val).mp a.property
    simp [hx,hy]

/-- The order of the center is the order of the fixed field. -/
theorem center_radical_card (hnt : ∃ u, σ u ≠ u) :
    Nat.card (Subgroup.center R) = Nat.card (FixedBy.subfield F σ) := by
  exact Nat.card_congr ((centerEquivFixedField F σ hσ hnt).toEquiv.trans
    (Multiplicative.toAdd : Multiplicative (FixedBy.subfield F σ) ≃ _))

include hσ in
/-- Trace onto the fixed field is surjective for a nonidentity involution. -/
theorem exists_trace_eq (hnt : ∃ u, σ u ≠ u) (t : FixedBy.subfield F σ) :
    ∃ b : F, b + σ b = t := by
  obtain ⟨u, hu⟩ := hnt
  have hd : u + σ u ≠ 0 := by
    intro he
    have he' := eq_neg_of_add_eq_zero_right he
    exact hu (he'.trans (CharTwo.neg_eq _))
  have hf : σ (u + σ u) = u + σ u := by rw [map_add, hσ u, add_comm]
  have ht : σ (t : F) = t := t.property
  refine ⟨(t : F) / (u + σ u) * u, ?_⟩
  rw [map_mul, map_div₀, ht, hf]
  calc
    _ = (t : F) / (u + σ u) * (u + σ u) := by ring
    _ = t := div_mul_cancel₀ _ hd

private def horizontal : R →* Multiplicative (F × F) where
  toFun a := Multiplicative.ofAdd ((κ a).x, (κ a).y)
  map_one' := by
    change Multiplicative.ofAdd ((κ 1).x, (κ 1).y) = 1
    simp [coordinatesOfRadical]
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    exact Prod.ext (coord_mul F σ hσ a b).1 (coord_mul F σ hσ a b).2.1

/-- The radical has nilpotency class at most two. -/
theorem commutator_radical_le_center : commutator R ≤ Subgroup.center R := by
  rw [commutator_def]
  apply Subgroup.commutator_le.mpr
  intro a _ b _
  have he : horizontal F σ hσ ⁅a,b⁆ = 1 := by
    rw [map_commutatorElement]
    exact (Commute.all _ _).commutator_eq
  apply mem_center_of_xy_zero F σ hσ
  · exact congrArg (fun v : Multiplicative (F × F) => v.toAdd.1) he
  · exact congrArg (fun v : Multiplicative (F × F) => v.toAdd.2) he

private def traceFixed (b : F) : FixedBy.subfield F σ :=
  ⟨b + σ b, by change σ (b + σ b) = b + σ b; rw [map_add, hσ b, add_comm]⟩

private theorem root_commutator (b : F) :
    ⁅rootX F σ hσ 1, rootY F σ hσ b⁆ =
      centralElement F σ hσ (traceFixed F σ hσ b) := by
  have he : rootX F σ hσ 1 * rootY F σ hσ b =
      centralElement F σ hσ (traceFixed F σ hσ b) *
        (rootY F σ hσ b * rootX F σ hσ 1) := by
    apply coord_ext F σ hσ
    · simp only [(coord_mul F σ hσ _ _).1]
      change 1 + 0 = 0 + (0 + 1 : F)
      simp
    · simp only [(coord_mul F σ hσ _ _).2.1]
      change 0 + b = 0 + (b + 0)
      simp
    · simp only [(coord_mul F σ hσ _ _).2.2,
        (coord_mul F σ hσ _ _).1, (coord_mul F σ hσ _ _).2.1]
      change 0 + 0 + σ 0 * 0 + σ 1 * b =
        (b + σ b) + (0 + 0 + σ b * 1 + σ 0 * 0) + σ 0 * (0 + 1) + σ 0 * (b + 0)
      simp [add_assoc, CharTwo.add_self_eq_zero]
  rw [commutatorElement_def, he]
  simp [mul_assoc]

/-- Every central element is a single commutator. -/
theorem center_radical_exists_commutator (hnt : ∃ u, σ u ≠ u)
    (a : R) (ha : a ∈ Subgroup.center R) : ∃ b c : R, ⁅b,c⁆ = a := by
  let t := (centerEquivFixedField F σ hσ hnt ⟨a,ha⟩).toAdd
  obtain ⟨b,hb⟩ := exists_trace_eq F σ hσ hnt t
  refine ⟨rootX F σ hσ 1, rootY F σ hσ b, ?_⟩
  rw [root_commutator]
  have ht : traceFixed F σ hσ b = t := Subtype.ext hb
  rw [ht]
  exact congrArg Subtype.val ((centerEquivFixedField F σ hσ hnt).left_inv ⟨a,ha⟩)

/-- The derived group equals the center for a nontrivial involution. -/
theorem commutator_radical_eq_center (hnt : ∃ u, σ u ≠ u) :
    commutator R = Subgroup.center R := by
  apply le_antisymm (commutator_radical_le_center F σ hσ)
  intro a ha
  obtain ⟨b,c,rfl⟩ := center_radical_exists_commutator F σ hσ hnt a ha
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top b) (Subgroup.mem_top c)

/-- Squares are central, including before any finiteness assumption. -/
theorem radical_square_mem_center (a : R) : a ^ 2 ∈ Subgroup.center R := by
  rw [pow_two]
  apply mem_center_of_xy_zero F σ hσ
  · rw [(coord_mul F σ hσ _ _).1, CharTwo.add_self_eq_zero]
  · rw [(coord_mul F σ hσ _ _).2.1, CharTwo.add_self_eq_zero]

/-- For a finite two-group radical, its Frattini subgroup is its center. -/
theorem frattini_radical_eq_center [Finite R] (hnt : ∃ u, σ u ≠ u)
    (hR : IsPGroup 2 R) : frattini R = Subgroup.center R := by
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  apply le_antisymm
  · rw [hR.frattini_eq_closure_squares]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a,rfl⟩
    exact radical_square_mem_center F σ hσ a
  · rw [← commutator_radical_eq_center F σ hσ hnt]
    exact commutator_le_frattini_of_isPGroup (p := 2)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
