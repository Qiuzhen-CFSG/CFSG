module

public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.NaturalModel
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# Selecting an involution in a conjugate of the relative centralizer

In the split natural block, `U` is the actual two-core of the point
parabolic and `V2` is the translation plane v₂ = 0. We use the source
convention `W^g = g⁻¹ W g`, with `W = C_U(V2)`.

The root involution I + E₀₂ belongs to W. For every g in the line parabolic
outside the point parabolic, its conjugate belongs to the compatible flag
Sylow subgroup and has nonzero (1,2)-entry, hence lies outside U. Moreover
the whole W^g lies in that Sylow subgroup. This avoids an assumption that
W^g is elementary or that every element outside U is an involution.

`CoreCoordinates` is the explicit identification of the actual two-core
with the point radical. The flagged-model assembly must supply it, and
must identify the source P − H with the displayed parabolic difference.
No full ambient source theorem is asserted from the split model alone.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 12.8.9,
printed pp.852–853, and proof of 14.4.4, printed p.1007.
-/

@[expose] public section

open Matrix Subgroup
namespace Matrix.PSL3Two.SplitParabolic.OutsideSelection

def U : Subgroup Block := pointPreimage.pCoreIn 2
/-- Coordinate identification to be supplied by the flagged Sylow construction. -/
def CoreCoordinates : Prop := ∀ x : Block,
  x ∈ U ↔ x ∈ standardSylow ∧ x.right.val 1 2 = 0

def planeMap : Multiplicative (Fin 2 → ZMod 2) →* Block where
  toFun v := SemidirectProduct.inl (Multiplicative.ofAdd ![v.toAdd 0,v.toAdd 1,0])
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i; fin_cases i <;> rfl
    · rfl
  map_mul' v w := by
    rw [← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    funext i; fin_cases i <;> simp

def V2 : Subgroup Block := planeMap.range

theorem mem_V2_iff (x : Block) : x ∈ V2 ↔ x.right = 1 ∧ x.left.toAdd 2 = 0 := by
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨rfl,rfl⟩
  · rintro ⟨hr,hl⟩
    refine ⟨Multiplicative.ofAdd ![x.left.toAdd 0,x.left.toAdd 1], ?_⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · rfl
      · rfl
      · exact hl.symm
    · exact hr.symm

def W : Subgroup Block := U ⊓ centralizer (V2 : Set Block)
def X (g : Block) : Subgroup Block := W.map (MulAut.conj g⁻¹).toMonoidHom

def root : SL := ⟨!![1,0,1;0,1,0;0,0,1], by decide⟩
def rootLift : Block := SemidirectProduct.inr root

theorem root_square : rootLift ^ 2 = 1 := by
  change (SemidirectProduct.inr root : Block)^2 = 1
  rw [← map_pow]
  have h : root ^ 2 = 1 := by apply Subtype.ext; decide +kernel
  rw [h, map_one]

theorem root_mem_W (hc : CoreCoordinates) : rootLift ∈ W := by
  constructor
  · apply (hc _).mpr
    exact ⟨(mem_borelSL_iff _).mpr ⟨rfl,rfl,rfl⟩,rfl⟩
  · rintro y ⟨v,rfl⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      revert v i
      decide +kernel
    · change (planeMap v).right * root = root * (planeMap v).right
      change 1 * root = root * 1
      simp

theorem W_right (hc : CoreCoordinates) (x : Block) (hx : x ∈ W) :
    x.right = 1 ∨ x.right = root := by
  have hb : x.right ∈ borelSL := ((hc x).mp hx.1).1
  have h12 := ((hc x).mp hx.1).2
  have he := hx.2 (planeMap (Multiplicative.ofAdd ![0,1])) ⟨_,rfl⟩
  have h01 : x.right.val 0 1 = 0 := by
    have hh := congrArg (fun y : Block => y.left.toAdd 0) he
    simp only [planeMap, MonoidHom.coe_mk, OneHom.coe_mk,
      SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply] at hh
    change 0 + x.left.toAdd 0 = x.left.toAdd 0 +
      (x.right.val.mulVec ![0,1,0]) 0 at hh
    simpa [mulVec, dotProduct, Fin.sum_univ_three] using hh.symm
  exact (by decide +kernel : ∀ m : SL, m ∈ borelSL → m.val 1 2 = 0 →
    m.val 0 1 = 0 → m = 1 ∨ m = root) x.right hb h12 h01

theorem root_conjugate_linear : ∀ m : SL, m ∈ lineParabolicSL →
    m⁻¹ * root * m ∈ borelSL ∧
    (m ∉ pointParabolicSL → (m⁻¹ * root * m).val 1 2 ≠ 0) := by
  decide +kernel

/-- Source convention: conjugation on the right, `w ↦ g⁻¹ * w * g`. -/
def selected (g : Block) : Block := MulAut.conj g⁻¹ rootLift

theorem selected_eq (g : Block) : selected g = g⁻¹ * rootLift * g := by
  simp only [selected, MulAut.conj_apply, inv_inv]

theorem selected_mem (hc : CoreCoordinates) (g : Block) : selected g ∈ X g :=
  mem_map_of_mem _ (root_mem_W hc)

theorem selected_square (g : Block) : selected g ^ 2 = 1 := by
  rw [selected, ← map_pow, root_square, map_one]

theorem conjugate_le_sylow (hc : CoreCoordinates) (g : Block)
    (hg : g ∈ linePreimage) : X g ≤ standardSylow := by
  rintro y ⟨w,hw,rfl⟩
  change (g⁻¹ * w * (g⁻¹)⁻¹).right ∈ borelSL
  simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right, inv_inv]
  rcases W_right hc w hw with hw | hw
  · rw [hw, mul_one, inv_mul_cancel]
    exact borelSL.one_mem
  · rw [hw]
    exact (root_conjugate_linear g.right hg).1

theorem selected_not_mem (hc : CoreCoordinates) (g : Block)
    (hg : g ∈ linePreimage) (hp : g ∉ pointPreimage) : selected g ∉ U := by
  intro hu
  have hh := ((hc _).mp hu).2
  rw [selected_eq] at hh
  exact (root_conjugate_linear g.right hg).2 hp hh

/-- An actual involution of the actual conjugate centralizer outside the
first-parabolic core. No exponent condition on all of `X g` is used. -/
theorem exists_outside_involution (hc : CoreCoordinates) (g : Block)
    (hg : g ∈ linePreimage) (hp : g ∉ pointPreimage) :
    ∃ x : Block, x ∈ X g ∧ x ∉ U ∧ x ≠ 1 ∧ x^2=1 ∧ x ∈ standardSylow := by
  refine ⟨selected g, selected_mem hc g, selected_not_mem hc g hg hp, ?_,
    selected_square g, conjugate_le_sylow hc g hg (selected_mem hc g)⟩
  intro he
  exact selected_not_mem hc g hg hp (he ▸ U.one_mem)

end Matrix.PSL3Two.SplitParabolic.OutsideSelection
