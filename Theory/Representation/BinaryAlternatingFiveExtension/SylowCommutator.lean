module
public import Theory.Representation.BinaryAlternatingFiveExtension.SylowModel
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# A cyclic displacement line in the binary symmetric-five Sylow

In the coordinate Sylow `(E₄:C₂) wr C₂`, an actor with a nonzero
one-dimensional displacement on the natural elementary sixteen-group flips
exactly one pair of letters. Its displacement line is the center of that
one dihedral factor. The centralizer of its nonidentity element is therefore
the full base `D₈ × D₈`.

Only the eight-element actor and sixteen-element module are enumerated for
the displacement test. The centralizer test uses the order-128 Sylow; the
remaining transport and commutator proofs are structural.

This supplies the local short-root centralizer in Aschbacher--Smith F.4.37
and F.5.3, printed pp.293 and 300--301.
-/

@[expose] public section
namespace BinaryPermutation.AlternatingFiveExtension.SylowCommutator
open Subgroup SylowModel
open scoped commutatorElement
abbrev V4 := Bit → Plane
private instance : Fintype V4 := inferInstance
private instance : DecidableEq V4 := inferInstance
private instance : Fintype Actor := Fintype.ofEquiv _ (RegularWreathProduct.equivProd Bit Bit).symm
private instance : DecidableEq Actor := (RegularWreathProduct.equivProd Bit Bit).injective.decidableEq
private instance : Fintype PlaneWreath := Fintype.ofEquiv _ (RegularWreathProduct.equivProd PlaneGroup Bit).symm
private instance : DecidableEq PlaneWreath := (RegularWreathProduct.equivProd PlaneGroup Bit).injective.decidableEq

def baseMap : V4 →* PlaneWreath where
  toFun v := ⟨fun i => SemidirectProduct.inl (v i), 1⟩
  map_one' := rfl
  map_mul' v w := by
    apply RegularWreathProduct.ext
    · funext i
      simp
    · rfl

theorem baseMap_injective : Function.Injective baseMap := by
  intro v w h
  funext i
  exact congrArg (fun x : PlaneWreath => (x.left i).left) h

def displacement (a : Actor) (v : V4) : V4 :=
  fun i => v i * (planeAction (a.left i) (v (a.right⁻¹ * i)))⁻¹

def axis (j : Bit) : V4 := fun i => if i = j then (.ofAdd 1, .ofAdd 1) else 1

theorem displacement_axis : ∀ (a : Actor) (u : V4),
    (∃ v : V4, displacement a v ≠ 1) →
    (∀ v : V4, displacement a v = 1 ∨ displacement a v = u) →
    u = axis 1 ∨ u = axis (.ofAdd 1) := by decide +kernel

@[simp] theorem baseMap_left (v : V4) (i : Bit) :
    (baseMap v).left i = SemidirectProduct.inl (v i) := rfl
@[simp] theorem baseMap_right (v : V4) : (baseMap v).right = 1 := rfl

-- Conjugation on the base depends only on the actor projection.
theorem base_commutator (f : PlaneWreath) (v : V4) :
    ⁅baseMap v,f⁆ = baseMap (displacement (actorProjection f) v) := by
  apply RegularWreathProduct.ext
  · funext i
    simp only [commutatorElement_def, RegularWreathProduct.mul_left,
      RegularWreathProduct.mul_right, RegularWreathProduct.inv_left, RegularWreathProduct.inv_right,
      baseMap_left, baseMap_right, Pi.mul_apply, Pi.inv_apply, inv_one,
      one_mul, mul_one, mul_inv_cancel_left]
    apply SemidirectProduct.ext
    · simp [displacement, actorProjection, mul_assoc, mul_comm]
    · simp
  · simp [commutatorElement_def]

theorem centralizer_axis_test : ∀ (j : Bit) (x : PlaneWreath),
    x * baseMap (axis j) = baseMap (axis j) * x ↔ x.right = 1 := by decide +kernel


noncomputable def centralizerAxisEquiv (j : Bit) :
    centralizer ({baseMap (axis j)} : Set PlaneWreath) ≃* PlaneGroup × PlaneGroup where
  toFun x := (x.val.left 1,x.val.left (.ofAdd 1))
  invFun a := ⟨⟨fun i => if i = 1 then a.1 else a.2,1⟩,
    mem_centralizer_singleton_iff.mpr ((centralizer_axis_test j _).mpr rfl)⟩
  left_inv x := by
    apply Subtype.ext
    apply RegularWreathProduct.ext
    · funext i
      have hi : i = 1 ∨ i = Multiplicative.ofAdd 1 := by
        exact (by decide : ∀ i : Bit, i=1 ∨ i=Multiplicative.ofAdd 1) i
      rcases hi with rfl | rfl
      · simp
      · simp [show (Multiplicative.ofAdd 1 : Bit) ≠ 1 by decide]
    · exact ((centralizer_axis_test j _).mp (mem_centralizer_singleton_iff.mp x.property)).symm
  right_inv a := by
    simp [show (Multiplicative.ofAdd 1 : Bit) ≠ 1 by decide]
  map_mul' x y := by
    have hx := (centralizer_axis_test j _).mp (mem_centralizer_singleton_iff.mp x.property)
    apply Prod.ext <;> simp [hx]

theorem centralizer_of_cyclic_base_commutator (f : PlaneWreath) (u : V4)
    (hu : orderOf (baseMap u) = 2)
    (hc : ⁅baseMap.range,zpowers f⁆ = zpowers (baseMap u)) :
    Nonempty (centralizer ({baseMap u} : Set PlaneWreath) ≃*
      DihedralGroup 4 × DihedralGroup 4) := by
  have hcases (v : V4) : displacement (actorProjection f) v = 1 ∨
      displacement (actorProjection f) v = u := by
    have hh := commutator_mem_commutator (show baseMap v ∈ baseMap.range from ⟨v,rfl⟩)
      (mem_zpowers f)
    rw [hc,base_commutator,mem_zpowers_iff_mem_range_orderOf,hu] at hh
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hh
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · left
      apply baseMap_injective
      simpa using he.symm
    · right
      apply baseMap_injective
      simpa using he.symm
  have hmove : ∃ v : V4, displacement (actorProjection f) v ≠ 1 := by
    by_contra hh
    push Not at hh
    have hf : f ∈ centralizer (baseMap.range : Set PlaneWreath) := by
      rintro x ⟨v,rfl⟩
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [base_commutator,hh v,map_one]
    have hbot : ⁅baseMap.range,zpowers f⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr hf)
    have hu1 := mem_zpowers (baseMap u)
    rw [←hc,hbot,mem_bot] at hu1
    rw [hu1,orderOf_one] at hu
    omega
  obtain he | he := displacement_axis (actorProjection f) u hmove hcases
  all_goals
    rw [he]
    obtain ⟨d⟩ := plane_dihedral
    exact ⟨(centralizerAxisEquiv _).trans (MulEquiv.prodCongr d d)⟩

end BinaryPermutation.AlternatingFiveExtension.SylowCommutator
