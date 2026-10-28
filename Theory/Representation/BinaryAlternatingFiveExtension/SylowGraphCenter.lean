module
public import Theory.Representation.BinaryAlternatingFiveExtension.SylowCommutator.Transport
/-!
# The center of a marked graph centralizer in the binary affine Sylow

Write the Sylow subgroup of the binary affine symmetric-five group as
`D₈ wr C₂`, with its elementary sixteen-group marked. A nontrivial cyclic
commutator with an involution selects one factor-center line. If the
involution centralizer has order32, the involution is a reflection in that
factor times central elements. Its centralizer center is contained in the
eight products of the involution, the selected line and the whole-group
central involution. The factor swap conjugates the selected line onto its
product with the whole-group center.

The small coordinate checks test only the model generators and commute
predicates. The marking and cyclic-commutator deductions are structural.
Source: Aschbacher--Smith, F.4.37, printed p.293.
-/

@[expose] public section
namespace BinaryPermutation.AlternatingFiveExtension.SylowGraphCenter
open Subgroup SylowModel SylowCommutator
open scoped commutatorElement
private instance : Fintype V4 := inferInstance
private instance : DecidableEq V4 := inferInstance
private instance : Fintype PlaneWreath := Fintype.ofEquiv _ (RegularWreathProduct.equivProd PlaneGroup Bit).symm
private instance : DecidableEq PlaneWreath := (RegularWreathProduct.equivProd PlaneGroup Bit).injective.decidableEq
private instance : Fintype Actor := Fintype.ofEquiv _ (RegularWreathProduct.equivProd Bit Bit).symm
private instance : DecidableEq Actor := (RegularWreathProduct.equivProd Bit Bit).injective.decidableEq

private def root : PlaneWreath := baseMap (axis 1) * baseMap (axis (.ofAdd 1))
private def swap : PlaneWreath := ⟨1, .ofAdd 1⟩

private theorem swap_axis : ∀ j : Bit,
    swap * baseMap (axis j) * swap⁻¹ = baseMap (axis j) * root := by decide +kernel

private theorem center_test : ∀ x : PlaneWreath,
    (∀ y : PlaneWreath, x * y = y * x) → x = 1 ∨ x = root := by decide +kernel

private def graph (j : Bit) : PlaneWreath := ⟨fun k => if k = j then reflection else 1, 1⟩
private def otherRotation (j : Bit) : PlaneWreath := ⟨fun k => if k = j then 1 else rotation, 1⟩
private def otherReflection (j : Bit) : PlaneWreath := ⟨fun k => if k = j then 1 else reflection, 1⟩

private def graphForm (j : Bit) (f : PlaneWreath) : Prop :=
  f = graph j ∨ f = graph j * baseMap (axis j) ∨
  f = graph j * root ∨ f = graph j * baseMap (axis j) * root
private instance (j : Bit) (f : PlaneWreath) : Decidable (graphForm j f) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

private theorem graph_form_test : ∀ (f : PlaneWreath) (j : Bit),
    f * f = 1 →
    (∃ v : V4, displacement (actorProjection f) v ≠ 1) →
    (∀ v : V4, displacement (actorProjection f) v = 1 ∨
      displacement (actorProjection f) v = axis j) →
    (Finset.univ.filter (fun x : PlaneWreath => x * f = f * x)).card = 32 →
    graphForm j f := by decide +kernel

private theorem other_generators_commute : ∀ (j : Bit) (f : PlaneWreath), graphForm j f →
    otherRotation j * f = f * otherRotation j ∧
    otherReflection j * f = f * otherReflection j := by decide +kernel

private theorem center_generators_test : ∀ (j : Bit) (f x : PlaneWreath), graphForm j f →
    x * f = f * x →
    x * otherRotation j = otherRotation j * x →
    x * otherReflection j = otherReflection j * x →
    x = 1 ∨ x = root ∨ x = baseMap (axis j) ∨ x = baseMap (axis j) * root ∨
    x = f ∨ x = f * baseMap (axis j) ∨ x = f * root ∨ x = f * baseMap (axis j) * root := by
  decide +kernel

theorem displacement_of_cyclic_base_commutator (f : PlaneWreath) (u : V4)
    (hu : orderOf (baseMap u) = 2)
    (hc : ⁅baseMap.range,zpowers f⁆ = zpowers (baseMap u)) :
    (u = axis 1 ∨ u = axis (.ofAdd 1)) ∧
      (∃ v : V4, displacement (actorProjection f) v ≠ 1) ∧
      ∀ v : V4, displacement (actorProjection f) v = 1 ∨
        displacement (actorProjection f) v = u := by
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
  exact ⟨displacement_axis (actorProjection f) u hmove hcases,hmove,hcases⟩

private theorem commutant_card (f : PlaneWreath) :
    Nat.card (centralizer ({f} : Set PlaneWreath)) =
      (Finset.univ.filter (fun x : PlaneWreath => x * f = f * x)).card := by
  let e : centralizer ({f} : Set PlaneWreath) ≃ {x : PlaneWreath // x * f = f * x} := {
    toFun x := ⟨x.val,mem_centralizer_singleton_iff.mp x.property⟩
    invFun x := ⟨x.val,mem_centralizer_singleton_iff.mpr x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]

/-- In the marked cyclic-displacement situation, the center of the graph
centralizer consists of the eight products of the graph, short and central
involutions. Only the inclusion needed by the fusion argument is asserted. -/
theorem center_centralizer_cases (f z : PlaneWreath) (u : V4)
    (hf : orderOf f = 2) (hu : orderOf (baseMap u) = 2)
    (hc : ⁅baseMap.range,zpowers f⁆ = zpowers (baseMap u))
    (hcard : Nat.card (centralizer ({f} : Set PlaneWreath)) = 32)
    (hz : z ∈ center PlaneWreath) (hz1 : z ≠ 1)
    (x : PlaneWreath) (hx : ∀ y : PlaneWreath, y * f = f * y → x * y = y * x) :
    x = 1 ∨ x = z ∨ x = baseMap u ∨ x = baseMap u * z ∨
    x = f ∨ x = f * baseMap u ∨ x = f * z ∨ x = f * baseMap u * z := by
  have hzroot : z = root := (center_test z (fun y => (mem_center_iff.mp hz y).symm)).resolve_left hz1
  rw [hzroot]
  obtain ⟨haxis,hmove,hdisp⟩ := displacement_of_cyclic_base_commutator f u hu hc
  have hf2 : f * f = 1 := by simpa [hf,pow_two] using pow_orderOf_eq_one f
  have hcount := (commutant_card f).symm.trans hcard
  rcases haxis with rfl | rfl
  all_goals
    have hform := graph_form_test f _ hf2 hmove hdisp hcount
    have hgen := other_generators_commute _ f hform
    exact center_generators_test _ f x hform (hx f rfl) (hx _ hgen.1) (hx _ hgen.2)

/-- The actual whole-Sylow factor swap conjugates the marked short involution
onto its product with the unique nontrivial central involution. -/
theorem exists_conjugator_short_root (f z : PlaneWreath) (u : V4)
    (hu : orderOf (baseMap u) = 2)
    (hc : ⁅baseMap.range,zpowers f⁆ = zpowers (baseMap u))
    (hz : z ∈ center PlaneWreath) (hz1 : z ≠ 1) :
    ∃ y : PlaneWreath, y * baseMap u * y⁻¹ = baseMap u * z := by
  have hzroot : z = root := (center_test z (fun y => (mem_center_iff.mp hz y).symm)).resolve_left hz1
  rw [hzroot]
  obtain ⟨haxis,_⟩ := displacement_of_cyclic_base_commutator f u hu hc
  rcases haxis with rfl | rfl
  all_goals exact ⟨swap,swap_axis _⟩

end BinaryPermutation.AlternatingFiveExtension.SylowGraphCenter
