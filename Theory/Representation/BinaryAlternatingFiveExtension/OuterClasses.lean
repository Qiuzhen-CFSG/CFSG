module
public import Theory.Representation.BinaryAlternatingFiveExtension.SylowGraphCenter
public import Theory.Representation.BinaryAlternatingFiveExtension.IndexTwo

/-!
# Outer involution classes in the binary affine plane

The odd involutions of a Sylow in the affine symmetric-five group have two
classes in the whole affine group. In wreath coordinates, the exact cyclic
commutator and centralizer order32 identify the marked graph involution up
to multiplication by the central root. A small finite calculation places
all odd involutions in those two classes, using Sylow elements and two
additional coordinate swaps as explicit affine conjugators.

This is the outer-coset part of Aschbacher--Smith F.4.37, printed p.293.
The source consumer preserves the endpoint containing each conjugator.
-/

@[expose] public section
namespace BinaryPermutation.AlternatingFiveExtension.OuterClasses
open SylowModel SylowCommutator Subgroup
private instance : Fintype V4 := inferInstance
private instance : DecidableEq V4 := inferInstance
private instance : Fintype PlaneWreath := Fintype.ofEquiv _ (RegularWreathProduct.equivProd PlaneGroup Bit).symm
private instance : DecidableEq PlaneWreath := (RegularWreathProduct.equivProd PlaneGroup Bit).injective.decidableEq
private instance : DecidableEq Model := SemidirectProduct.equivProd.injective.decidableEq

private def graph : PlaneWreath := ⟨fun k => if k = 1 then reflection else 1, 1⟩
private def root : PlaneWreath := baseMap (axis 1) * baseMap (axis (.ofAdd 1))
private def odd (x : PlaneWreath) : Prop := (x.left 1).right ≠ (x.left (.ofAdd 1)).right
private instance (x : PlaneWreath) : Decidable (odd x) := inferInstanceAs (Decidable (_ ≠ _))
private def extra (n : Fin 3) : Model := SemidirectProduct.inr
  (if n=0 then 1 else if n=1 then Equiv.swap 2 4 else Equiv.swap 3 4)

private theorem small_test : ∀ x : PlaneWreath, x*x=1 → odd x →
    ∃ (y : PlaneWreath) (n : Fin 3),
      let g := embedding y * extra n
      g * embedding graph * g⁻¹ = embedding x ∨
      g * embedding (graph*root) * g⁻¹ = embedding x := by decide +kernel

private theorem graph_pair_test : ∀ (f : PlaneWreath) (j : Bit),
    f*f=1 →
    (∃ v : V4, displacement (actorProjection f) v ≠ 1) →
    (∀ v : V4, displacement (actorProjection f) v = 1 ∨
      displacement (actorProjection f) v = axis j) →
    (Finset.univ.filter (fun y : PlaneWreath => y*f=f*y)).card = 32 →
    ∃ y : PlaneWreath,
      (y*f*y⁻¹=graph ∧ y*(f*root)*y⁻¹=graph*root) ∨
      (y*f*y⁻¹=graph*root ∧ y*(f*root)*y⁻¹=graph) := by decide +kernel

private theorem odd_iff : ∀ x : PlaneWreath,
    odd x ↔ Equiv.Perm.sign (embedding x).right ≠ 1 := by decide +kernel

private theorem root_test : ∀ z : PlaneWreath,
    (∀ y : PlaneWreath, z*y=y*z) → z ≠ 1 → z=root := by decide +kernel


private theorem commutant_card (f : PlaneWreath) :
    Nat.card (centralizer ({f} : Set PlaneWreath)) =
      (Finset.univ.filter (fun x : PlaneWreath => x*f=f*x)).card := by
  let e : centralizer ({f} : Set PlaneWreath) ≃ {x : PlaneWreath // x*f=f*x} := {
    toFun x := ⟨x.val,mem_centralizer_singleton_iff.mp x.property⟩
    invFun x := ⟨x.val,mem_centralizer_singleton_iff.mpr x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]

open scoped commutatorElement
/-- The odd involutions in the coordinate Sylow have two classes under the full affine endpoint. -/
theorem outer_classes (f z : PlaneWreath) (u : V4)
    (hf : orderOf f=2) (hu : orderOf (baseMap u)=2)
    (hc : ⁅baseMap.range,zpowers f⁆=zpowers (baseMap u))
    (hcard : Nat.card (centralizer ({f} : Set PlaneWreath))=32)
    (hz : z∈center PlaneWreath) (hz1 : z≠1)
    (x : PlaneWreath) (hx : x*x=1)
    (hxodd : (embedding x).right ∉ alternatingGroup (Fin 5)) :
    IsConj (embedding f) (embedding x) ∨ IsConj (embedding (f*z)) (embedding x) := by
  have hzr : z=root := root_test z (fun y => (mem_center_iff.mp hz y).symm) hz1
  rw [hzr]
  obtain ⟨haxis,hmove,hdisp⟩ := SylowGraphCenter.displacement_of_cyclic_base_commutator f u hu hc
  have hfp : f*f=1 := by simpa [hf,pow_two] using pow_orderOf_eq_one f
  have hfc := (commutant_card f).symm.trans hcard
  have hpair : ∃ y : PlaneWreath,
      (y*f*y⁻¹=graph ∧ y*(f*root)*y⁻¹=graph*root) ∨
      (y*f*y⁻¹=graph*root ∧ y*(f*root)*y⁻¹=graph) := by
    rcases haxis with rfl | rfl
    all_goals exact graph_pair_test f _ hfp hmove hdisp hfc
  have hodd : odd x := (odd_iff x).mpr (by
    simpa only [Equiv.Perm.mem_alternatingGroup] using hxodd)
  obtain ⟨a,n,ha⟩ := small_test x hx hodd
  obtain ⟨b,hb|hb⟩ := hpair
  all_goals
    have hb1 := embedding.map_isConj (isConj_iff.mpr ⟨b,hb.1⟩)
    have hb2 := embedding.map_isConj (isConj_iff.mpr ⟨b,hb.2⟩)
  · rcases ha with ha | ha
    · exact Or.inl (hb1.trans (isConj_iff.mpr ⟨_,ha⟩))
    · exact Or.inr (hb2.trans (isConj_iff.mpr ⟨_,ha⟩))
  · rcases ha with ha | ha
    · exact Or.inr (hb2.trans (isConj_iff.mpr ⟨_,ha⟩))
    · exact Or.inl (hb1.trans (isConj_iff.mpr ⟨_,ha⟩))

end BinaryPermutation.AlternatingFiveExtension.OuterClasses
