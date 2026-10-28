module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.TransvectionCommutator
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.LargeQuadratic

/-!
# Refinements on subgroups normalized by the full Sylow

A normal subgroup of the standard unipotent group preserving a quadratic
refinement lies in the plane wing. For an element with first parameter b,
normality supplies the central commutators theta(b²a,ba), for every a.
Refinement preservation would make every field element idempotent if b
were nonzero. The orthogonal plane bound then bounds the subgroup by 2q.

Consequently a normal subgroup of order at least q² has no invariant
refinement, independently of any comparison with another natural marking.
This supplies the marking-independent obstruction needed in MS93 (5.12)(2),
printed p.926, with the original full-Sylow normalization retained.
-/

public noncomputable section
open Subgroup Matrix
open scoped commutatorElement
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem theta_refinement_equation (c : Vector F) (s t : F)
    (hc : ∀ x, refinement c ((theta s t).val • x)=refinement c x) :
    s=c (.inl 0)*s^2+c (.inl 1)*t^2 := by
  have hh := hc (Pi.single (.inr 0) 1)
  change refinement c ((theta s t).val.val *ᵥ Pi.single (.inr 0) 1)=_ at hh
  rw [refinement_apply,refinement_apply,theta,element_matrix] at hh
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.fromBlocks, Pi.single_apply] at hh
  norm_num at hh
  simp only [Sum.inl_ne_inr, ↓reduceIte, zero_add] at hh
  have hz : s+(c (.inl 0)*s^2+c (.inl 1)*t^2)=0 :=
    add_right_cancel (by simpa only [add_assoc,zero_add] using hh)
  exact CharTwo.add_eq_zero.mp hz

omit [Finite F] [CharP F 2] in
private theorem field_card_le_two_of_idempotent
    (h : ∀ a : F, a^2=a) : Nat.card F ≤ 2 := by
  classical
  let f : F → Bool := fun a => decide (a≠0)
  have hf : Function.Injective f := by
    intro a b he
    rcases eq_zero_or_one_of_sq_eq_self (h a) with rfl | rfl <;>
      rcases eq_zero_or_one_of_sq_eq_self (h b) with rfl | rfl
    · rfl
    · simp [f] at he
    · simp [f] at he
    · rfl
  simpa using Nat.card_le_card_of_injective f hf

private theorem normal_refinement_le_plane (hq : 2 < Nat.card F)
    (T : Subgroup (unipotent (F := F))) [T.Normal]
    (c : Vector F) (hc : ∀ g : T, ∀ x, refinement c (g.val.val • x)=refinement c x) :
    T ≤ wing true := by
  intro g hg
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
  apply (element_mem_wing true b u w v).mpr
  change b=0
  by_contra hb
  have heq (a : F) : b^2*a=(c (.inl 0)*b^4+c (.inl 1)*b^2)*a^2 := by
    have hm : theta (b^2*a) (b*a) ∈ T := by
      have hm := commutator_le_left T ⊤ (commutator_mem_commutator hg
        (mem_top (element 0 0 0 a)))
      simpa only [element_commutator,zero_pow (by decide : (2:ℕ)≠0),zero_mul,zero_add] using hm
    have hh := theta_refinement_equation c (b^2*a) (b*a) (hc ⟨_,hm⟩)
    calc
      b^2*a = c (.inl 0)*(b^2*a)^2+c (.inl 1)*(b*a)^2 := hh
      _ = (c (.inl 0)*b^4+c (.inl 1)*b^2)*a^2 := by ring
  have hcoeff : b^2=c (.inl 0)*b^4+c (.inl 1)*b^2 := by simpa using heq 1
  have hidem (a : F) : a^2=a := by
    have hh := heq a
    rw [←hcoeff] at hh
    exact (mul_left_cancel₀ (pow_ne_zero 2 hb) hh).symm
  exact hq.not_ge (field_card_le_two_of_idempotent hidem)

/-- A subgroup normal in the full symplectic Sylow and preserving a
quadratic refinement has order at most twice the field order. -/
theorem normal_refinement_card_le (hq : 2 < Nat.card F)
    (T : Subgroup (unipotent (F := F))) [T.Normal]
    (c : Vector F) (hc : ∀ g : T, ∀ x, refinement c (g.val.val • x)=refinement c x) :
    Nat.card T ≤ 2*Nat.card F := by
  have hplane := normal_refinement_le_plane hq T c hc
  let A := T.map unipotent.subtype
  have hcard : Nat.card A=Nat.card T := card_map_of_injective unipotent.subtype_injective
  rw [←hcard]
  apply card_le_of_fixes_standard_plane A ?_ c ?_
  · rintro ⟨g,⟨g,hg,rfl⟩⟩ x hx
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
    have hb : b=0 := (element_mem_wing true _ _ _ _).mp (hplane hg)
    subst b
    have hx0 : ∀ i, x (.inr i)=0 := hx
    change (element 0 u w v).val.val *ᵥ x=x
    rw [element_matrix]
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [Matrix.mulVec,dotProduct,Matrix.fromBlocks,Fintype.sum_sum_type,Fin.sum_univ_two,hx0]
  · rintro ⟨g,⟨g,hg,rfl⟩⟩ x
    exact hc ⟨g,hg⟩ x

/-- A large normal subgroup of the full symplectic Sylow has no invariant
quadratic refinement in the supplied natural coordinates. -/
theorem normal_no_refinement (hq : 2 < Nat.card F)
    (T : Subgroup (unipotent (F := F))) [T.Normal]
    (hlarge : Nat.card F^2 ≤ Nat.card T) :
    ¬ ∃ c : Vector F, ∀ g : T, ∀ x, refinement c (g.val.val • x)=refinement c x := by
  rintro ⟨c,hc⟩
  have hh := normal_refinement_card_le hq T c hc
  nlinarith

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
