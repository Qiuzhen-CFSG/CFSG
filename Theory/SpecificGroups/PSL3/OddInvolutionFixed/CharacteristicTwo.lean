module

public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Theory.SpecificGroups.GL2.CubicCentralQuotientComponent
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# The SL₂ component in an odd PSL₃ involution centralizer

The canonical projection on the full involution centralizer has central kernel
of exponent three. Transporting along the actual GL₂ block isomorphism and
restricting to its determinant kernel constructs a normal SL₂ component.
Consequently, when the field has more than three elements, the centralizer's
two-core cannot be self-centralizing. The final theorem applies this to the
full fixed subgroup of an inner involution of a simple perfect PSL₃ model.

Source: Aschbacher--Smith A.3.21(a), printed p.55, and the odd-characteristic
paragraph of the proof of 1.1.5(3), printed p.503 (PDF p.520).
-/

public section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3.OddInvolutionFixed
variable {F : Type*} [Field F] [Finite F]

omit [Finite F] in
/-- The restriction of the canonical quotient map retains a central kernel. -/
theorem centralizerProjection_ker_le_center (t : SL(3,F)) :
    (centralizerProjection t).ker ≤ center (centralizer ({t} : Set SL(3,F))) := by
  intro x hx
  have hz : (x : SL(3,F)) ∈ center SL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hz y)

/-- Every element of the actual centralizer projection kernel has cube one. -/
theorem centralizerProjection_ker_cube (t : SL(3,F))
    (x : centralizer ({t} : Set SL(3,F))) (hx : x ∈ (centralizerProjection t).ker) :
    x ^ 3 = 1 := by
  have hz : (x : SL(3,F)) ∈ center SL(3,F) := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  have hd := (orderOf_dvd_natCard (⟨x.val, hz⟩ : center SL(3,F))).trans
    (SL3.card_center_dvd_three F)
  apply Subtype.ext
  exact congrArg (fun w : center SL(3,F) => (w : SL(3,F)))
    (orderOf_dvd_iff_pow_eq_one.mp hd)

/-- The full projective centralizer is a cubic central quotient of GL₂. -/
theorem exists_gl2_cubic_central_surjection (t : PSL(3,F)) (ht : orderOf t = 2)
    (h2 : (2 : F) ≠ 0) :
    ∃ f : GL (Fin 2) F →* centralizer ({t} : Set PSL(3,F)),
      Function.Surjective f ∧ f.ker ≤ center (GL (Fin 2) F) ∧
        ∀ g ∈ f.ker, g ^ 3 = 1 := by
  obtain ⟨x, hx, rfl⟩ := involution_lift t ht
  let e := SL3.involutionCentralizerEquiv F x hx h2
  let f := (centralizerProjection x).comp e.symm.toMonoidHom
  refine ⟨f, (centralizerProjection_surjective x (hx ▸ pow_orderOf_eq_one x)).comp
    e.symm.surjective, ?_, ?_⟩
  · intro g hg
    have hc : e.symm g ∈ center (centralizer ({x} : Set SL(3,F))) :=
      centralizerProjection_ker_le_center x hg
    apply mem_center_iff.mpr
    intro y
    apply e.symm.injective
    simpa only [map_mul] using mem_center_iff.mp hc (e.symm y)
  · intro g hg
    apply e.symm.injective
    simpa only [map_pow, map_one] using centralizerProjection_ker_cube x (e.symm g) hg

/-- The full centralizer contains a normal component isomorphic to SL₂(F). -/
theorem exists_sl2_component_in_involution_centralizer
    (hlarge : 3 < Nat.card F) (h2 : (2 : F) ≠ 0)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    ∃ K : Subgroup (centralizer ({t} : Set PSL(3,F))),
      K.Normal ∧ IsComponent (centralizer ({t} : Set PSL(3,F))) K ∧
        Nonempty (K ≃* SL(2,F)) := by
  obtain ⟨f, hf, hk, hcube⟩ := exists_gl2_cubic_central_surjection t ht h2
  exact GeneralLinearGroup.exists_sl2_component_of_cubic_central_surjection hlarge f hf hk hcube

/-- The SL₂ component obstructs a self-centralizing two-core in the full
projective involution centralizer. -/
theorem inner_centralizer_not_selfCentralizing_twoCore
    (hlarge : 3 < Nat.card F) (h2 : (2 : F) ≠ 0)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    ¬ centralizer (pCore 2 (centralizer ({t} : Set PSL(3,F))) :
        Set (centralizer ({t} : Set PSL(3,F)))) ≤
      pCore 2 (centralizer ({t} : Set PSL(3,F))) := by
  intro hchar
  obtain ⟨K, _, hK, _⟩ := exists_sl2_component_in_involution_centralizer hlarge h2 t ht
  let : Group.IsNilpotent (pCore 2 (centralizer ({t} : Set PSL(3,F)))) := pCore_isPGroup.isNilpotent
  exact not_isComponent_of_solvable_normal_selfCentralizing _ hchar K hK

/-- The fixed subgroup of an inner involution has the same obstruction.
Simplicity and perfectness are inherited from the supplied model. -/
theorem inner_fixed_not_selfCentralizing_twoCore
    [IsSimpleGroup PSL(3,F)] [Group.IsPerfect PSL(3,F)]
    (hlarge : 3 < Nat.card F) (h2 : (2 : F) ≠ 0)
    (a : MulAut PSL(3,F)) (ha : orderOf a = 2)
    (hi : a ∈ MulAut.innerSubgroup PSL(3,F)) :
    ¬ centralizer (pCore 2 a.fixedSubgroup : Set a.fixedSubgroup) ≤ pCore 2 a.fixedSubgroup := by
  obtain ⟨t, rfl⟩ := hi
  have ht : orderOf t = 2 :=
    (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot (center_eq_bot_of_simple_perfect (G := PSL(3,F))))
      t).symm.trans ha
  rw [MulAut.fixedSubgroup_conj]
  exact inner_centralizer_not_selfCentralizing_twoCore hlarge h2 t ht

end Matrix.PSL3.OddInvolutionFixed
