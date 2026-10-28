module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.ModelCases
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.Reduction
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# The intrinsic cube-one line in an abelian SU₃ lift

Restrict the actual projection SU₃ → PSU₃ to the full preimage of U. When
that preimage is abelian, its cube-one elements form a subgroup. Their
projective image is preserved by every ambient automorphism admitting a
multiplicative lift, hence by the full pair automizer once coverage is used.

If U is elementary of order nine and the scalar kernel has order three,
the preimage has order 27. Cubing maps it into the scalar kernel. A bound
of nine on the cube-one subgroup therefore forces that subgroup to have
order nine and its projective image to have order three. The Frattini
quotient then has a proper nonzero invariant subgroup.

The determinant-one matrix torsion bound remains an explicit mathematical
input. No conclusion of the source exclusion is built into this input.
Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), and the abelian weight-space argument
underlying A.3.21(c), printed pp.55–56.
-/

@[expose] public section

open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))

/-- Projection restricted to the full preimage of U. -/
def liftProjection : U.comap J.specialToProjective →* U where
  toFun x := ⟨J.specialToProjective x.val, x.property⟩
  map_one' := Subtype.ext J.specialToProjective.map_one
  map_mul' x y := Subtype.ext (J.specialToProjective.map_mul x.val y.val)

/-- The restricted projection is onto U. -/
theorem liftProjection_surjective : Function.Surjective (liftProjection J U) := by
  intro u
  obtain ⟨x, hx⟩ := J.specialToProjective_surjective u.val
  exact ⟨⟨x, by change J.specialToProjective x ∈ U; rw [hx]; exact u.property⟩, Subtype.ext hx⟩

/-- Restriction retains the entire scalar kernel. -/
theorem liftProjection_kernel_card :
    Nat.card (liftProjection J U).ker = Nat.card J.specialToProjective.ker := by
  apply Nat.card_congr
  exact {
    toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
    invFun := fun x => ⟨⟨x.val, by
      change J.specialToProjective x.val ∈ U
      rw [show J.specialToProjective x.val = 1 from x.property]
      exact U.one_mem⟩, Subtype.ext x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

variable [IsMulCommutative (U.comap J.specialToProjective)]

/-- The cube-one subgroup of the abelian full preimage. -/
def cubeSubgroup : Subgroup (U.comap J.specialToProjective) :=
  (powMonoidHom 3).ker

/-- The projective image of the cube-one elements. -/
def cubeOneImage : Subgroup U := (cubeSubgroup J U).map (liftProjection J U)

/-- Membership is witnessed by an actual cube-one special-unitary matrix. -/
theorem mem_cubeOneImage_iff (u : U) :
    u ∈ cubeOneImage J U ↔ ∃ x : J.specialSubgroup, x ^ 3 = 1 ∧ J.specialToProjective x = u := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, congrArg Subtype.val hx, rfl⟩
  · rintro ⟨x, hx, he⟩
    refine ⟨⟨x, ?_⟩, Subtype.ext hx, Subtype.ext he⟩
    change J.specialToProjective x ∈ U
    rw [he]
    exact u.property

/-- Multiplicative lifts preserve this subgroup for the full pair action. -/
theorem cubeOneImage_invariant_of_lifts
    (hlift : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ f : J.specialSubgroup →* J.specialSubgroup,
        ∀ x, J.specialToProjective (f x) = a (J.specialToProjective x))
    (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∀ b ∈ pairAutomizer S U, ∀ u ∈ cubeOneImage J U, b u ∈ cubeOneImage J U := by
  intro b hb u hu
  obtain ⟨a, _, ha⟩ := hb
  obtain ⟨f, hf⟩ := hlift a
  obtain ⟨x, hx, hxu⟩ := (mem_cubeOneImage_iff J U u).mp hu
  apply (mem_cubeOneImage_iff J U (b u)).mpr
  refine ⟨f x, ?_, ?_⟩
  · rw [← map_pow, hx, map_one]
  · rw [hf, hxu, ha]

/-- The matrix torsion bound and the scalar kernel order give a line. -/
theorem cubeOneImage_card_three [Finite E]
    (he : IsElementaryAbelian 3 U) (hU : Nat.card U = 9)
    (hk : Nat.card J.specialToProjective.ker = 3)
    (hc : Nat.card (cubeSubgroup J U) ≤ 9) : Nat.card (cubeOneImage J U) = 3 := by
  let q := liftProjection J U
  let K := cubeSubgroup J U
  have hqk : Nat.card q.ker = 3 := (liftProjection_kernel_card J U).trans hk
  have hq : Nat.card (U.comap J.specialToProjective) = 27 := by
    have hh := q.ker.card_mul_index
    rw [index_ker, MonoidHom.range_eq_top.mpr (liftProjection_surjective J U),
      Nat.card_congr Subgroup.topEquiv.toEquiv, hqk, hU] at hh
    omega
  have hpower : (powMonoidHom 3 : (U.comap J.specialToProjective) →* _).range ≤ q.ker := by
    rintro _ ⟨x, rfl⟩
    change q (x ^ 3) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.exponent_dvd_p _
  have hpr : Nat.card (powMonoidHom 3 : (U.comap J.specialToProjective) →* _).range ≤ 3 := by
    exact (Nat.card_le_card_of_injective (inclusion hpower) (inclusion_injective hpower)).trans_eq hqk
  have hK : Nat.card K = 9 := by
    have hh := K.card_mul_index
    change Nat.card K * (powMonoidHom 3 : (U.comap J.specialToProjective) →* _).ker.index = _ at hh
    rw [index_ker, hq] at hh
    change Nat.card K ≤ 9 at hc
    nlinarith
  have hle : q.ker ≤ K := by
    intro x hx
    change x ^ 3 = 1
    have hx3 : x.val ^ 3 = 1 := congrArg
      (fun z : J.specialToProjective.ker => z.val)
      (J.specialToProjective_ker_cube ⟨x.val, congrArg Subtype.val hx⟩)
    exact Subtype.ext hx3
  have hkerK : Nat.card (q.ker.subgroupOf K) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hqk
  have hh := (q.ker.subgroupOf K).card_mul_index
  rw [hkerK, hK] at hh
  change 3 * q.ker.relIndex K = 9 at hh
  rw [relIndex_ker] at hh
  change 3 * Nat.card (cubeOneImage J U) = 9 at hh
  omega

/-- An order-three cube-one image excludes every irreducible pair action. -/
theorem reducible_of_cubeOneImage_card [Finite E]
    (he : IsElementaryAbelian 3 U) (hU : Nat.card U = 9)
    (hline : Nat.card (cubeOneImage J U) = 3)
    (hlift : ∀ a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J),
      ∃ f : J.specialSubgroup →* J.specialSubgroup,
        ∀ x, J.specialToProjective (f x) = a (J.specialToProjective x))
    (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : PairReducible S U := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let _ := he
  let : Fact (IsPGroup 3 U) := ⟨IsPGroup.of_card (n := 2) hU⟩
  apply reducible_of_invariant_subgroup S U (cubeOneImage J U)
  · rw [frattini_eq_bot_of_isElementaryAbelian (R := U) (p := 3)]
    intro h
    have hh := bot_unique h
    rw [hh, Subgroup.card_bot] at hline
    omega
  · intro h
    rw [h, Nat.card_congr Subgroup.topEquiv.toEquiv, hU] at hline
    omega
  · exact cubeOneImage_invariant_of_lifts J U hlift S


/-- The remaining matrix bound. The full preimage is abelian; only its
cube-one subgroup is counted. This is independent of Sylow and pair actions. -/
def CubicTorsionBound (p : ℕ) : Prop :=
  ∀ {F : Type} [Field F] [Finite F] (K : HermitianForm 3 F),
    Nat.card F = p ^ 2 → (∀ x, K.conj x = x ^ p) →
    ∀ (V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup K))
      [IsMulCommutative (V.comap K.specialToProjective)],
      Nat.card (cubeSubgroup K V) ≤ 9

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.AbelianLift
