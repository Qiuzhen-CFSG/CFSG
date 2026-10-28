module
public import Theory.Representation.InvertedOddSubgroup
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupTheory.Commutator.ActionTriviality

/-!
For an odd nontrivial automorphism subgroup of a finite elementary abelian
2-group, inversion by an involution produces a nontrivial displacement
subgroup inside the odd commutator support.  We restrict the action to the
normalizer of the odd subgroup, apply the coprime fixed-point decomposition,
and use the square-cardinality theorem for inverted odd actions.  The closure
description of commutators also gives the generator containment needed by the
source13 support argument.
-/

open scoped IsMulCommutative

public theorem inverted_odd_support_displacement_packet
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (R : Subgroup (MulAut W)) (hodd : Odd (Nat.card R)) (hR : R ≠ ⊥)
    (t : MulAut W) (ht : IsInvolution t)
    (hinverts : ∀ r ∈ R, t * r * t⁻¹ = r⁻¹) :
    let U := commutatorAction R W
    let C := FixedPoints.subgroup R W
    Disjoint U C ∧ ∃ S : Subgroup W, S ≠ ⊥ ∧ S ≤ U ∧
      S ≤ commutatorAction (Subgroup.zpowers t) W ∧ Nat.card U = Nat.card S ^ 2 ∧
      ∀ D : Subgroup W, (∀ u ∈ U, u⁻¹ * t u ∈ D) → S ≤ D := by
  classical
  let U := commutatorAction R W
  let C := FixedPoints.subgroup R W
  have hcop : Nat.Coprime (Nat.card R) (Nat.card W) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := R) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hfix := actsTrivially_of_commutatorAction_eq_bot hbot
    apply hR
    apply bot_unique
    intro r hr
    ext point
    exact hfix ⟨r,hr⟩ point
  let N := Subgroup.normalizer (R : Set (MulAut W))
  have htN : t ∈ N := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · rintro _ ⟨r,hr,rfl⟩
      change t*r*t⁻¹ ∈ R
      rw [hinverts r hr]
      exact R.inv_mem hr
    · intro r hr
      refine ⟨r⁻¹,R.inv_mem hr,?_⟩
      change t*r⁻¹*t⁻¹=r
      simpa only [inv_inv] using hinverts r⁻¹ (R.inv_mem hr)
  let _ : IsInvariant N W U := commutatorAction_isInvariant_of_normalizing_actor N R le_rfl
  let Ri := R.subgroupOf N
  let ti : N := ⟨t,htN⟩
  let _ : IsElementaryAbelian 2 U := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun point =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) (point : W)) }
  have hRiOdd : Odd (Nat.card Ri) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show R ≤ N from Subgroup.le_normalizer)).toEquiv]
    exact hodd
  have hti : IsInvolution ti :=
    ⟨fun heq => ht.1 (congrArg Subtype.val heq),Subtype.ext ht.2⟩
  have hinvertRi : ∀ r : Ri, ti * (r : N) * ti⁻¹ = (r : N)⁻¹ := by
    intro r
    exact Subtype.ext (hinverts r r.property)
  have hRiFixed : FixedPoints.subgroup Ri U = ⊥ := by
    apply bot_unique
    intro point hpoint
    have hfixed : (point : W) ∈ C := by
      intro r
      have hh := hpoint ⟨⟨r,Subgroup.le_normalizer r.property⟩,r.property⟩
      exact congrArg Subtype.val hh
    exact Subtype.ext (hcompl.disjoint.le_bot ⟨hfixed,point.property⟩)
  let B := commutatorAction (Subgroup.zpowers ti) U
  let S := B.map U.subtype
  have hScard : Nat.card S = Nat.card B := Subgroup.card_map_of_injective U.subtype_injective
  have hsquare : Nat.card U = Nat.card S ^ 2 := by
    rw [hScard]
    exact invertedOddSubgroup_card_eq_commutator_sq Ri hRiOdd ti hti hinvertRi hRiFixed
  have hSneq : S ≠ ⊥ := by
    intro hbot
    rw [hbot,Subgroup.card_bot,one_pow] at hsquare
    exact hUne (Subgroup.card_eq_one.mp hsquare)
  have hSgen (D : Subgroup W) (hD : ∀ u ∈ U, u⁻¹ * t u ∈ D) : S ≤ D := by
    rintro point ⟨vector,hvector,rfl⟩
    change vector ∈ commutatorAction (Subgroup.zpowers ti) U at hvector
    rw [commutatorAction_eq_closure] at hvector
    apply Subgroup.closure_induction (x := vector)
      (p := fun (v : U) _ => (v : W) ∈ D) ?_ ?_ ?_ ?_ hvector
    · rintro vector ⟨actor,point,rfl⟩
      have hTcard : Nat.card (Subgroup.zpowers ti) = 2 := by
        rw [Nat.card_zpowers,orderOf_eq_prime hti.2 hti.1]
      by_cases hone : actor = 1
      · simp only [hone,one_smul,inv_mul_cancel,OneMemClass.coe_one]
        exact D.one_mem
      obtain ⟨other,hother,hunique⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.zpowers ti)).mp hTcard
      have hgenNe : (⟨ti,Subgroup.mem_zpowers ti⟩ : Subgroup.zpowers ti) ≠ 1 :=
        fun heq => hti.1 (congrArg Subtype.val heq)
      have heq : actor = ⟨ti,Subgroup.mem_zpowers ti⟩ :=
        (hunique actor hone).trans (hunique _ hgenNe).symm
      rw [heq]
      exact hD point point.property
    · exact D.one_mem
    · intro x y _ _ hx hy
      exact D.mul_mem hx hy
    · intro x _ hx
      exact D.inv_mem hx
  refine ⟨hcompl.disjoint.symm,S,hSneq,Subgroup.map_subtype_le _,?_,hsquare,hSgen⟩
  apply hSgen
  intro point _
  rw [commutatorAction_eq_closure]
  exact Subgroup.subset_closure ⟨⟨t,Subgroup.mem_zpowers t⟩,point,rfl⟩
