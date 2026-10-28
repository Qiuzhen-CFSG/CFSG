module
public import Stellmacher.PushingUp.SL2TwoNaturalSylow
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Quotient
/-!
# The natural SL₂(2) commutator complement

For an elementary abelian 2-group acted on by a group identified with SL₂(2),
if the quotient by the global fixed subgroup is natural, then the full action
commutator complements that subgroup and carries the same natural action.
The public interface accepts the caller's named fixed subgroup and its exact
quotient action, so the coordinate identification is preserved in applications.

The normal order-three subgroup of SL₂(2) has no fixed vector on the natural
module. Its fixed subgroup upstairs is therefore precisely the global fixed
subgroup. Coprime action splits off its commutator; normality makes this
complement invariant under the whole actor. The resulting decomposition shows
that its commutator is the full action commutator. Finally the quotient map
restricts to an equivariant isomorphism from the complement to the natural
quotient. The finite matrix facts are checked by kernel reduction.

Source: Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (2.2) for the
natural quotient and (3.2), p. 14, for the n = 1 splitting. This supplies
the distance-two module step within Theorem 2 of the N-group paper,
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped IsMulCommutative
namespace Stellmacher.PushingUp
private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private def threeSubgroup : Subgroup SL where
  carrier := {a | a ^ 3 = 1}
  one_mem' := by simp
  mul_mem' := by decide +revert +kernel
  inv_mem' := by intro a ha; change a ^ 3 = 1 at ha; change (a⁻¹) ^ 3 = 1; simp [inv_pow, ha]
private instance : DecidablePred (· ∈ threeSubgroup) := fun a =>
  inferInstanceAs (Decidable (a ^ 3 = 1))
private instance : Fintype threeSubgroup := Subtype.fintype _
private instance : threeSubgroup.Normal where
  conj_mem := by decide +revert +kernel
private theorem threeSubgroup_card : Nat.card threeSubgroup = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem threeSubgroup_fixed (y : Fin 2 → ZMod 2)
    (h : ∀ a : threeSubgroup, Matrix.mulVec a.1.1 y = y) : y = 0 := by
  decide +revert +kernel

private theorem normal_commutator_invariant
    {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]
    (F : Subgroup A) [F.Normal] : IsInvariant A V (commutatorAction F V) := by
  have hforward (g : A) (v : V) (hv : v ∈ commutatorAction F V) :
      g • v ∈ commutatorAction F V := by
    rw [commutatorAction_eq_closure] at hv ⊢
    induction hv using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, z, rfl⟩ := hw
      let aga : F := ⟨g * (a : A) * g⁻¹, Subgroup.Normal.conj_mem (inferInstance : F.Normal) a a.property g⟩
      refine Subgroup.subset_closure ⟨aga, g • z, ?_⟩
      change g • (z⁻¹ * (a : A) • z) = (g • z)⁻¹ * (aga : A) • (g • z)
      simp [aga, smul_mul', smul_inv', ← mul_smul, mul_assoc]
    | one => simp
    | mul x y hx hy hxs hys => simpa [smul_mul'] using Subgroup.mul_mem _ hxs hys
    | inv x hx hxs => simpa [smul_inv'] using Subgroup.inv_mem _ hxs
  constructor
  intro g v
  exact ⟨hforward g v, fun h => by simpa using hforward g⁻¹ (g • v) h⟩

private theorem natural_quotient_complement
    {A V : Type*} [Group A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (eA : A ≃* SL) (hC : IsInvariant A V (FixedPoints.subgroup A V))
    (hNat : letI := quotientMulDistribMulAction (A := A) (G := V) (FixedPoints.subgroup A V) hC;
      IsNaturalSL2TwoActionAlong (V ⧸ FixedPoints.subgroup A V) eA) :
    IsCompl (FixedPoints.subgroup A V) (commutatorAction A V) := by
  let C := FixedPoints.subgroup A V
  let F := threeSubgroup.comap eA.toMonoidHom
  let eF : F ≃* threeSubgroup :=
    { toFun := fun a => ⟨eA a, a.property⟩
      invFun := fun a => ⟨eA.symm a, by simp [F, a.property]⟩
      left_inv := fun a => Subtype.ext (eA.symm_apply_apply a)
      right_inv := fun a => Subtype.ext (eA.apply_symm_apply a)
      map_mul' := fun a b => Subtype.ext (eA.map_mul a b) }
  let : Finite F := Finite.of_equiv threeSubgroup eF.symm.toEquiv
  have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [Nat.card_congr eF.toEquiv, threeSubgroup_card, hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hcompl : IsCompl (FixedPoints.subgroup F V) (commutatorAction F V) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm fun x y =>
        (IsMulCommutative.is_comm (M := V)).comm x y) hcop inferInstance
  let := quotientMulDistribMulAction (A := A) (G := V) C hC
  obtain ⟨eW, heW⟩ := hNat
  have hfixed : FixedPoints.subgroup F V = C := by
    apply le_antisymm
    · intro v hv
      have hvfix (a : F) : (a : A) • v = v :=
        ((FixedPoints.mem_subgroup (M := F) (a := v)).mp hv) a
      have hz : eW (Additive.ofMul (QuotientGroup.mk' C v)) = 0 := by
        apply threeSubgroup_fixed
        intro a
        have he := heW (eA.symm a) (QuotientGroup.mk' C v)
        have hfix : eA.symm (a : SL) • QuotientGroup.mk' C v = QuotientGroup.mk' C v := by
          change QuotientGroup.mk' C (eA.symm (a : SL) • v) = QuotientGroup.mk' C v
          exact congrArg (QuotientGroup.mk' C) (hvfix (eF.symm a))
        rw [hfix, eA.apply_symm_apply] at he
        exact he.symm
      have hq : QuotientGroup.mk' C v = 1 := by
        exact eW.injective (hz.trans eW.map_zero.symm)
      exact (QuotientGroup.eq_one_iff (N := C) v).mp hq
    · intro v hv
      exact fun a => ((FixedPoints.mem_subgroup (M := A) (a := v)).mp hv) (a : A)
  rw [hfixed] at hcompl
  let U := commutatorAction F V
  let : F.Normal := inferInstanceAs ((threeSubgroup.comap eA.toMonoidHom).Normal)
  let : IsInvariant A V U := normal_commutator_invariant F
  have hcomm : commutatorAction A V = U := by
    apply le_antisymm
    · rw [commutatorAction_eq_closure]
      apply (Subgroup.closure_le (K := _)).mpr
      rintro d ⟨a, v, rfl⟩
      have hv : v ∈ C ⊔ U := by rw [hcompl.sup_eq_top]; trivial
      obtain ⟨c, hc, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hv
      have hcf : a • c = c := ((FixedPoints.mem_subgroup (M := A) (a := c)).mp hc) a
      have hau : a • u ∈ U := (IsInvariant.invariant a u).mp hu
      have heq : (c * u)⁻¹ * a • (c * u) = u⁻¹ * a • u := by
        simp [smul_mul', hcf, mul_assoc]
      rw [heq]
      exact U.mul_mem (U.inv_mem hu) hau
    · change commutatorAction F V ≤ commutatorAction A V
      rw [commutatorAction_eq_closure (A := F), commutatorAction_eq_closure (A := A)]
      apply (Subgroup.closure_le (K := _)).mpr
      rintro d ⟨a, v, rfl⟩
      exact Subgroup.subset_closure ⟨(a : A), v, rfl⟩
  rwa [hcomm]

/-- A natural quotient by the global fixed subgroup splits as the full action
commutator, with the same specified identification of the acting group. -/
public theorem naturalSL2TwoActionAlong_commutator_of_natural_quotient
    {A V : Type*} [Group A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (eA : A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (C : Subgroup V) (hCeq : C = FixedPoints.subgroup A V)
    (hC : IsInvariant A V C)
    (hNat : letI := quotientMulDistribMulAction (A := A) (G := V) C hC;
      IsNaturalSL2TwoActionAlong (V ⧸ C) eA) :
    IsCompl C (commutatorAction A V) ∧
      let : IsInvariant A V (commutatorAction A V) := commutatorAction_isInvariant
      IsNaturalSL2TwoActionAlong (commutatorAction A V) eA := by
  subst C
  have hcompl := natural_quotient_complement eA hC hNat
  refine ⟨hcompl, ?_⟩
  let C := FixedPoints.subgroup A V
  let U := commutatorAction A V
  let : IsInvariant A V U := commutatorAction_isInvariant
  let := quotientMulDistribMulAction (A := A) (G := V) C hC
  have hcomp : U.IsComplement' C := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hcompl.disjoint.symm
    rw [← Subgroup.normal_mul U C, sup_comm, hcompl.sup_eq_top]
    rfl
  let e : (V ⧸ C) ≃* U := hcomp.QuotientMulEquiv
  obtain ⟨eW, heW⟩ := hNat
  refine ⟨e.symm.toAdditive.trans eW, ?_⟩
  intro a u
  change eW (Additive.ofMul (e.symm (a • u))) =
    Matrix.mulVec (eA a).1 (eW (Additive.ofMul (e.symm u)))
  have he (u : U) : e.symm u = QuotientGroup.mk' C (u : V) := rfl
  rw [he, he]
  exact heW a (QuotientGroup.mk' C (u : V))
end Stellmacher.PushingUp
