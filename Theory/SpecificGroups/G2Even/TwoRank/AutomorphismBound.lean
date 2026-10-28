module

public import Theory.SpecificGroups.G2Even.TwoRank
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.FieldDegree
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Two-rank bounds for the actual even G₂ semilinear group

An elementary two-subgroup projects to a cyclic group of field automorphisms,
so its image has order at most two. A trivial projection embeds the subgroup
in G₂(F). Otherwise an involution gives a cocycle; a coboundary conjugates its
projection kernel into the coefficient-fixed group. Descent identifies that
full fixed group with G₂ over the field of half the degree. Its already proved
rank bounds the kernel, including the full G₂(2) endpoint.

The two structural hypotheses are explicit: cocycles for involutory field
components are coboundaries, and the pure coefficient-fixed group descends to
the actual fixed field. No numerical rank bound is assumed. Surjectivity of
the semilinear action is a separate input for the full automorphism bounds.
The source assembly must discharge all three structural inputs.

Sources: Aschbacher–Smith, *The Classification of Quasithin Groups*, printed
p.356, 16.1.4(4) and 16.1.7(3a), pp.1171–1172, and 16.3.9, p.1180.
GLS3, Definition 2.5.13, uses arbitrary automorphism conjugacy for field type;
that definition alone does not supply the inner coboundary used here.
-/

public section

open Theory.GroupTheory
open scoped IsMulCommutative

namespace Atlas.G2.EvenTwoRank

section Algebra
variable {N C : Type*} [Group N] [Group C] {φ : C →* MulAut N}

/-- The actual projection kernel embeds by its first coordinate. -/
private def kernelLeft (E : Subgroup (N ⋊[φ] C)) :
    ((SemidirectProduct.rightHom : N ⋊[φ] C →* C).comp E.subtype).ker →* N where
  toFun x := x.1.1.left
  map_one' := rfl
  map_mul' x y := by
    have hx : x.1.1.right = 1 := x.2
    change x.1.1.left * φ x.1.1.right y.1.1.left = _
    simp only [hx, map_one, MulAut.one_apply]

private theorem kernelLeft_injective (E : Subgroup (N ⋊[φ] C)) :
    Function.Injective (kernelLeft E) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply SemidirectProduct.ext h
  exact x.2.trans y.2.symm

/-- Conjugating by the inverse coboundary places the kernel in the pure fixed group. -/
private def kernelFixed (E : Subgroup (N ⋊[φ] C)) [IsMulCommutative E]
    (z : E) (c : N) (hc : z.1.left = c * φ z.1.right c⁻¹) :
    ((SemidirectProduct.rightHom : N ⋊[φ] C →* C).comp E.subtype).ker →*
      (φ z.1.right).fixedSubgroup := by
  let f := (MulAut.conj c⁻¹).toMonoidHom.comp (kernelLeft E)
  refine f.codRestrict _ ?_
  intro x
  rw [MulAut.mem_fixedSubgroup]
  change φ z.1.right (c⁻¹ * x.1.1.left * (c⁻¹)⁻¹) = c⁻¹ * x.1.1.left * (c⁻¹)⁻¹
  rw [inv_inv]
  have hx : x.1.1.right = 1 := x.2
  have hcomm := congrArg (fun a : E => a.1.left)
    (IsMulCommutative.is_comm.comm x.1 z)
  change x.1.1.left * φ x.1.1.right z.1.left =
    z.1.left * φ z.1.right x.1.1.left at hcomm
  simp only [hx, map_one, MulAut.one_apply] at hcomm
  have hfix : z.1.left * φ z.1.right x.1.1.left * z.1.left⁻¹ = x.1.1.left := by
    rw [← hcomm, mul_inv_cancel_right]
  calc
    _ = c⁻¹ * (z.1.left * φ z.1.right x.1.1.left * z.1.left⁻¹) * c := by
      rw [hc]
      simp only [map_mul, map_inv]
      group
    _ = _ := by rw [hfix]

private theorem kernelFixed_injective (E : Subgroup (N ⋊[φ] C)) [IsMulCommutative E]
    (z : E) (c : N) (hc : z.1.left = c * φ z.1.right c⁻¹) :
    Function.Injective (kernelFixed E z c hc) := by
  intro x y h
  apply kernelLeft_injective E
  exact (MulAut.conj c⁻¹).injective (congrArg Subtype.val h)

private def leftOfTrivial (E : Subgroup (N ⋊[φ] C))
    (h : ∀ x : E, x.1.right = 1) : E →* N where
  toFun x := x.1.left
  map_one' := rfl
  map_mul' x y := by
    change x.1.left * φ x.1.right y.1.left = _
    simp only [h x, map_one, MulAut.one_apply]

private theorem leftOfTrivial_injective (E : Subgroup (N ⋊[φ] C))
    (h : ∀ x : E, x.1.right = 1) : Function.Injective (leftOfTrivial E h) := by
  intro x y hxy
  exact Subtype.ext (SemidirectProduct.ext hxy ((h x).trans (h y).symm))

private theorem elementary_subgroup {p : ℕ} {G : Type*} [Group G]
    [IsElementaryAbelian p G] (H : Subgroup G) : IsElementaryAbelian p H := by
  refine {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one ?_ }
  intro x
  apply Subtype.ext
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p p G) x.1

private theorem elementary_card_le_of_embedding {G H : Type*} [Group G] [Group H]
    [Finite H] [IsElementaryAbelian 2 G] (f : G →* H) (hf : Function.Injective f)
    {r : ℕ} (hr : primeRank 2 H ≤ r) : Nat.card G ≤ 2 ^ r := by
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le H).mp hr f.range he
  rwa [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at hc
end Algebra

open LieAutomorphismExtensions EvenFieldFixedResidual
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

private instance finiteFieldAut : Finite (F ≃+* F) :=
  Finite.of_injective (fun e : F ≃+* F => (e : F → F))
    (fun _ _ h => RingEquiv.ext (congrFun h))

private instance finiteSemilinear : Finite (Model F ⋊[fieldAction] (F ≃+* F)) :=
  Finite.of_equiv (Model F × (F ≃+* F)) SemidirectProduct.equivProd.symm

variable
  (hboundary : ∀ (σ : F ≃+* F), orderOf σ = 2 →
    ∀ g : Model F, g * fieldAction σ g = 1 →
      ∃ c : Model F, g = c * fieldAction σ c⁻¹)
  (hdescent : ∀ (σ : F ≃+* F), orderOf σ = 2 →
    Nonempty ((fieldAction σ).fixedSubgroup ≃* Model (fixedField σ)))

include hboundary hdescent in
/-- Cardinality bound for each elementary subgroup of the actual semilinear group,
conditional only on cocycle conjugacy and coefficient-fixed descent. -/
theorem elementary_semilinear_card_le {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (E : Subgroup (Model F ⋊[fieldAction] (F ≃+* F)))
    (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 2 ^ (3 * n) := by
  classical
  let := hE
  by_cases htriv : ∀ x : E, x.1.right = 1
  · exact elementary_card_le_of_embedding (leftOfTrivial E htriv)
      (leftOfTrivial_injective E htriv) (two_rank F hF).le
  push Not at htriv
  obtain ⟨z, hz⟩ := htriv
  have hz2 : z.1 ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z.1 z.2
  have hs : orderOf z.1.right = 2 :=
    orderOf_eq_prime (congrArg SemidirectProduct.right hz2) hz
  have hg : z.1.left * fieldAction z.1.right z.1.left = 1 :=
    congrArg SemidirectProduct.left hz2
  obtain ⟨c, hc⟩ := hboundary z.1.right hs z.1.left hg
  obtain ⟨d⟩ := hdescent z.1.right hs
  obtain ⟨m, hm, hnm, hFm⟩ := fixedField_card z.1.right hs hF
  let f : E →* (F ≃+* F) := SemidirectProduct.rightHom.comp E.subtype
  let j : f.ker →* Model (fixedField z.1.right) :=
    d.toMonoidHom.comp (kernelFixed E z c hc)
  have hj : Function.Injective j := d.injective.comp (kernelFixed_injective E z c hc)
  let : IsElementaryAbelian 2 f.ker := elementary_subgroup f.ker
  have hk : Nat.card f.ker ≤ 2 ^ (3 * m) :=
    elementary_card_le_of_embedding j hj (two_rank (fixedField z.1.right) hFm).le
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hr : Nat.card f.range ≤ 2 := by
    apply Nat.le_of_dvd (by decide)
    rw [← IsCyclic.exponent_eq_card]
    exact he.exponent_dvd_p
  calc
    Nat.card E = Nat.card f.ker * Nat.card f.range := by
      rw [← f.ker.card_mul_index, Subgroup.index_ker]
    _ ≤ 2 ^ (3 * m) * 2 := Nat.mul_le_mul hk hr
    _ = 2 ^ (3 * m + 1) := by rw [pow_succ]
    _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by decide) (by omega)

include hboundary hdescent in
/-- The semilinear group has two-rank at most 3n. The elementary-subgroup argument
also allows the binary field, without identifying its full and derived groups. -/
theorem semilinear_two_rank_le {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    primeRank 2 (Model F ⋊[fieldAction] (F ≃+* F)) ≤ 3 * n := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  exact elementary_semilinear_card_le F hboundary hdescent hF

include hboundary hdescent in
/-- Coverage and the proved faithful semilinear action transfer the bound to
all automorphisms of the full G₂ model when q > 2. -/
theorem automorphism_two_rank_le {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hcoverage : Function.Surjective (semilinearAction (F := F))) :
    primeRank 2 (MulAut (Model F)) ≤ 3 * n := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (show 1 < n by omega)
  let e := MulEquiv.ofBijective (semilinearAction (F := F))
    ⟨semilinearAction_injective hq, hcoverage⟩
  rw [← primeRank_equiv 2 e]
  exact semilinear_two_rank_le F hboundary hdescent hF

include hboundary hdescent in
/-- The same bound for automorphisms of the genuine derived subgroup, transported
through its proved equivalence with the full model at the ordinary endpoints. -/
theorem derived_automorphism_two_rank_le {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n)
    (hcoverage : Function.Surjective (semilinearAction (F := F))) :
    primeRank 2 (MulAut (commutator (Model F))) ≤ 3 * n := by
  rw [primeRank_equiv 2 (derivedAutEquiv F hn hF)]
  exact automorphism_two_rank_le F hboundary hdescent hn hF hcoverage

end Atlas.G2.EvenTwoRank
