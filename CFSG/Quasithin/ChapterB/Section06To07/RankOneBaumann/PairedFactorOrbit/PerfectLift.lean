module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.Residuals
public import Theory.GroupTheory.SolvableResidual.TwoKernel
/-!
# The actual perfect factor and its conjugate cover the residual

A two-group action kernel identifies the canonical solvable-residual factor
with its two-residual lift. Conjugating the original factor preimage commutes
with lifting and taking the residual. The prescribed quotient exchanger thus
gives an actual conjugate component, and the product of the two preimage
residuals is the original O²(G). No residual coverage is assumed.
Source: Aschbacher--Smith B.6.9 and E.2.3, pp.115--116 and216--217.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] [Finite H] in
private theorem preimage_conjugate (q : G →* H) (A : Subgroup H) (t : G) :
    (A.comap q).map (MulAut.conj t).toMonoidHom =
      (A.map (MulAut.conj (q t)).toMonoidHom).comap q := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨q a,ha,?_⟩
    change q t * q a * (q t)⁻¹ = q (t*a*t⁻¹)
    simp only [map_mul,map_inv]
  · rintro ⟨a,ha,he⟩
    refine ⟨t⁻¹*x*t,?_,?_⟩
    · change q (t⁻¹*x*t) ∈ A
      rw [map_mul,map_mul,map_inv,←he]
      change (q t)⁻¹ * (q t * a * (q t)⁻¹) * q t ∈ A
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      exact ha
    · change t*(t⁻¹*x*t)*t⁻¹=x
      group

omit [Finite H] in
/-- The canonical perfect factor and its prescribed conjugate cover the actual residual. -/
theorem selected_perfect_factor_sup_conjugate
    (q : G →* H) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (Y : Subgroup H) (A B : Subgroup Y) [A.Normal] [B.Normal] [Group.IsPerfect A]
    (hAB : A ⊔ B = ⊤) (hR : (pResidual 2 G).map q ≤ Y)
    (K : Subgroup G)
    (hK : (solvableResidual (factorPreimage q Y A)).map
      (factorPreimage q Y A).subtype = K)
    (t : G) (ht : (A.map Y.subtype).map (MulAut.conj (q t)).toMonoidHom = B.map Y.subtype) :
    pResidual 2 G = K ⊔ K.map (MulAut.conj t).toMonoidHom := by
  let : Group.IsPerfect (A.map Y.subtype) := Group.IsPerfect.ofSurjective
    (f := (A.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
    (A.equivMapOfInjective Y.subtype Y.subtype_injective).surjective
  have hA : factorResidual q Y A = K :=
    (embedded_pResidual_eq_solvableResidual_of_two_kernel q (A.map Y.subtype) hq hk).trans hK
  have hm : (factorResidual q Y A).map (MulAut.conj t).toMonoidHom = factorResidual q Y B := by
    change ((pResidual 2 (factorPreimage q Y A)).map _).map _ = _
    rw [map_embedded_pResidual]
    have hp : (factorPreimage q Y A).map (MulAut.conj t).toMonoidHom = factorPreimage q Y B := by
      rw [factorPreimage,preimage_conjugate,ht]
    rw [hp]
  rw [←hA,hm]
  exact (factorResidual_sup q hq Y A B hAB hR).symm
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
