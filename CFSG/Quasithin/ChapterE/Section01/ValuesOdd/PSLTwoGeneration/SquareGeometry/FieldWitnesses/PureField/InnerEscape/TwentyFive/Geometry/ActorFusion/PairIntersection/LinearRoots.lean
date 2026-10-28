module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.PairIntersection.Inputs
public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import GorensteinWalter.DihedralOddRotationCentralizer
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Linear square-root rigidity in the order-25 inner model

The linear elements of the literal inner model lift through the canonical
PSL₂ embedding. In odd PSL₂, the centralizer of an involution is a cyclic
torus extended by an inverting involution. Every element outside the torus
squares to one. Thus roots of a nonidentity square lie in the torus, where
uniqueness of the involution identifies equal-square roots up to inversion.
Applying the same argument to the centralizer of a commuting involution
identifies it with the square of an order-four element.

`PairIntersection.linearRootRigidity` discharges both fields of the exact
`LinearRootRigidity` contract used by `Frame.linear_common_eq_one_or_twist`
and `Frame.pairIntersectionBound_of_squareRoots`. No local root-existence,
frame, actor, intersection, or generation premise is needed. The result
holds for any field automorphism σ; in particular it applies to the
involutory σ of the source model.

Source: the local model calculation supporting Aschbacher--Smith E.1.14(6),
printed p.214, citing Aschbacher (1982), Lemma 4.10. This proves the rigidity
input, not the full E-generation assertion of E.1.14(6).
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
namespace PairIntersection

private theorem reflected_mem_of_square_ne_one {G : Type*} [Group G]
    {T : Subgroup G} {w x : G} (hwT : w ∉ T) (hw : w ^ 2 = 1)
    (hi : ∀ a ∈ T, w * a * w⁻¹ = a⁻¹)
    (hx : x ∈ T ⊔ zpowers w) (hx2 : x ^ 2 ≠ 1) : x ∈ T := by
  have hww : w * w = 1 := by simpa [pow_two] using hw
  obtain ⟨a, ha, rfl | rfl⟩ :=
    (mem_sup_zpowers_of_involution_inverts hwT hww hi).mp hx
  · exact ha
  · exfalso
    apply hx2
    calc
      (a * w) ^ 2 = a * (w * a * w⁻¹) * (w * w) := by rw [pow_two]; group
      _ = 1 := by rw [hi a ha, hww]; simp

private theorem square_order_of_order_four {G : Type*} [Group G]
    {r : G} (hr : orderOf r = 4) : orderOf (r ^ 2) = 2 := by
  rw [orderOf_pow' r (by decide : (2 : ℕ) ≠ 0), hr]
  decide

private theorem cyclic_same_square {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {r s : G} (hr : orderOf r = 4) (he : r ^ 2 = s ^ 2) : s = r ∨ s = r⁻¹ := by
  let : CommGroup G := IsCyclic.commGroup
  have hr2 := square_order_of_order_four hr
  have hc : Commute s r⁻¹ := Commute.all _ _
  have hs : (s * r⁻¹) ^ 2 = 1 := by
    rw [hc.mul_pow, inv_pow, ← he, mul_inv_cancel]
  by_cases h : s * r⁻¹ = 1
  · exact Or.inl (mul_inv_eq_one.mp h)
  · have ho : orderOf (s * r⁻¹) = 2 := orderOf_eq_prime hs h
    have hh : s * r⁻¹ = r ^ 2 := IsCyclic.eq_of_orderOf_eq_two ho hr2
    right
    have h4 : r ^ 4 = 1 := hr ▸ pow_orderOf_eq_one r
    calc
      s = r ^ 2 * r := mul_inv_eq_iff_eq_mul.mp hh
      _ = r⁻¹ := by
        apply mul_right_cancel (b := r)
        simpa only [pow_succ, pow_zero, one_mul, inv_mul_cancel] using h4

variable {F : Type*} [Field F] [Finite F]

private theorem psl_same_square (hF : IsOddPrimePower (Nat.card F))
    {r s : PSL2 F} (hr : orderOf r = 4) (he : r ^ 2 = s ^ 2) :
    s = r ∨ s = r⁻¹ := by
  have hr2 := square_order_of_order_four hr
  have ht : IsInvolution (r ^ 2) := by
    constructor
    · intro h
      simp [h] at hr2
    · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hr2])
  obtain ⟨T, w, hT, _, hw, hwT, hi, hC, _⟩ := psl2_reflected_torus_card hF ht
  have hrT : r ∈ T := by
    apply reflected_mem_of_square_ne_one hwT hw.2 hi
    · rw [← hC, mem_centralizer_singleton_iff]
      exact (Commute.self_pow r 2).eq
    · exact ht.1
  have hsT : s ∈ T := by
    apply reflected_mem_of_square_ne_one hwT hw.2 hi
    · rw [← hC, mem_centralizer_singleton_iff, he]
      exact (Commute.self_pow s 2).eq
    · rw [← he]
      exact ht.1
  let : IsCyclic T := hT
  rcases cyclic_same_square (r := (⟨r, hrT⟩ : T)) (s := ⟨s, hsT⟩)
    (by simpa only [← orderOf_coe] using hr) (Subtype.ext he) with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

private theorem psl_central_involution (hF : IsOddPrimePower (Nat.card F))
    {r z : PSL2 F} (hr : orderOf r = 4) (hz : orderOf z = 2)
    (hc : Commute z r) : z = r ^ 2 := by
  have ht : IsInvolution z := by
    constructor
    · intro h
      simp [h] at hz
    · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hz])
  obtain ⟨T, w, hT, hzT, hw, hwT, hi, hC, _⟩ := psl2_reflected_torus_card hF ht
  have hrT : r ∈ T := by
    apply reflected_mem_of_square_ne_one hwT hw.2 hi
    · rw [← hC, mem_centralizer_singleton_iff]
      exact hc.symm.eq
    · intro h
      have hd := orderOf_dvd_of_pow_eq_one h
      rw [hr] at hd
      norm_num at hd
  let : IsCyclic T := hT
  have he := IsCyclic.eq_of_orderOf_eq_two (x := (⟨z, hzT⟩ : T))
    (y := (⟨r, hrT⟩ : T) ^ 2) (by simpa only [← orderOf_coe] using hz)
    (square_order_of_order_four (by simpa only [← orderOf_coe] using hr))
  exact congrArg Subtype.val he

private theorem linear_mem_pslRange (hF : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F)
    (σ : F ≃+* F) (x : innerModel F σ) (hx : (x : PGammaL2 F).right = 1) :
    (x : PGammaL2 F) ∈ pGammaL2PSLRange F := by
  let : (pGammaL2PSLRange F).Normal :=
    pGammaL2PSLRange_normal F hF hcard
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_left.mp x.property
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
  obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff F a).mp ha
  have hn : σ ^ n = 1 := by
    have hh := congrArg (fun g : PGammaL2 F => g.right) hab
    simpa only [← map_zpow, SemidirectProduct.mul_right, SemidirectProduct.right_inl,
      SemidirectProduct.right_inr, one_mul, hx] using hh
  rw [← map_zpow, hn, map_one, mul_one] at hab
  rw [← hab]
  exact (mem_pGammaL2PSLRange_iff F _).mpr ⟨y, rfl⟩

private def pslLift (σ : F ≃+* F) : PSL2 F →* innerModel F σ :=
  (((SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp
    ProjectiveSpecialLinearGroup.toPGL)).codRestrict (innerModel F σ)
    (fun x => mem_sup_left (show _ ∈ pGammaL2PSLRange F from ⟨x, rfl⟩))

omit [Finite F] in
private theorem pslLift_injective (σ : F ≃+* F) : Function.Injective (pslLift σ) := by
  intro a b h
  exact ProjectiveSpecialLinearGroup.toPGL_injective
    (SemidirectProduct.inl_injective (congrArg Subtype.val h))

private theorem exists_pslLift (hF : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F)
    (σ : F ≃+* F) (x : innerModel F σ) (hx : (x : PGammaL2 F).right = 1) :
    ∃ y : PSL2 F, pslLift σ y = x := by
  obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff F x).mp (linear_mem_pslRange hF hcard σ x hx)
  exact ⟨y, Subtype.ext hy⟩

/-- Linear square roots of order four in the actual order-25 inner model are
rigid up to inversion, and their commuting linear involution is their square. -/
theorem linearRootRigidity (F : Type*) [Field F] [Finite F]
    (σ : F ≃+* F) (hF : Nat.card F = 5 ^ 2) : LinearRootRigidity F σ := by
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨5, 2, by decide, by decide, by decide, hF⟩
  have hcard : 3 < Nat.card F := by rw [hF]; decide
  have hf := pslLift_injective σ
  constructor
  · intro r s hr hs ho he
    obtain ⟨r, rfl⟩ := exists_pslLift hodd hcard σ r hr
    obtain ⟨s, rfl⟩ := exists_pslLift hodd hcard σ s hs
    have hor : orderOf r = 4 := (orderOf_injective (pslLift σ) hf r).symm.trans ho
    have hsq : r ^ 2 = s ^ 2 := hf (by simpa only [map_pow] using he)
    rcases psl_same_square hodd hor hsq with h | h
    · exact Or.inl (congrArg (pslLift σ) h)
    · exact Or.inr (by rw [h, map_inv])
  · intro r z hr hz ho hzo hc
    obtain ⟨r, rfl⟩ := exists_pslLift hodd hcard σ r hr
    obtain ⟨z, rfl⟩ := exists_pslLift hodd hcard σ z hz
    have hor : orderOf r = 4 := (orderOf_injective (pslLift σ) hf r).symm.trans ho
    have hoz : orderOf z = 2 := (orderOf_injective (pslLift σ) hf z).symm.trans hzo
    have hcomm : Commute z r := hf (by simpa only [map_mul] using hc.eq)
    have he := psl_central_involution hodd hor hoz hcomm
    simpa only [map_pow] using congrArg (pslLift σ) he

end PairIntersection
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
