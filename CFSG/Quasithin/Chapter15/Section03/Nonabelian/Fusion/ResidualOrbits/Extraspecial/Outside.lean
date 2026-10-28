module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.QuotientFusion
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces.Certificates

/-!
# Outside involutions in the actual residual

The literal quotient K/(U ∩ K) is identified with SL₃(2), as supplied by
15.3.58–59. Its single involution class supplies a conjugator in K ≤ H.
After conjugation an outside involution is a*u; the two square equations
imply that a sends u to its inverse. Since U/Z has exponent two, u belongs
to the actual fixedLift. No involution-cover assumption is used.

The source noncontainment V ≰ U and elementary structure also supply an
actual involution in V−U. The stronger centralization of the entire fixed
lift and its direct-product structure are separate geometric calculations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the first paragraph proving 15.3.61(2), printed p.1150.
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion
open CFSG.Quasithin.Chapter15.Section03.FusionCore
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial
variable {G : Type*} [Group G] {Z ZS : Subgroup G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

/-- An involution in a coset of a fixed involution has fixed image in the
binary quotient. The lift need not itself centralize that involution. -/
theorem mem_fixedLift_of_involution_mul
    (a : centralizerH Z) (ha : (a : G) ^ 2 = 1) (u : closureU Z ZS)
    (hau : ((a : G) * (u : G)) ^ 2 = 1)
    (hbinary : ∀ w : VectorQuotient Z ZS, w ^ 2 = 1) :
    (u : G) ∈ fixedLift Z ZS a := by
  have hai : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha)
  have haui : ((a : G) * (u : G))⁻¹ = (a : G) * (u : G) :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hau)
  have hconj : (a : G) * (u : G) * (a : G)⁻¹ = (u : G)⁻¹ := by
    have hh := congrArg (fun x : G => x * (a : G)) haui
    simpa only [mul_inv_rev, hai, mul_assoc, show (a : G) * a = 1 by simpa [pow_two] using ha,
      mul_one] using hh.symm
  apply (mem_fixedLift_iff Z ZS a u).mpr
  refine ⟨u.property, ?_⟩
  rw [quotientAction_mk]
  have he : (⟨(a : G) * (u : G) * (a : G)⁻¹,
    (mem_normalizer_iff.mp (H_normalizes_closureU Z ZS a.property) u).mp u.property⟩ :
      closureU Z ZS) = u⁻¹ := Subtype.ext hconj
  rw [he, map_inv]
  exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hbinary (QuotientGroup.mk' _ u))

/-- The actual central quotient of extraspecial U has exponent two. -/
theorem quotient_square_eq_one [IsExtraspecial 2 (closureU Z ZS)]
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (w : VectorQuotient Z ZS) : w ^ 2 = 1 := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf (closureU Z ZS)) w
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [hcenter]
  exact (IsExtraspecial.quotient_elementary_abelian 2 (closureU Z ZS)).sq_mem_center_of_central_quotient u

omit [(Z.subgroupOf (closureU Z ZS)).Normal] in
/-- The earlier nontrivial V-image supplies the required outside involution. -/
theorem exists_involution_in_V_outside_U (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hVU : ¬ V ≤ closureU Z ZS) :
    ∃ a : G, a ∈ V ∧ a ∉ closureU Z ZS ∧ orderOf a = 2 := by
  obtain ⟨a, ha, hn⟩ := SetLike.not_le_iff_exists.mp hVU
  have hp : (⟨a, ha⟩ : V) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 V) _
  exact ⟨a, ha, hn, orderOf_eq_prime (congrArg Subtype.val hp)
    (fun he => hn (he ▸ (closureU Z ZS).one_mem))⟩

private theorem binary_involutions_isConj (a b : Matrix.PSL3Two.SL)
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  have h (x : Matrix.PSL3Two.SL) (hx : orderOf x = 2) :
      IsConj x BinaryLinearThree.FourGroupGeometry.FixedSpaces.involution := by
    obtain ⟨g, hg⟩ := BinaryLinearThree.FourGroupGeometry.FixedSpaces.exists_involution_conjugator x
      (by intro he; simp [he] at hx) (by simpa only [← pow_two, hx] using pow_orderOf_eq_one x)
    apply isConj_iff.mpr
    refine ⟨g⁻¹, ?_⟩
    calc
      g⁻¹ * x * (g⁻¹)⁻¹ = g⁻¹ * (x * g) := by group
      _ = _ := by rw [hg, inv_mul_cancel_left]
  exact (h a ha).trans (h b hb).symm

/-- The actual residual quotient moves every outside involution into aU_a.
The fixed-lift membership is derived from the two involution equations. -/
theorem outside_conjugate_fixedLift
    [IsExtraspecial 2 (closureU Z ZS)]
    [((closureU Z ZS).subgroupOf (residualK Z)).Normal]
    (hKH : residualK Z ≤ centralizerH Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (eK : (residualK Z ⧸ (closureU Z ZS).subgroupOf (residualK Z)) ≃* Matrix.PSL3Two.SL)
    (a : centralizerH Z) (haK : (a : G) ∈ residualK Z)
    (haU : (a : G) ∉ closureU Z ZS) (ha : orderOf (a : G) = 2)
    (x : G) (hxK : x ∈ residualK Z) (hxU : x ∉ closureU Z ZS) (hx : orderOf x = 2) :
    ∃ u ∈ fixedLift Z ZS a, ConjugateBy (centralizerH Z) x ((a : G) * u) := by
  let q := QuotientGroup.mk' ((closureU Z ZS).subgroupOf (residualK Z))
  let aK : residualK Z := ⟨a, haK⟩
  let xK : residualK Z := ⟨x, hxK⟩
  have horder (y : residualK Z) (hyU : (y : G) ∉ closureU Z ZS)
      (hy : orderOf (y : G) = 2) : orderOf (eK (q y)) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ← map_pow]
      have he : y ^ 2 = 1 := Subtype.ext (hy ▸ pow_orderOf_eq_one (y : G))
      rw [he, map_one, map_one]
    · intro he
      have hq : q y = 1 := eK.injective (he.trans (map_one eK).symm)
      exact hyU ((QuotientGroup.eq_one_iff y).mp hq)
  obtain ⟨s, hs⟩ := isConj_iff.mp
    (binary_involutions_isConj (eK (q xK)) (eK (q aK))
      (horder xK hxU hx) (horder aK haU ha))
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
    ((closureU Z ZS).subgroupOf (residualK Z)) (eK.symm s)
  let y : residualK Z := k * xK * k⁻¹
  have hyq : q y = q aK := by
    apply eK.injective
    change eK (q (k * xK * k⁻¹)) = _
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hk,
      eK.apply_symm_apply]
    exact hs
  let u : G := (a : G)⁻¹ * (y : G)
  have hu : u ∈ closureU Z ZS := by
    have he : q (aK⁻¹ * y) = 1 := by rw [map_mul, map_inv, hyq, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (aK⁻¹ * y)).mp he
  have hay : (a : G) * u = (y : G) := by dsimp [u]; group
  have hy2 : ((y : residualK Z) : G) ^ 2 = 1 := by
    change ((k : G) * x * (k : G)⁻¹) ^ 2 = 1
    calc
      _ = MulAut.conj (k : G) (x ^ 2) := (map_pow (MulAut.conj (k : G)) x 2).symm
      _ = 1 := by rw [show x ^ 2 = 1 from hx ▸ pow_orderOf_eq_one x, map_one]
  refine ⟨u, mem_fixedLift_of_involution_mul a (ha ▸ pow_orderOf_eq_one (a : G))
    ⟨u, hu⟩ (by simpa only [hay] using hy2) (quotient_square_eq_one hcenter), ?_⟩
  exact ⟨k, hKH k.property, hay.symm⟩

/-- A fixed-lift representative lies in the local product used by the parent assembly. -/
theorem outside_conjugate_localProduct
    [IsExtraspecial 2 (closureU Z ZS)]
    [((closureU Z ZS).subgroupOf (residualK Z)).Normal]
    (hKH : residualK Z ≤ centralizerH Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (eK : (residualK Z ⧸ (closureU Z ZS).subgroupOf (residualK Z)) ≃* Matrix.PSL3Two.SL)
    (V : Subgroup G) (a : centralizerH Z) (haV : (a : G) ∈ V)
    (haK : (a : G) ∈ residualK Z) (haU : (a : G) ∉ closureU Z ZS)
    (ha : orderOf (a : G) = 2) (x : G)
    (hxK : x ∈ residualK Z) (hxU : x ∉ closureU Z ZS) (hx : orderOf x = 2) :
    ∃ y ∈ fixedLift Z ZS a ⊔ V, ConjugateBy (centralizerH Z) x y := by
  obtain ⟨u, hu, hconj⟩ := outside_conjugate_fixedLift hKH hcenter eK a haK haU ha x hxK hxU hx
  exact ⟨(a : G) * u, (fixedLift Z ZS a ⊔ V).mul_mem ((show V ≤ fixedLift Z ZS a ⊔ V from le_sup_right) haV)
    ((show fixedLift Z ZS a ≤ fixedLift Z ZS a ⊔ V from le_sup_left) hu), hconj⟩

/-- Choose one actual involution in V−U and use it for every outside residual
involution. The quotient equivalence is the genuine earlier K/U recognition. -/
theorem exists_outside_representative
    [IsExtraspecial 2 (closureU Z ZS)]
    [((closureU Z ZS).subgroupOf (residualK Z)).Normal]
    (hKH : residualK Z ≤ centralizerH Z)
    (hcenter : Z.subgroupOf (closureU Z ZS) = center (closureU Z ZS))
    (eK : (residualK Z ⧸ (closureU Z ZS).subgroupOf (residualK Z)) ≃* Matrix.PSL3Two.SL)
    (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hVK : V ≤ residualK Z) (hVU : ¬ V ≤ closureU Z ZS) :
    ∃ a : centralizerH Z, (a : G) ∈ V ∧ (a : G) ∉ closureU Z ZS ∧
      orderOf (a : G) = 2 ∧
      ∀ x ∈ residualK Z, x ∉ closureU Z ZS → orderOf x = 2 →
        ∃ u ∈ fixedLift Z ZS a, ConjugateBy (centralizerH Z) x ((a : G) * u) := by
  obtain ⟨a, haV, haU, ha⟩ := exists_involution_in_V_outside_U V hVU
  refine ⟨⟨a, hKH (hVK haV)⟩, haV, haU, ha, ?_⟩
  intro x hxK hxU hx
  exact outside_conjugate_fixedLift hKH hcenter eK _ (hVK haV) haU ha x hxK hxU hx

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial
