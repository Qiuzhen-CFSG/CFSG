module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.QuotientFusion.Fusion
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Involution geometry inside each transfer kernel

The transfer intersection identifies the E-image inside every kernel M.
The cubic subgroup X₁ maps into M because its elements have odd order.
Its transitive action on E# and Sylow conjugacy give one involution class
in M. Intersecting the previously computed quotient centralizer with M
identifies C_M(z*) with the E-image, giving an actual DihedralGroup 2
equivalence via the Klein four-group classification.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), printed p.260.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} {t : G}
namespace LocalFrame
variable (F : LocalFrame D t) (L : LocalCensus D) (ht : orderOf t = 2)
variable (K : TransferKernel (F.quotientTransfer L ht))

theorem quotient_kernel_intersection :
    K.M ⊓ (F.quotientSylow : Subgroup (CentralQuotient t)) = quotientImage F.E := by
  have h := congrArg (fun B : Subgroup F.quotientSylow =>
    B.map (F.quotientSylow : Subgroup (CentralQuotient t)).subtype) K.intersection
  exact (subgroupOf_map_subtype K.M _).symm.trans (h.trans F.quotientClosed_eq)

theorem quotient_E_le_kernel : quotientImage F.E ≤ K.M := by
  rw [← F.quotient_kernel_intersection L ht K]
  exact inf_le_left

theorem quotient_cubic_mem_kernel (x : F.X1) :
    quotientMap t ⟨(x : G), F.X1_le x.property⟩ ∈ K.M := by
  let xc : involutionCentralizer t := ⟨(x : G), F.X1_le x.property⟩
  let q := quotientMap t xc
  have hx3 : xc ^ 3 = 1 := by
    apply Subtype.ext
    have h := pow_card_eq_one' (x := x)
    rw [F.X1_card] at h
    exact congrArg (fun y : F.X1 => (y : G)) h
  have hq3 : q ^ 2 * q = 1 := by
    rw [← pow_succ, ← map_pow, hx3, map_one]
  have hsq := K.M.sq_mem_of_index_two K.index q
  rw [eq_inv_of_mul_eq_one_left hq3] at hsq
  exact K.M.inv_mem_iff.mp hsq

def quotientKernelSource : K.M :=
  ⟨F.quotientSource, F.quotient_E_le_kernel L ht K F.quotientSource_mem⟩

theorem quotientKernelSource_involution : GorensteinWalter.IsInvolution
    (F.quotientKernelSource L ht K) := by
  refine ⟨fun h => F.quotientSource_ne_one ht (congrArg Subtype.val h), ?_⟩
  apply Subtype.ext
  exact (orderOf_eq_prime_iff.mp (F.quotientSource_order ht)).1

theorem quotient_kernel_centralizer :
    centralizer ({F.quotientKernelSource L ht K} : Set K.M) =
      (quotientImage F.E).subgroupOf K.M := by
  ext x
  rw [mem_centralizer_singleton_iff]
  have hS : ((x : K.M) : CentralQuotient t) ∈
      (F.quotientSylow : Subgroup (CentralQuotient t)) ↔
      ((x : K.M) : CentralQuotient t) ∈ quotientImage F.E := by
    rw [← F.quotient_kernel_intersection L ht K, mem_inf]
    exact (and_iff_right x.property).symm
  change (x * F.quotientKernelSource L ht K = F.quotientKernelSource L ht K * x) ↔
    (x : CentralQuotient t) ∈ quotientImage F.E
  rw [← hS, ← F.quotientSource_centralizer L ht, mem_centralizer_singleton_iff]
  exact Subtype.ext_iff

theorem quotient_kernel_centralizer_equiv : Nonempty
    (centralizer ({F.quotientKernelSource L ht K} : Set K.M) ≃* DihedralGroup 2) := by
  let B : Subgroup (CentralQuotient t) := quotientImage F.E
  have hc : Nat.card (B.subgroupOf K.M) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (F.quotient_E_le_kernel L ht K)).toEquiv).trans
      (F.quotient_E_card ht)
  have he : IsElementaryAbelian 2 B := by
    refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
    · exact isMulCommutative_iff.mpr fun a b => Subtype.ext (by
        let : IsElementaryAbelian 2 F.quotientSylow := F.quotientSylow_elementary
        exact setLike_mul_comm (F.quotient_E_le a.property) (F.quotient_E_le b.property))
    · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply Subtype.ext
      let : IsElementaryAbelian 2 F.quotientSylow := F.quotientSylow_elementary
      exact elemPow_eq_one_of_isElementaryAbelian _ (F.quotient_E_le x.property)
  let : IsElementaryAbelian 2 B := he
  let : IsElementaryAbelian 2 (B.subgroupOf K.M) :=
    IsElementaryAbelian.subgroupOf (F.quotient_E_le_kernel L ht K)
  let : Nontrivial (B.subgroupOf K.M) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; decide)
  let : IsKleinFour (B.subgroupOf K.M) := ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := B.subgroupOf K.M) (G₂ := DihedralGroup 2)
  exact ⟨(MulEquiv.subgroupCongr (F.quotient_kernel_centralizer L ht K)).trans e⟩

theorem quotient_kernel_involutions_conjugate (u : K.M) (hu : GorensteinWalter.IsInvolution u) :
    ∃ g : K.M, g * u * g⁻¹ = F.quotientKernelSource L ht K := by
  let : K.M.Normal := K.normal
  obtain ⟨P, hP⟩ := F.quotientSylow.exists_subgroupOf_eq_of_normal K.M
  have huo : orderOf u = 2 ^ 1 := by
    simpa using (orderOf_eq_prime hu.2 hu.1 : orderOf u = 2)
  obtain ⟨v, huv⟩ := P.exists_isConj_of_orderOf_eq_prime_pow huo
  have hvS : ((v : K.M) : CentralQuotient t) ∈
      (F.quotientSylow : Subgroup (CentralQuotient t)) := by
    have h : (v : K.M) ∈ (P : Subgroup K.M) := v.property
    rw [hP] at h
    exact h
  have hvE : ((v : K.M) : CentralQuotient t) ∈ quotientImage F.E := by
    rw [← F.quotient_kernel_intersection L ht K]
    exact ⟨(v : K.M).property, hvS⟩
  obtain ⟨e, he, heq⟩ := mem_map.mp hvE
  have hvne : (v : K.M) ≠ 1 := fun h => hu.1 (isConj_one_left.mp (h ▸ huv))
  have hene : (e : G) ≠ 1 := by
    intro h
    have h1 : e = 1 := Subtype.ext h
    have hv1 : ((v : K.M) : CentralQuotient t) = 1 := by
      rw [← heq, h1, map_one]
    exact hvne (Subtype.ext hv1)
  obtain ⟨x, hx⟩ := F.X1_transitive e he hene D.z F.z_mem
    (orderOf_eq_prime_iff.mp D.localType.involution).2
  let xc : involutionCentralizer t := ⟨(x : G), F.X1_le x.property⟩
  let xM : K.M := ⟨quotientMap t xc, F.quotient_cubic_mem_kernel L ht K x⟩
  have hxv : xM * (v : K.M) * xM⁻¹ = F.quotientKernelSource L ht K := by
    apply Subtype.ext
    change quotientMap t xc * ((v : K.M) : CentralQuotient t) * (quotientMap t xc)⁻¹ =
      quotientMap t F.quotientSourceLift
    rw [← heq, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg (quotientMap t) (Subtype.ext hx)
  exact isConj_iff.mp (huv.trans (isConj_iff.mpr ⟨xM, hxv⟩))

theorem quotient_kernel_local : Nonempty (DihedralInvolutionCentralizerHypotheses K.M 2) := by
  refine ⟨{
    two_le := le_rfl
    z := F.quotientKernelSource L ht K
    involution := F.quotientKernelSource_involution L ht K
    involutions_conjugate := F.quotient_kernel_involutions_conjugate L ht K
    centralizer_equiv := ?_ }⟩
  simpa using F.quotient_kernel_centralizer_equiv L ht K
end LocalFrame
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
