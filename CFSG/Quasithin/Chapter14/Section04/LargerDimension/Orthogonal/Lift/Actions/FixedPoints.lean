module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Centralizers

/-!
# Fixed points of elements outside the lift base

Write A=[U,i]⟨z⟩ and D=A⟨i⟩. If ai centralizes an element u of U,
then [u,i] is central. Applied to C_U(ai), U and ⟨i⟩, the three-subgroups
lemma shows that C_U(ai) centralizes [U,i], and hence A. The already
proved identity C_U(A)=A now gives C_D(u)≤A for every u∈U\A.
The centralizers are literal ambient intersections, and the elementary
lift and its cardinalities are supplied by Lift/Elementary.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

/-- No element of the other coset of A in D centralizes an element of U outside A. -/
theorem centralizerLift_element_centralizer_le_base
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hiz : i ∈ centralizer ({z} : Set G))
    (hUcard : Nat.card U = 512)
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hA : IsElementaryAbelian 2 (liftBase U z i))
    (hAcard : Nat.card (liftBase U z i) = 32)
    (u : G) (hu : u ∈ U) (huA : u ∉ liftBase U z i) :
    centralizerLift U z i ⊓ centralizer ({u} : Set G) ≤ liftBase U z i := by
  classical
  let A := liftBase U z i
  let D := centralizerLift U z i
  let : IsElementaryAbelian 2 D := hD
  have hAD : A ≤ D := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hID : zpowers i ≤ D := le_sup_right.trans le_sup_left
  have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
  have hAU : A ≤ U := sup_le
    (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)) hzU
  have hzCU : zpowers z ≤ centralizer (U : Set G) := by
    rw [← hZ]
    rintro _ ⟨a,ha,rfl⟩ v hv
    exact congrArg Subtype.val (mem_center_iff.mp ha (⟨v,hv⟩ : U))
  have hZi : zpowers z ≤ centralizer (zpowers i : Set G) := by
    apply le_centralizer_iff.mp
    apply zpowers_le.mpr
    simpa only [zpowers_eq_closure, centralizer_closure] using hiz
  have hUU : ⁅U,U⁆ ≤ zpowers z := by
    have hh := map_mono (f := U.subtype)
      (IsExtraspecial.quotient_elementary_abelian 2 U).commutator_le_center_of_central_quotient
    simpa only [map_subtype_commutator, hZ] using hh
  have hcases {b : G} (hb : b ∈ zpowers i) : b = 1 ∨ b = i := by
    rw [mem_zpowers_iff_mem_range_orderOf, hi] at hb
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hb
    have hn2 := Finset.mem_range.mp hn
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hDA : D = A ⊔ zpowers i := by
    dsimp only [D,A,centralizerLift,liftBase]
    ac_rfl
  have hiA : zpowers i ≤ normalizer (A : Set G) :=
    ((hID.trans D.le_centralizer).trans (centralizer_le hAD)).trans (_root_.centralizer_le_normalizer _)
  rintro d ⟨hd,hdu⟩
  have hdprod : d ∈ (A : Set G) * (zpowers i : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left A (zpowers i) hiA, ← hDA]
    exact hd
  obtain ⟨a,ha,b,hb,rfl⟩ := hdprod
  rcases hcases hb with he | he
  · subst b
    change a * 1 ∈ A
    rw [mul_one]
    exact ha
  · subst b
    exfalso
    let C := U ⊓ centralizer ({a*i} : Set G)
    have hci : ⁅C,zpowers i⁆ ≤ zpowers z := by
      apply commutator_le.mpr
      intro c hc b hb
      rcases hcases hb with he | he
      · rw [he]
        simpa only [commutatorElement_one_right] using (zpowers z).one_mem
      · rw [he]
        have hcomm : Commute c (a*i) := mem_centralizer_singleton_iff.mp hc.2
        have he : ⁅c,i⁆ = ⁅c,a⁻¹⁆ := by
          calc
            ⁅c,i⁆ = ⁅c,a⁻¹ * (a*i)⁆ := by congr 1; group
            _ = ⁅c,a⁻¹⁆ := by
              rw [commutatorElement_mul_right_eq_mul_conj, hcomm.commutator_eq]
              group
        rw [he]
        exact hUU (commutator_mem_commutator hc.1 (U.inv_mem (hAU ha)))
    have hBC : ⁅⁅U,zpowers i⁆,C⁆ = ⊥ := by
      apply commutator_commutator_eq_bot_of_rotate
      · apply commutator_eq_bot_iff_le_centralizer.mpr
        rw [commutator_comm]
        exact hci.trans hzCU
      · apply commutator_eq_bot_iff_le_centralizer.mpr
        exact ((commutator_mono inf_le_left le_rfl).trans hUU).trans hZi
    have hAC : A ≤ centralizer (C : Set G) :=
      sup_le (commutator_eq_bot_iff_le_centralizer.mp hBC)
        (hzCU.trans (centralizer_le inf_le_left))
    have huC : u ∈ C := ⟨hu, mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp hdu).symm⟩
    have huCA : u ∈ U ⊓ centralizer (A : Set G) :=
      ⟨hu, le_centralizer_iff.mp hAC huC⟩
    rw [liftBase_self_centralizer U z i hZ hiU hUcard hA hAcard] at huCA
    exact huA huCA

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
