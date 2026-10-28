module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Elementary
public import Theory.ElementaryAbelian.ExtraspecialAbelianBound

/-!
# Centralizers of the elementary lift

The elementary base A has order 32 in extraspecial U of order 512, so it
attains the extraspecial abelian size bound and C_U(A)=A. Decomposing UD
as a subgroup product then gives C_{UD}(D)=D. Finally an element ai of D
outside A centralizing U would make i act as an inner automorphism of U;
this would force [U,i] into Z(U), contradicting |A|=32. Thus C_D(U)=⟨z⟩.
All centralizers and subtype maps are the actual ambient ones.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

/-- The order-32 elementary base attains the extraspecial size bound, and
therefore is its own centralizer inside U. -/
theorem liftBase_self_centralizer
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hUcard : Nat.card U = 512)
    (hA : IsElementaryAbelian 2 (liftBase U z i))
    (hAcard : Nat.card (liftBase U z i) = 32) :
    U ⊓ centralizer (liftBase U z i : Set G) = liftBase U z i := by
  let A := liftBase U z i
  have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
  have hAU : A ≤ U := sup_le
    (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)) hzU
  let : IsElementaryAbelian 2 A := hA
  let : IsElementaryAbelian 2 (A.subgroupOf U) := IsElementaryAbelian.subgroupOf hAU
  have hZA : center U ≤ A.subgroupOf U := by
    intro a ha
    exact (le_sup_right : zpowers z ≤ A) (hZ ▸ mem_map_of_mem U.subtype ha)
  have hc : centralizer (A.subgroupOf U : Set U) = A.subgroupOf U := by
    apply extraspecial_two_centralizer_eq_of_card_sq (A.subgroupOf U) hZA
    rw [Nat.card_congr (subgroupOfEquivOfLe hAU).toEquiv, hUcard, hAcard]
    norm_num
  apply le_antisymm
  · intro a ha
    have haC : (⟨a,ha.1⟩ : U) ∈ centralizer (A.subgroupOf U : Set U) := by
      intro b hb
      exact Subtype.ext (ha.2 b hb)
    rw [hc] at haC
    exact haC
  · exact le_inf hAU A.le_centralizer

/-- The elementary lift is self-centralizing in UD: its U-part centralizes
A and hence belongs to A by the extraspecial size bound. -/
theorem centralizerLift_self_centralizer
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hUcard : Nat.card U = 512)
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hA : IsElementaryAbelian 2 (liftBase U z i))
    (hAcard : Nat.card (liftBase U z i) = 32) :
    (U ⊔ centralizerLift U z i) ⊓ centralizer (centralizerLift U z i : Set G) =
      centralizerLift U z i := by
  let D := centralizerLift U z i
  let A := liftBase U z i
  let : IsElementaryAbelian 2 D := hD
  have hAD : A ≤ D := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hcA := liftBase_self_centralizer U z i hZ hiU hUcard hA hAcard
  have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
  have hBU : ⁅U,zpowers i⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)
  have hDU : D ≤ normalizer (U : Set G) := sup_le
    (sup_le (hBU.trans U.le_normalizer) (zpowers_le.mpr hiU)) (hzU.trans U.le_normalizer)
  apply le_antisymm
  · rintro x ⟨hxUD,hxC⟩
    have hxprod : x ∈ (U : Set G) * (D : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left U D hDU]
      exact hxUD
    obtain ⟨u,hu,d,hd,rfl⟩ := hxprod
    have huC : u ∈ centralizer (D : Set G) := by
      have hh := (centralizer (D : Set G)).mul_mem hxC
        ((centralizer (D : Set G)).inv_mem (D.le_centralizer hd))
      simpa only [mul_inv_cancel_right] using hh
    have huA : u ∈ A := by
      have hh : u ∈ U ⊓ centralizer (A : Set G) := ⟨hu, centralizer_le hAD huC⟩
      rwa [hcA] at hh
    exact D.mul_mem (hAD huA) hd
  · exact le_inf le_sup_right D.le_centralizer

/-- An element of D outside A cannot centralize U: otherwise i acts on U
as an inner automorphism, forcing its moved image into the central line. -/
theorem centralizerLift_fixed_line
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hAcard : Nat.card (liftBase U z i) = 32) :
    centralizerLift U z i ⊓ centralizer (U : Set G) = zpowers z := by
  classical
  let D := centralizerLift U z i
  let A := liftBase U z i
  let : IsElementaryAbelian 2 D := hD
  have hAD : A ≤ D := sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hID : zpowers i ≤ D := le_sup_right.trans le_sup_left
  have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
  have hAU : A ≤ U := sup_le
    (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)) hzU
  have hUU : ⁅U,U⁆ ≤ zpowers z := by
    have hh := map_mono (f := U.subtype)
      (IsExtraspecial.quotient_elementary_abelian 2 U).commutator_le_center_of_central_quotient
    simpa only [map_subtype_commutator, hZ] using hh
  have hcases {a : G} (ha : a ∈ zpowers i) : a = 1 ∨ a = i := by
    rw [mem_zpowers_iff_mem_range_orderOf, hi] at ha
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ha
    have hn2 := Finset.mem_range.mp hn
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> simp
  have hDA : D = A ⊔ zpowers i := by
    dsimp only [D,A,centralizerLift,liftBase]
    ac_rfl
  have hiA : zpowers i ≤ normalizer (A : Set G) :=
    ((hID.trans D.le_centralizer).trans (centralizer_le hAD)).trans (_root_.centralizer_le_normalizer _)
  apply le_antisymm
  · rintro d ⟨hd,hc⟩
    have hdprod : d ∈ (A : Set G) * (zpowers i : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A (zpowers i) hiA, ← hDA]
      exact hd
    obtain ⟨a,ha,b,hb,rfl⟩ := hdprod
    have hb1 : b = 1 := by
      rcases hcases hb with he | he
      · exact he
      · subst b
        exfalso
        have hcomm (u : G) (hu : u ∈ U) : ⁅u,i⁆ ∈ zpowers z := by
          have hdcomm : Commute u (a*i) := hc u hu
          have he : ⁅u,i⁆ = ⁅u,a⁻¹⁆ := by
            calc
              ⁅u,i⁆ = ⁅u,a⁻¹ * (a*i)⁆ := by congr 1; group
              _ = ⁅u,a⁻¹⁆ := by
                rw [commutatorElement_mul_right_eq_mul_conj, hdcomm.commutator_eq]
                group
          rw [he]
          exact hUU (commutator_mem_commutator hu (U.inv_mem (hAU ha)))
        have hBZ : ⁅U,zpowers i⁆ ≤ zpowers z := by
          apply commutator_le.mpr
          intro u hu b hb
          rcases hcases hb with he | he
          · rw [he]
            simp
          · rw [he]
            exact hcomm u hu
        have hAZ : A = zpowers z := sup_eq_right.mpr hBZ
        have hh : Nat.card A = 2 := by rw [hAZ,Nat.card_zpowers,hz]
        change Nat.card A = 32 at hAcard
        omega
    subst b
    simp only [mul_one] at hc ⊢
    rw [← hZ]
    refine ⟨⟨a,hAU ha⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro u
    exact Subtype.ext (hc u u.property)
  · refine le_inf le_sup_right ?_
    rw [← hZ]
    rintro _ ⟨a,ha,rfl⟩ u hu
    exact congrArg Subtype.val (mem_center_iff.mp ha (⟨u,hu⟩ : U))

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
