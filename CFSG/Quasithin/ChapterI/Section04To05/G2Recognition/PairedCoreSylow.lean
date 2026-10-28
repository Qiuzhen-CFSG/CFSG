module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PairedCoreDisplacement
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The paired cubic extensions cannot both be Sylow

If the marked cores D and E have order 27, put K=D ∩ E and
R=D⟨y⟩, S=E⟨x⟩. Both extensions have order 81. Their derived subgroups
are K, whereas their centers are ⟨x⟩K and ⟨y⟩K respectively. Every line
in the latter center other than K is conjugate to ⟨y⟩, by the actual
surjective displacement action of D. Thus a conjugacy R→S would carry
⟨x⟩ to a line conjugate to ⟨y⟩, contrary to marked factor nonconjugacy.
Sylow conjugacy now forces 3^5 to divide the ambient order.

Together with the previously checked core-order alternatives this gives
3^3 ∣ |G| → 3^5 ∣ |G|. This excludes Sylow order 81, not the whole
order-27-core branch: a larger ambient Sylow subgroup remains possible
at this stage. The Sylow-nine case and Atlas recognition remain open.

Source: Aschbacher–Smith I.4.5, printed p.417. This replaces the part of
Fong §6C's Sylow-center argument requiring q>3 with the actual derived
line and displacement geometry at q=3. `Chapter14PairedCoreSylow` supplies
the original SourceLocalData consumer.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
open scoped commutatorElement

private theorem core_extension_setup (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    let D := cubicOddCore c t.x
    let Y := zpowers ((t.y:c.H):G)
    let K := D ⊓ cubicOddCore (swapFactors c) t.y
    let R := D ⊔ Y
    Nat.card R=81 ∧ Disjoint D Y ∧ Y ≤ normalizer (D:Set G) ∧
      centerIn R=zpowers ((t.x:c.H):G) ⊔ K := by
  let D := cubicOddCore c t.x
  let Y := zpowers ((t.y:c.H):G)
  let K := D ⊓ cubicOddCore (swapFactors c) t.y
  let R := D ⊔ Y
  let F := D ⊓ Subgroup.centralizer (Y:Set G)
  let : IsElementaryAbelian 3 D := t.left_oddCore_twentySeven_elementary hc
  have hYL : Y ≤ c.H₂.map c.H.subtype := zpowers_le.mpr
    (mem_map_of_mem c.H.subtype t.y.property)
  have hYC : Y ≤ cubicCentralizer c t.x := hYL.trans (opposite_factor_le_cubic_centralizer c t.x)
  have hn : Y ≤ normalizer (D:Set G) := hYC.trans
    ((cubicCentralizer c t.x).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 (cubicCentralizer c t.x))))
  have hd : Disjoint D Y := disjoint_iff.mpr (bot_unique
    ((inf_le_inf_left D hYL).trans (cubic_oddCore_inf_factor c t.x).le))
  have hZ : centerIn R=F := by
    apply le_antisymm
    · intro z hz
      have hzD : z ∈ D := by
        change z ∈ cubicOddCore c t.x
        rw [←t.left_oddCore_twentySeven_selfCentralizing hc]
        exact (centralizer_le (show D ≤ R from le_sup_left)) hz.2
      exact ⟨hzD,(centralizer_le (show Y ≤ R from le_sup_right)) hz.2⟩
    · intro z hz
      refine ⟨(le_sup_left:D≤R) hz.1,?_⟩
      have hD : D ≤ Subgroup.centralizer ({z}:Set G) := by
        intro d hd
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mul_comm' (⟨d,hd⟩:D) ⟨z,hz.1⟩))
      have hY : Y ≤ Subgroup.centralizer ({z}:Set G) := by
        intro y hy
        exact mem_centralizer_singleton_iff.mpr (hz.2 y hy)
      intro r hr
      exact mem_centralizer_singleton_iff.mp ((sup_le hD hY) hr)
  refine ⟨?_,hd,hn,hZ.trans t.left_oddCore_fixed_decomposition⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint D Y hn hd,hc,
    Nat.card_zpowers,orderOf_coe,orderOf_coe,t.y_order]

theorem left_core_extension_derived (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    let R := cubicOddCore c t.x ⊔ zpowers ((t.y:c.H):G)
    ⁅R,R⁆=cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y := by
  let D := cubicOddCore c t.x
  let Y := zpowers ((t.y:c.H):G)
  let K := D ⊓ cubicOddCore (swapFactors c) t.y
  let R := D ⊔ Y
  let : IsElementaryAbelian 3 D := t.left_oddCore_twentySeven_elementary hc
  obtain ⟨hR,hd,hn,hZ⟩ := t.core_extension_setup hc
  have hKZ : K ≤ centerIn R := hZ ▸ le_sup_right
  have hKR : K ≤ R := inf_le_left.trans le_sup_left
  have hRC : R ≤ Subgroup.centralizer (K:Set G) :=
    le_centralizer_iff.mp (hKZ.trans inf_le_right)
  have hRN : R ≤ normalizer (K:Set G) := hRC.trans (Subgroup.centralizer_le_normalizer _)
  let W := K.subgroupOf R
  let : W.Normal := normal_subgroupOf_of_le_normalizer hRN
  let q := QuotientGroup.mk' W
  let y : R := ⟨((t.y:c.H):G),mem_sup_right (mem_zpowers _)⟩
  have hcomm (d : D) : Commute (q y) (q (inclusion (show D≤R from le_sup_left) d)) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (t.left_displacement_mem_intersection hc d)
  have hYD : ⁅Y,D⁆ ≤ K := by
    apply commutator_le.mpr
    intro a ha d hd
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp ha
    have hh := (hcomm ⟨d,hd⟩).zpow_left n
    have hm := (QuotientGroup.eq_one_iff _).mp
      (show q ⁅y^n,inclusion (show D≤R from le_sup_left) ⟨d,hd⟩⁆=1 by
        rw [map_commutatorElement,map_zpow]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hh.eq)
    exact hm
  have hDD : ⁅D,D⁆ ≤ K := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr D.le_centralizer]
    exact bot_le
  have hYY : ⁅Y,Y⁆ ≤ K := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr Y.le_centralizer]
    exact bot_le
  have hDR : ⁅D,R⁆ ≤ K := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal R D Y D K hRN le_sup_left le_sup_right hDD hYD
  have hYR : ⁅Y,R⁆ ≤ K := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal R D Y Y K hRN le_sup_left le_sup_right
      (by rw [commutator_comm];exact hYD) hYY
  have hle : ⁅R,R⁆ ≤ K :=
    commutator_sup_le_of_relative_normal R D Y R K hRN le_sup_left le_sup_right hDR hYR
  have hne : ⁅R,R⁆≠⊥ := by
    intro he
    have hcommR := commutator_eq_bot_iff_le_centralizer.mp he
    have hyD : ((t.y:c.H):G) ∈ D := by
      change ((t.y:c.H):G) ∈ cubicOddCore c t.x
      rw [←t.left_oddCore_twentySeven_selfCentralizing hc]
      exact (centralizer_le (show D ≤ R from le_sup_left)) (hcommR y.property)
    have hy1 : ((t.y:c.H):G)=1 := mem_bot.mp
      (disjoint_iff.mp hd ▸ (show ((t.y:c.H):G) ∈ D ⊓ Y from ⟨hyD,mem_zpowers _⟩))
    have ho := t.y_order
    have hey : t.y=1 := Subtype.ext (Subtype.ext hy1)
    rw [hey,orderOf_one] at ho
    omega
  have hkc : Nat.card K=3 := t.oddCore_intersection_card_of_twentySeven hc
  have hdiv : Nat.card (⁅R,R⁆:Subgroup G) ∣ 3 := hkc ▸ card_dvd_of_le hle
  have hcard : Nat.card (⁅R,R⁆:Subgroup G)=3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h|h
    · exact (hne ((card_eq_one.mp h))).elim
    · exact h
  exact eq_of_le_of_card_ge hle (by rw [hkc,hcard])
private theorem core_center_line_conjugate (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27)
    (u : G) (hu : u ∈ zpowers ((t.y:c.H):G) ⊔
      (cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y))
    (hne : u ∉ cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y) :
    ∃ d : G, (zpowers u).map (MulAut.conj d).toMonoidHom=zpowers ((t.y:c.H):G) := by
  classical
  let Y := zpowers ((t.y:c.H):G)
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  have hKY : K ≤ Subgroup.centralizer (Y:Set G) := by
    change K ≤ Subgroup.centralizer (zpowers ((t.y:c.H):G):Set G)
    rw [zpowers_eq_closure,centralizer_closure]
    exact inf_le_right.trans (map_subtype_le _)
  have hn : K ≤ normalizer (Y:Set G) := hKY.trans (Subgroup.centralizer_le_normalizer _)
  change u ∈ (↑(Y ⊔ K):Set G) at hu
  rw [coe_mul_of_right_le_normalizer_left Y K hn] at hu
  obtain ⟨a,ha,k,hk,he⟩ := hu
  have hy3 : orderOf ((t.y:c.H):G)=3 := by rw [orderOf_coe,orderOf_coe,t.y_order]
  change a ∈ zpowers ((t.y:c.H):G) at ha
  rw [mem_zpowers_iff_mem_range_orderOf,hy3] at ha
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
  have hi3 : i<3 := Finset.mem_range.mp hi
  interval_cases i
  · simp only [pow_zero,one_mul] at he
    exact (hne (he ▸ hk)).elim
  · simp only [pow_one] at he
    obtain ⟨d,_,hd⟩ := t.left_intersection_conjugate hc k hk
    refine ⟨d⁻¹,?_⟩
    have hdu : MulAut.conj d ((t.y:c.H):G)=u := hd.trans he
    rw [MonoidHom.map_zpowers]
    have hback : MulAut.conj d⁻¹ u=((t.y:c.H):G) := by
      rw [←hdu]
      change d⁻¹*(d*((t.y:c.H):G)*d⁻¹)*(d⁻¹)⁻¹=((t.y:c.H):G)
      group
    change zpowers (MulAut.conj d⁻¹ u)=zpowers ((t.y:c.H):G)
    rw [hback]
  · have hyinv : ((t.y:c.H):G)^2=(((t.y:c.H):G))⁻¹ := by
      apply mul_eq_one_iff_eq_inv.mp
      rw [←pow_succ]
      change ((t.y:c.H):G)^3=1
      rw [←hy3,pow_orderOf_eq_one]
    rw [hyinv] at he
    obtain ⟨d,_,hd⟩ := t.left_intersection_conjugate hc k⁻¹ (K.inv_mem hk)
    have hdu : MulAut.conj d (((t.y:c.H):G))⁻¹=u := by
      rw [map_inv,hd,mul_inv_rev,inv_inv]
      have hky := hKY hk ((t.y:c.H):G) (mem_zpowers _)
      have hi := (show Commute ((t.y:c.H):G) k from hky).inv_left.eq
      exact hi.symm.trans he
    refine ⟨d⁻¹,?_⟩
    rw [MonoidHom.map_zpowers]
    have hback : MulAut.conj d⁻¹ u=(((t.y:c.H):G))⁻¹ := by
      rw [←hdu]
      change d⁻¹*(d*((((t.y:c.H):G))⁻¹)*d⁻¹)*(d⁻¹)⁻¹=(((t.y:c.H):G))⁻¹
      group
    change zpowers (MulAut.conj d⁻¹ u)=zpowers ((t.y:c.H):G)
    rw [hback,zpowers_inv]

theorem core_extensions_not_conjugate (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) (g : G) :
    (cubicOddCore c t.x ⊔ zpowers ((t.y:c.H):G)).map (MulAut.conj g).toMonoidHom ≠
      cubicOddCore (swapFactors c) t.y ⊔ zpowers ((t.x:c.H):G) := by
  intro hmap
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let K := D ⊓ E
  let X := zpowers ((t.x:c.H):G)
  let Y := zpowers ((t.y:c.H):G)
  let R := D ⊔ Y
  let S := E ⊔ X
  have he : Nat.card E=27 := t.right_oddCore_twentySeven_of_left hc
  have hKR : ⁅R,R⁆=K := t.left_core_extension_derived hc
  have hKS : ⁅S,S⁆=K := by
    have h := t.swap.left_core_extension_derived he
    change ⁅S,S⁆=E ⊓ D at h
    simpa only [inf_comm] using h
  have hKmap : K.map (MulAut.conj g).toMonoidHom=K := by
    calc
      K.map (MulAut.conj g).toMonoidHom = (⁅R,R⁆).map (MulAut.conj g).toMonoidHom := by rw [hKR]
      _ = ⁅S,S⁆ := by rw [map_commutator,hmap]
      _ = K := hKS
  have hZR : centerIn R=X ⊔ K := (t.core_extension_setup hc).2.2.2
  have hZS : centerIn S=Y ⊔ K := by
    have h := (t.swap.core_extension_setup he).2.2.2
    change centerIn S=Y ⊔ (E ⊓ D) at h
    simpa only [inf_comm] using h
  have hxK : ((t.x:c.H):G) ∉ K := by
    intro hx
    have hbot := (cubic_oddCore_inf_factor (swapFactors c) t.y).le
      ⟨hx.2,mem_map_of_mem c.H.subtype t.x.property⟩
    have hx1 : t.x=1 := Subtype.ext (Subtype.ext (mem_bot.mp hbot))
    have ho := t.x_order
    rw [hx1,orderOf_one] at ho
    omega
  let u := MulAut.conj g ((t.x:c.H):G)
  change R.map (MulAut.conj g).toMonoidHom=S at hmap
  have hu : u ∈ Y ⊔ K := by
    rw [←hZS,←hmap,←centerIn_map_equiv,hZR]
    exact mem_map_of_mem _ (mem_sup_left (mem_zpowers _))
  have hune : u ∉ K := by
    intro huK
    rw [←hKmap] at huK
    exact hxK ((mem_map_iff_mem (MulAut.conj g).injective).mp huK)
  obtain ⟨d,hd⟩ := t.core_center_line_conjugate hc u hu hune
  apply cubic_lines_not_conjugate c t.x t.y t.x_order (d*g)
  rw [MonoidHom.map_zpowers] at hd ⊢
  convert hd using 1
  congr 1
  change (d*g)*((t.x:c.H):G)*(d*g)⁻¹=d*(g*((t.x:c.H):G)*g⁻¹)*d⁻¹
  group

theorem left_oddCore_twentySeven_fifth_power_dvd (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) : 3^5 ∣ Nat.card G := by
  by_contra hnot
  let R := cubicOddCore c t.x ⊔ zpowers ((t.y:c.H):G)
  let S := cubicOddCore (swapFactors c) t.y ⊔ zpowers ((t.x:c.H):G)
  have hr : Nat.card R=81 := (t.core_extension_setup hc).1
  have hs : Nat.card S=81 := (t.swap.core_extension_setup
    (t.right_oddCore_twentySeven_of_left hc)).1
  have hindex (A : Subgroup G) (hA : Nat.card A=81) : ¬3∣A.index := by
    intro hi
    apply hnot
    have hd := Nat.mul_dvd_mul_left 81 hi
    rw [←hA,A.card_mul_index,hA] at hd
    exact hd
  let P : Sylow 3 G := (IsPGroup.of_card (p:=3) (n:=4) hr).toSylow (hindex R hr)
  let Q : Sylow 3 G := (IsPGroup.of_card (p:=3) (n:=4) hs).toSylow (hindex S hs)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P Q
  exact t.core_extensions_not_conjugate hc g (congrArg Sylow.toSubgroup hg)

end CubicTorus

include c in
/-- The ambient three-part cannot be exactly 27 or 81. -/
theorem cubic_cube_dvd_fifth_power (hd : 3^3 ∣ Nat.card G) : 3^5 ∣ Nat.card G := by
  obtain ⟨t⟩ := exists_cubic_torus c
  rcases t.left_oddCore_orders with h|h|h
  · exact ((t.small_cores_iff_not_cube_dvd.mp ⟨h,t.oddCore_three_iff.mp h⟩) hd).elim
  · exact t.left_oddCore_twentySeven_fifth_power_dvd h
  · exact (by decide : 3^5 ∣ 3^6).trans (cubic_maximal_core_sixth_power_dvd c t.x t.x_order h)

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
