module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CommonLineClassTwo
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.GroupAction.PrimeOrderPoints
public import Theory.GroupAction.QuaternionEight
public import Theory.GroupTheory.PrimeSubgroupInvolution

/-!
# Excluding Sylow order 243 for the marked order-27 cores

Suppose P = O(C_G(D ∩ E)) has order 243. The preceding calculation makes
P class two, hence P normalizes D. The action of N_G(D) on D is faithful
modulo D, and |Aut(D)| divides |GL₃(3)| = 11232. The stabilizer of the
original cubic line X has order 27·48. Since there are thirteen lines in
D and the ambient Sylow order is 243, the orbit of X has size three or six.
The opposite quaternion subgroup therefore has its central involution z
acting trivially on this orbit.

For p in P, write x^p = kx with k in Z(P) = D ∩ E. The original z fixes
x and inverts k. Its normalization of every conjugate of X forces k=1.
Thus x centralizes P, contradicting the disjointness of X and D ∩ E.
Only Sylow order 729 remains in this branch. In the full configuration,
3³ dividing |G| now implies 3⁶ dividing |G|.

Source hypotheses: Aschbacher–Smith I.4(G1)–(G2), printed p.417. This is
an elementary exceptional-q=3 branch argument, using the actual H and M
geometry established by the imported modules. It excludes Sylow order
243, not subgroups of that order. The order-27-core branch with Sylow
order 729, the Sylow-nine branch, and the Atlas recognition equivalence
remain open. `Chapter14CommonLine243Exclusion` gives the literal consumer.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

omit [Finite G] in
private theorem line_normalizer_le_core_normalizer (t : CubicTorus c) :
    cubicNormalizer c t.x ≤ normalizer (cubicOddCore c t.x:Set G) := by
  have hh := normalizer_le_normalizer_centralizer (zpowers ((t.x:c.H):G))
  have he : Subgroup.centralizer (zpowers ((t.x:c.H):G):Set G)=cubicCentralizer c t.x := by
    rw [zpowers_eq_closure,centralizer_closure]; rfl
  rw [he] at hh
  exact hh.trans (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 _))

private theorem core_line_orbit_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27)
    (hdiv : 243∣Nat.card (normalizer (cubicOddCore c t.x:Set G)))
    (hnot : ¬729∣Nat.card G) :
    let D := cubicOddCore c t.x
    let X : Subgroup.OrderPoints 3 D := ⟨cubicCoreLine c t.x,cubicCoreLine_card c t.x t.x_order⟩
    Nat.card (Subgroup.OrderPoints.orbit D.normalizerMonoidHom X)=3 ∨
      Nat.card (Subgroup.OrderPoints.orbit D.normalizerMonoidHom X)=6 := by
  let D := cubicOddCore c t.x
  let N := normalizer (D:Set G)
  let X : Subgroup.OrderPoints 3 D := ⟨cubicCoreLine c t.x,cubicCoreLine_card c t.x t.x_order⟩
  let : IsElementaryAbelian 3 D := t.left_oddCore_twentySeven_elementary hc
  let ρ := D.normalizerMonoidHom
  let U := Subgroup.OrderPoints.stabilizer ρ X
  let O := Subgroup.OrderPoints.orbit ρ X
  have hU : U=(cubicNormalizer c t.x).subgroupOf N := by
    ext g
    rw [Subgroup.OrderPoints.mem_stabilizer_iff]
    change (cubicCoreLine c t.x).map (ρ g).toMonoidHom=cubicCoreLine c t.x ↔
      (g:G)∈cubicNormalizer c t.x
    constructor
    · intro he
      have hm := congrArg (fun A : Subgroup D => A.map D.subtype) he
      rw [map_map] at hm
      have hh : D.subtype.comp (ρ g).toMonoidHom =
          (MulAut.conj (g:G)).toMonoidHom.comp D.subtype := rfl
      rw [hh,←map_map,cubicCoreLine,map_subgroupOf_eq_of_le
        (cubic_line_le_oddCore c t.x t.x_order)] at hm
      exact mem_normalizer_iff_map_conj_eq.mpr hm
    · intro hg
      apply map_injective D.subtype_injective
      rw [map_map]
      have hh : D.subtype.comp (ρ g).toMonoidHom =
          (MulAut.conj (g:G)).toMonoidHom.comp D.subtype := rfl
      rw [hh,←map_map,cubicCoreLine,map_subgroupOf_eq_of_le
        (cubic_line_le_oddCore c t.x t.x_order)]
      exact mem_normalizer_iff_map_conj_eq.mp hg
  have hUc : Nat.card U=1296 := by
    rw [hU,Nat.card_congr (subgroupOfEquivOfLe t.line_normalizer_le_core_normalizer).toEquiv,
      t.left_ambient_normalizer_card,hc]
  have hmul : Nat.card O * 1296=Nat.card N := by
    let := Subgroup.OrderPoints.action (p:=3) ρ
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N X)
    rw [Nat.card_prod] at hh
    change Nat.card O * Nat.card U=Nat.card N at hh
    rwa [hUc] at hh
  let : Finite (Subgroup.OrderPoints 3 D) := inferInstanceAs
    (Finite {A : Subgroup D // Nat.card A=3})
  have hbound : Nat.card O≤13 := by
    have hh := Nat.card_le_card_of_injective (Subtype.val:O→Subgroup.OrderPoints 3 D)
      Subtype.val_injective
    rwa [Subgroup.OrderPoints.card_thirteen hc] at hh
  have hker : Nat.card ρ.ker=27 := by
    rw [normalizerMonoidHom_ker,t.left_oddCore_twentySeven_selfCentralizing hc,
      Nat.card_congr (subgroupOfEquivOfLe D.le_normalizer).toEquiv,hc]
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p:=3) (n:=3) D (by rw [hc]; decide)
  have hAut : Nat.card (MulAut D)∣11232 := by
    have hd := card_dvd_of_injective f hf
    have he : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3))=11232 := by
      rw [Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ,ZMod.card]
    rwa [he] at hd
  have hN : Nat.card N∣27*11232 := by
    have he := ρ.ker.card_mul_index
    rw [hker,index_ker] at he
    rw [←he]
    exact Nat.mul_dvd_mul_left 27 (ρ.range.card_subgroup_dvd_card.trans hAut)
  have ho : Nat.card O∣234 := by
    rw [←hmul] at hN
    have hmul' : 1296*Nat.card O∣1296*234 := by simpa only [mul_comm,show 27*11232=234*1296 by decide] using hN
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0<1296) hmul'
  have hno : ¬9∣Nat.card O := by
    intro h
    apply hnot
    have hd : 729∣Nat.card O*1296 :=
      (by decide : 729∣9*1296).trans (Nat.mul_dvd_mul h (dvd_refl 1296))
    rw [hmul] at hd
    exact hd.trans N.card_subgroup_dvd_card
  have hthree : 3∣Nat.card O := by
    rw [←hmul] at hdiv
    have hd : 81*3∣81*(Nat.card O*16) := by
      convert hdiv using 1
      ring
    have he := Nat.dvd_of_mul_dvd_mul_left (by decide : 0<81) hd
    exact (Nat.Prime.dvd_mul Nat.prime_three).mp he |>.resolve_right (by decide)
  have hmem := Nat.mem_divisors.mpr ⟨ho,(by decide : 234≠0)⟩
  have he : Nat.divisors 234={1,2,3,6,9,13,18,26,39,78,117,234} := by decide
  simp only [he,Finset.mem_insert,Finset.mem_singleton] at hmem
  change Nat.card O=3 ∨ Nat.card O=6
  omega

private theorem core_line_conjugates_normalized (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27)
    (hdiv : 243∣Nat.card (normalizer (cubicOddCore c t.x:Set G)))
    (hnot : ¬729∣Nat.card G) (g : G) (hg : g∈normalizer (cubicOddCore c t.x:Set G)) :
    (t.z:G)∈normalizer (((zpowers ((t.x:c.H):G)).map (MulAut.conj g).toMonoidHom):Set G) := by
  let D := cubicOddCore c t.x
  let N := normalizer (D:Set G)
  let X : Subgroup.OrderPoints 3 D := ⟨cubicCoreLine c t.x,cubicCoreLine_card c t.x t.x_order⟩
  let ρ := D.normalizerMonoidHom
  let := Subgroup.OrderPoints.action (p:=3) ρ
  let O := MulAction.orbit N X
  let : Finite (Subgroup.OrderPoints 3 D) := inferInstanceAs
    (Finite {A : Subgroup D // Nat.card A=3})
  have hsmall : Nat.card O<8 := by
    rcases t.core_line_orbit_card hc hdiv hnot with h|h <;> change Nat.card O=_ at h <;> omega
  let Q := c.H₂.pCoreIn 2
  let e := factorCoreEquiv c c.H₂ c.H₂_model.some
  have hQN : Q.map c.H.subtype≤N :=
    (map_mono (c.H₂.pCoreIn_le 2)).trans
      ((opposite_factor_le_cubic_centralizer c t.x).trans
        ((cubicCentralizer c t.x).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 _))))
  let f : Q →* N := {
    toFun q := ⟨q,hQN (mem_map_of_mem c.H.subtype q.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let j := f.comp e.symm.toMonoidHom
  let : MulAction (QuaternionGroup 2) O := MulAction.compHom O j
  have hzQ : t.z∈Q := by
    have hh : t.z∈c.H₁⊓c.H₂ := t.central_line ▸ mem_zpowers t.z
    rw [←factor_core_intersection c] at hh
    exact hh.2
  let zQ : Q := ⟨t.z,hzQ⟩
  have hez : e zQ=QuaternionGroup.a 2 := QuaternionGroup.eq_a_two_of_orderOf_eq_two _
    ((e.orderOf_eq zQ).trans ((orderOf_coe zQ).symm.trans t.z_order))
  have hjz : ((j (QuaternionGroup.a 2):N):G)=(t.z:G) := by
    change (((e.symm (QuaternionGroup.a 2):Q):c.H):G)=(t.z:G)
    rw [←hez,e.symm_apply_apply]
  let w : O := ⟨(⟨g,hg⟩:N) • X,⟨⟨g,hg⟩,rfl⟩⟩
  have hh := QuaternionGroup.a_two_smul_eq_of_card_lt_eight hsmall w
  have hm := congrArg (fun v : O => v.val.val.map D.subtype) hh
  change (((X.val.map (ρ ⟨g,hg⟩).toMonoidHom).map
    (ρ (j (QuaternionGroup.a 2))).toMonoidHom).map D.subtype)=
      (X.val.map (ρ ⟨g,hg⟩).toMonoidHom).map D.subtype at hm
  have hmap (A : Subgroup D) (n : N) :
      (A.map (ρ n).toMonoidHom).map D.subtype=
        (A.map D.subtype).map (MulAut.conj (n:G)).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  rw [hmap,hmap,hjz] at hm
  have hX : X.val.map D.subtype=zpowers ((t.x:c.H):G) :=
    map_subgroupOf_eq_of_le (cubic_line_le_oddCore c t.x t.x_order)
  rw [hX] at hm
  exact mem_normalizer_iff_map_conj_eq.mpr hm

/-- The order243 Sylow possibility in the original order27-core branch is impossible. -/
theorem commonLineCore_card_ne243 (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) : Nat.card t.commonLineCore≠243 := by
  intro hp
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let P := t.commonLineCore
  let K := D⊓E
  let x : G := ((t.x:c.H):G)
  let X := zpowers x
  let z : G := t.z
  let : IsElementaryAbelian 3 D := t.left_oddCore_twentySeven_elementary hc
  have hXD : X≤D := cubic_line_le_oddCore c t.x t.x_order
  have hxD : x∈D := hXD (mem_zpowers _)
  have hx3 : orderOf x=3 := by dsimp [x]; rw [orderOf_coe,orderOf_coe,t.x_order]
  have hxne : x≠1 := by intro h; rw [h,orderOf_one] at hx3; omega
  have hxP : x∈P := t.left_oddCore_le_commonLineCore hc hxD
  have hPN : P≤normalizer (D:Set G) := (t.commonLineCore_normalizes_cores_of_card243 hc hp).1
  have hdiv : 243∣Nat.card (normalizer (D:Set G)) := hp ▸ card_dvd_of_le hPN
  have hnot : ¬729∣Nat.card G := by
    intro h
    obtain ⟨S,hS⟩ := t.commonLineCore_sylow hc
    have hd := S.pow_dvd_card_of_pow_dvd_card (n:=6) h
    change 3^6∣Nat.card (S:Subgroup G) at hd
    rw [hS,hp] at hd
    norm_num at hd
  have hKX : K⊓X=⊥ := by
    apply bot_unique
    have hXL : X≤c.H₁.map c.H.subtype := zpowers_le.mpr
      (mem_map_of_mem c.H.subtype t.x.property)
    exact (inf_le_inf inf_le_right hXL).trans
      (cubic_oddCore_inf_factor (swapFactors c) t.y).le
  have hKZ : K≤Subgroup.centralizer (P:Set G) := (t.commonLineCore_centralizer hc).ge
  have hzN : z∈normalizer (K:Set G) := t.torus_normalizes_core_intersection
    (mem_map_of_mem c.H.subtype (mem_sup_left (mem_zpowers _)))
  have hzX : MulAut.conj z x=x := by
    have hxH : x∈Subgroup.centralizer ({z}:Set G) := t.centralizer.le t.x.val.property
    have hh := mem_centralizer_singleton_iff.mp hxH
    change z*x*z⁻¹=x
    rw [←hh,mul_inv_cancel_right]
  have hinvK (k : G) (hk : k∈K) : MulAut.conj z k=k⁻¹ := by
    have hnorm : MulAut.conj z k∈K := (hzN k).mp hk
    have hinv : MulAut.conj z k*k∈X :=
      (cubic_oddCore_inversion c t.x t.x_order t.z
        ((orderOf_coe t.z).trans t.z_order) t.centralizer).1 k hk.1
    have he : MulAut.conj z k*k=1 := mem_bot.mp
      (hKX ▸ (show MulAut.conj z k*k∈K⊓X from ⟨K.mul_mem hnorm hk,hinv⟩))
    exact mul_eq_one_iff_eq_inv.mp he
  have hfixed (p : G) (hpP : p∈P) : MulAut.conj p x=x := by
    let k : G := ⁅p,x⁆
    have hk : k∈K := (t.commonLineCore_extraspecial_of_card243 hc hp).2.2
      (commutator_mem_commutator hpP hxP)
    let u := MulAut.conj p x
    have hu : u=k*x := by dsimp [u,k]; simp [commutatorElement_def,mul_assoc]
    have huz : MulAut.conj z u=k⁻¹*x := by rw [hu,map_mul,hinvK k hk,hzX]
    have hU : z∈normalizer (zpowers u:Set G) := by
      have hh := t.core_line_conjugates_normalized hc hdiv hnot p (hPN hpP)
      rwa [MonoidHom.map_zpowers] at hh
    have hu3 : orderOf u=3 := ((MulAut.conj p).orderOf_eq x).trans hx3
    have hz2 : z^2=1 := by
      change (t.z:G)^2=1
      simpa only [orderOf_coe,t.z_order] using pow_orderOf_eq_one (t.z:G)
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one (zpowers u)
      (by rw [Nat.card_zpowers,hu3]; exact Nat.prime_three) z hz2 hU with h|h
    · have hzu : MulAut.conj z u=u := by
        change z*u*z⁻¹=u
        rw [(h u (mem_zpowers u)).eq,mul_inv_cancel_right]
      have hkself : k⁻¹=k := mul_right_cancel (huz.symm.trans (hzu.trans hu))
      have hk2 : k^2=1 := (pow_two k).trans
        (by simpa only [hkself] using inv_mul_cancel k)
      have hk3 : k^3=1 := elemPow_eq_one_of_isElementaryAbelian k hk.1
      have hk1 : k=1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
        (by decide : Nat.Coprime 2 3) (orderOf_dvd_of_pow_eq_one hk2)
        (orderOf_dvd_of_pow_eq_one hk3))
      simpa only [hk1,one_mul] using hu
    · have hzu : MulAut.conj z u=u⁻¹ := h u (mem_zpowers u)
      have hxk : Commute x k := (hKZ hk x hxP)
      have hux : u⁻¹=k⁻¹*x⁻¹ := by rw [hu,mul_inv_rev,hxk.inv_inv.eq]
      have hxself : x=x⁻¹ := mul_left_cancel (huz.symm.trans (hzu.trans hux))
      have hx2 : x^2=1 := (pow_two x).trans
        (by simpa only [←hxself] using mul_inv_cancel x)
      have hd := orderOf_dvd_of_pow_eq_one hx2
      rw [hx3] at hd
      norm_num at hd
  have hxK : x∈K := by
    apply (t.commonLineCore_centralizer hc).le
    intro p hpP
    exact mul_inv_eq_iff_eq_mul.mp (hfixed p hpP)
  exact hxne (mem_bot.mp (hKX ▸ (show x∈K⊓X from ⟨hxK,mem_zpowers _⟩)))

/-- Only Sylow order729 survives for the original paired order27 cores. -/
theorem sylow_three_card729_of_twentySeven (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) (S : Sylow 3 G) : Nat.card S=729 := by
  obtain ⟨P,hP⟩ := t.commonLineCore_sylow hc
  have hp : Nat.card P≠243 := by
    rw [hP]
    exact t.commonLineCore_card_ne243 hc
  have hPcard : Nat.card P=729 := (t.sylow_three_card_of_twentySeven hc P).resolve_left hp
  exact (Nat.card_congr (S.equiv P).toEquiv).trans hPcard


/-- The literal common-line odd core has order 729. -/
theorem commonLineCore_card729 (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) : Nat.card t.commonLineCore=729 := by
  obtain ⟨P,hP⟩ := t.commonLineCore_sylow hc
  have hh := t.sylow_three_card729_of_twentySeven hc P
  rwa [hP] at hh

/-- The order486 centralizer alternative is excluded as well. -/
theorem core_intersection_centralizer_card1458 (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    Nat.card (Subgroup.centralizer
      ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G))=1458 := by
  let C := Subgroup.centralizer
    ((cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G)
  have hO : Nat.card (pPrimeCore 2 C)=729 := by
    have hh := t.commonLineCore_card729 hc
    change Nat.card ((pPrimeCore 2 C).map C.subtype)=729 at hh
    rwa [card_map_of_injective C.subtype_injective] at hh
  have hm := (pPrimeCore 2 C).card_mul_index
  rw [hO,(t.core_intersection_oddCore_index hc).1] at hm
  exact hm.symm

end CubicTorus

include c in
/-- From the original configuration, a Sylow subgroup larger than nine has
order at least 729. -/
theorem cubic_cube_dvd_sixth_power (hd : 3^3∣Nat.card G) : 3^6∣Nat.card G := by
  obtain ⟨t⟩ := exists_cubic_torus c
  rcases t.left_oddCore_orders with h|h|h
  · exact ((t.small_cores_iff_not_cube_dvd.mp ⟨h,t.oddCore_three_iff.mp h⟩) hd).elim
  · have hc := t.commonLineCore_card729 h
    have hh := t.commonLineCore.card_subgroup_dvd_card
    rwa [hc] at hh
  · exact cubic_maximal_core_sixth_power_dvd c t.x t.x_order h

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
