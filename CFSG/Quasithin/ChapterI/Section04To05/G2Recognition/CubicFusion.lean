module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicThreeCore
public import Theory.GroupTheory.CentralizerSylowConjugacy
public import Theory.GroupAction.ElementaryNineSylowLine
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure

/-!
# Cubic nonfusion and the Sylow-nine alternative

The quaternion cores of the two marked SL₂(3) factors are not conjugate:
any conjugator fixes their shared unique involution, hence lies in H,
where both factors are normal. Sylow conjugacy inside cubic centralizers
therefore prevents fusion between cubic elements or lines of the two factors.

The two lines generate an elementary group E of order nine. If both cubic
odd cores have order three, their normalizers lie in H. A hypothetical
order27 overgroup P of E normalizes E and acts on its four cubic lines.
The two marked lines have disjoint P-orbits, so at least one is fixed.
This would put P in H, contradicting |H|=576. Thus E is already Sylow.
Conversely a Sylow E of order nine forces both cores to have order three.
Together with the established orders 3,27,243, this excludes 3³ as the
exact three-part of the ambient order.

Source: Fong, Nagoya Math. J.39 (1970), §6B, p.75, using Fong–Wong,
Nagoya Math. J.36 (1969), §3B–C, p.156. We prove this argument directly
for q=3; we do not import §6's q≥5 standing assumption or its separate
branch exclusions. The Sylow-nine and order27-core branches still need
exclusion before the BN-pair/model recognition of Aschbacher–Smith I.4.5,
p.417. Those obligations remain with `qt-i45-g2-recognition`.
`Chapter14CubicFusion` applies these results to the original SourceLocalData.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal

private theorem quaternion_involutions_eq {Q : Type*} [Group Q]
    (e : Q ≃* QuaternionGroup 2) (a b : Q) (ha : orderOf a=2) (hb : orderOf b=2) : a=b := by
  have hna : e a ≠ 1 := by
    intro h
    have hh := e.orderOf_eq a
    rw [h, orderOf_one] at hh
    omega
  have hnb : e b ≠ 1 := by
    intro h
    have hh := e.orderOf_eq b
    rw [h, orderOf_one] at hh
    omega
  have hpa : (e a)^2 = 1 := by
    have hh := pow_orderOf_eq_one (e a)
    rw [e.orderOf_eq, ha] at hh
    exact hh
  have hpb : (e b)^2 = 1 := by
    have hh := pow_orderOf_eq_one (e b)
    rw [e.orderOf_eq, hb] at hh
    exact hh
  apply e.injective
  exact (by decide : ∀ u v : QuaternionGroup 2,
    u≠1 → u^2=1 → v≠1 → v^2=1 → u=v) _ _
      hna hpa hnb hpb

/-- The literal quaternion factors cannot be exchanged by ambient conjugation. -/
theorem factor_cores_not_conjugate (g : G) :
    ((c.H₂.pCoreIn 2).map c.H.subtype).map (MulAut.conj g).toMonoidHom ≠
      (c.H₁.pCoreIn 2).map c.H.subtype := by
  intro hg
  let Q₁ := (c.H₁.pCoreIn 2).map c.H.subtype
  let Q₂ := (c.H₂.pCoreIn 2).map c.H.subtype
  change Q₂.map (MulAut.conj g).toMonoidHom = Q₁ at hg
  obtain ⟨z,hz,hline,hH⟩ := exists_marked_involution c
  have hzI : z ∈ c.H₁.pCoreIn 2 ⊓ c.H₂.pCoreIn 2 :=
    (factor_core_intersection c).symm ▸ (hline ▸ mem_zpowers z)
  have hz₁ : (z:G) ∈ Q₁ := mem_map_of_mem c.H.subtype hzI.1
  have hz₂ : (z:G) ∈ Q₂ := mem_map_of_mem c.H.subtype hzI.2
  have hzg : MulAut.conj g (z:G) ∈ Q₁ := by
    rw [← hg]
    exact mem_map_of_mem _ hz₂
  let e : Q₁ ≃* QuaternionGroup 2 :=
    ((c.H₁.pCoreIn 2).equivMapOfInjective c.H.subtype c.H.subtype_injective).symm.trans
      (factorCoreEquiv c c.H₁ c.H₁_model.some)
  have he : MulAut.conj g (z:G) = (z:G) := congrArg Subtype.val
    (quaternion_involutions_eq e ⟨_,hzg⟩ ⟨_,hz₁⟩
      ((orderOf_coe _).symm.trans (((MulAut.conj g).orderOf_eq _).trans
        ((orderOf_coe z).trans hz))) ((orderOf_coe _).symm.trans ((orderOf_coe z).trans hz)))
  have hgH : g ∈ c.H := by
    rw [hH]
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  have hQ₂conj : Q₂.map (MulAut.conj g).toMonoidHom ≤ c.H₂.map c.H.subtype := by
    rintro q ⟨r,⟨s,hs,rfl⟩,rfl⟩
    exact ⟨(⟨g,hgH⟩ : c.H)*s*(⟨g,hgH⟩ : c.H)⁻¹,
      (inferInstance : c.H₂.Normal).conj_mem s (c.H₂.pCoreIn_le 2 hs) ⟨g,hgH⟩,rfl⟩
  have hQ₁H₂ : Q₁ ≤ c.H₂.map c.H.subtype := by rw [←hg]; exact hQ₂conj
  have hle : c.H₁.pCoreIn 2 ≤ c.H₁ ⊓ c.H₂ := by
    refine le_inf (c.H₁.pCoreIn_le 2) ?_
    exact (map_le_map_iff_of_injective c.H.subtype_injective).mp hQ₁H₂
  have hc := card_le_of_le hle
  have hQ : Nat.card (c.H₁.pCoreIn 2)=8 := by
    rw [Nat.card_congr (factorCoreEquiv c c.H₁ c.H₁_model.some).toEquiv,
      Nat.card_eq_fintype_card,QuaternionGroup.card]
  rw [hQ,intersection_card c] at hc
  omega

/-- Cubic elements in the two marked factors lie in distinct ambient classes. -/
theorem cubic_factors_not_conjugate (x : c.H₁) (y : c.H₂)
    (hx : orderOf x=3) (hy : orderOf y=3) : ¬ IsConj ((x:c.H):G) ((y:c.H):G) := by
  intro hxy
  obtain ⟨P,hP,_⟩ := cubic_quaternion_sylow c x hx
  obtain ⟨Q,hQ,_⟩ := cubic_quaternion_sylow (swapFactors c) y hy
  obtain ⟨g,_,hg⟩ := Sylow.exists_conj_element_and_centralizer_sylow _ _ hxy P Q
  exact factor_cores_not_conjugate c g
    ((congrArg (fun K : Subgroup G => K.map (MulAut.conj g).toMonoidHom) hP).symm.trans
      (hg.trans hQ))

/-- The two actual cyclic lines are not conjugate in the ambient group. -/
theorem cubic_lines_not_conjugate (x : c.H₁) (y : c.H₂)
    (hx : orderOf x=3) (g : G) :
    (zpowers ((x:c.H):G)).map (MulAut.conj g).toMonoidHom ≠ zpowers ((y:c.H):G) := by
  intro he
  have hmem : MulAut.conj g ((x:c.H):G) ∈ (c.H₂.map c.H.subtype) := by
    apply (zpowers_le.mpr (mem_map_of_mem c.H.subtype y.property) :
      zpowers ((y:c.H):G) ≤ c.H₂.map c.H.subtype)
    rw [←he]
    exact mem_map_of_mem _ (mem_zpowers _)
  obtain ⟨v,hv,heq⟩ := hmem
  let y' : c.H₂ := ⟨v,hv⟩
  have ho : orderOf y'=3 := by
    have hh := (MulAut.conj g).orderOf_eq ((x:c.H):G)
    rw [←heq,orderOf_coe,orderOf_coe,hx] at hh
    exact (orderOf_coe y').symm.trans ((orderOf_coe v).symm.trans hh)
  apply cubic_factors_not_conjugate c x y' hx ho
  exact isConj_iff.mpr ⟨g,heq.symm⟩

/-- The original cubic lines generate an elementary subgroup of order nine. -/
theorem cubic_plane_data (x : c.H₁) (y : c.H₂)
    (hx : orderOf x=3) (hy : orderOf y=3) :
    IsElementaryAbelian 3 (zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G) : Subgroup G) ∧
      Nat.card (zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G) : Subgroup G)=9 := by
  let A := zpowers ((x:c.H):G)
  let B := zpowers ((y:c.H):G)
  have ha : Nat.card A=3 := by rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,hx]
  have hb : Nat.card B=3 := by rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,hy]
  have hc : B ≤ centralizer (A : Set G) := by
    change B ≤ centralizer (zpowers ((x:c.H):G) : Set G)
    rw [zpowers_eq_closure,centralizer_closure]
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (c.commute x x.property y y.property).symm)
  have hab : A ⊓ B = ⊥ := by
    have hh := card_dvd_of_le (show A ⊓ B ≤ A from inf_le_left)
    have hI : A ⊓ B ≤ (c.H₁ ⊓ c.H₂).map c.H.subtype := by
      rw [map_inf _ _ _ c.H.subtype_injective]
      exact inf_le_inf (zpowers_le.mpr (mem_map_of_mem c.H.subtype x.property))
        (zpowers_le.mpr (mem_map_of_mem c.H.subtype y.property))
    have hi := card_dvd_of_le hI
    rw [ha] at hh
    rw [card_map_of_injective c.H.subtype_injective,intersection_card c] at hi
    have hone := Nat.dvd_gcd hh hi
    norm_num at hone
    exact (card_eq_one.mp hone)
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.zpowers_of_pow_eq_one
    (by simpa only [orderOf_coe,hx] using pow_orderOf_eq_one ((x:c.H):G))
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.zpowers_of_pow_eq_one
    (by simpa only [orderOf_coe,hy] using pow_orderOf_eq_one ((y:c.H):G))
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hc,?_⟩
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B
    (hc.trans (Subgroup.centralizer_le_normalizer _))
  rw [ha,hb,hab,card_bot,one_mul] at hh
  exact hh.symm

private theorem fixed_of_two_disjoint_orbits {K X : Type*} [Group K] [Finite K]
    [Finite X] [MulAction K X] (hp : IsPGroup 3 K) (S : Set X) (hS : S.ncard=4)
    (x y : X) (hx : MulAction.orbit K x ⊆ S) (hy : MulAction.orbit K y ⊆ S)
    (hne : ∀ k : K, k • x ≠ y) :
    (∀ k : K, k • x = x) ∨ (∀ k : K, k • y = y) := by
  classical
  have hd : Disjoint (MulAction.orbit K x) (MulAction.orbit K y) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨a,ha⟩ ⟨b,hb⟩
    apply hne (b⁻¹*a)
    change a • x = z at ha
    change b • y = z at hb
    rw [mul_smul,ha,←hb,inv_smul_smul]
  have hbound := Set.ncard_le_ncard (Set.union_subset hx hy)
  rw [hS,Set.ncard_union_eq hd] at hbound
  have horb (v : X) : (∀ k : K, k • v=v) ∨ 3 ≤ (MulAction.orbit K v).ncard := by
    obtain ⟨i,hi⟩ := hp.card_orbit v
    change (MulAction.orbit K v).ncard=3^i at hi
    by_cases hz : i=0
    · left
      have hh : (MulAction.orbit K v).ncard=1 := by simpa only [hz,pow_zero] using hi
      obtain ⟨w,hw⟩ := Set.ncard_eq_one.mp hh
      have hv : v=w := by simpa only [hw,Set.mem_singleton_iff] using MulAction.mem_orbit_self (M := K) v
      intro k
      have hm : k • v ∈ MulAction.orbit K v := ⟨k,rfl⟩
      simpa only [hw,Set.mem_singleton_iff,←hv] using hm
    · right
      rw [hi]
      exact (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 1 ≤ i))
  rcases horb x with h | h
  · exact Or.inl h
  rcases horb y with h' | h'
  · exact Or.inr h'
  omega


private theorem cubic_plane_no_twenty_seven (x : c.H₁) (y : c.H₂)
    (hx : orderOf x=3) (hy : orderOf y=3)
    (hNx : cubicNormalizer c x ≤ c.H)
    (hNy : cubicNormalizer (swapFactors c) y ≤ c.H) : ¬ 27 ∣ Nat.card G := by
  intro hdiv
  let A := zpowers ((x:c.H):G)
  let B := zpowers ((y:c.H):G)
  let E := A ⊔ B
  obtain ⟨he,hEc⟩ := cubic_plane_data c x y hx hy
  let : IsElementaryAbelian 3 E := he
  have hEc : Nat.card E=9 := hEc
  obtain ⟨P,hPc,hEP⟩ := Sylow.exists_subgroup_card_pow_succ (p := 3) (n := 2)
    hdiv hEc
  have hp : IsPGroup 3 P := IsPGroup.of_card (n := 3) hPc
  let E' := E.subgroupOf P
  have hi : E'.index=3 := by
    have hh := E'.card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv,hEc,hPc] at hh
    omega
  let : E'.Normal := normal_of_index_three_of_isPGroup hp E' hi
  have hPE : P ≤ normalizer (E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hEP).mp (inferInstance : E'.Normal)
  let ρ : P →* MulAut E := E.normalizerMonoidHom.comp (inclusion hPE)
  let : MulAction P (Subgroup E) := MulAction.compHom (Subgroup E) ρ
  let a := A.subgroupOf E
  let b := B.subgroupOf E
  let S := {L : Subgroup E | Nat.card L=3}
  have hS : S.ncard=4 := IsElementaryAbelian.TernarySylowLine.card_cubic_subgroups hEc
  have ha : Nat.card a=3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ E from le_sup_left)).toEquiv,
      Nat.card_zpowers,orderOf_coe,orderOf_coe,hx]
  have hb : Nat.card b=3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show B ≤ E from le_sup_right)).toEquiv,
      Nat.card_zpowers,orderOf_coe,orderOf_coe,hy]
  have hcompat (g : P) (L : Subgroup E) :
      (g • L).map E.subtype = (L.map E.subtype).map (MulAut.conj (g:G)).toMonoidHom := by
    change (L.map (ρ g).toMonoidHom).map E.subtype = _
    rw [map_map,map_map]
    rfl
  have haO : MulAction.orbit P a ⊆ S := by
    rintro L ⟨g,rfl⟩
    change Nat.card (a.map (ρ g).toMonoidHom)=3
    exact (Nat.card_congr (a.equivMapOfInjective (ρ g).toMonoidHom (ρ g).injective).toEquiv).symm.trans ha
  have hbO : MulAction.orbit P b ⊆ S := by
    rintro L ⟨g,rfl⟩
    change Nat.card (b.map (ρ g).toMonoidHom)=3
    exact (Nat.card_congr (b.equivMapOfInjective (ρ g).toMonoidHom (ρ g).injective).toEquiv).symm.trans hb
  have hnf : ∀ g : P, g • a ≠ b := by
    intro g hg
    have hh := congrArg (map E.subtype) hg
    rw [hcompat,map_subgroupOf_eq_of_le (show A ≤ E from le_sup_left),
      map_subgroupOf_eq_of_le (show B ≤ E from le_sup_right)] at hh
    exact cubic_lines_not_conjugate c x y hx g hh
  have hfixed := fixed_of_two_disjoint_orbits hp S hS a b haO hbO hnf
  have hPH : P ≤ c.H := by
    rcases hfixed with hf | hf
    · intro g hg
      apply hNx
      apply mem_normalizer_iff_map_conj_eq.mpr
      have hh := congrArg (map E.subtype) (hf ⟨g,hg⟩)
      rw [hcompat,map_subgroupOf_eq_of_le (show A ≤ E from le_sup_left)] at hh
      exact hh
    · intro g hg
      apply hNy
      apply mem_normalizer_iff_map_conj_eq.mpr
      have hh := congrArg (map E.subtype) (hf ⟨g,hg⟩)
      rw [hcompat,map_subgroupOf_eq_of_le (show B ≤ E from le_sup_right)] at hh
      exact hh
  have hh := card_dvd_of_le hPH
  rw [hPc,H_card c] at hh
  norm_num at hh


/-- When both odd cores have order three, the original plane is ambient Sylow. -/
theorem cubic_plane_sylow_of_small_cores (x : c.H₁) (y : c.H₂)
    (hx : orderOf x=3) (hy : orderOf y=3)
    (hDx : Nat.card (cubicOddCore c x)=3)
    (hDy : Nat.card (cubicOddCore (swapFactors c) y)=3) :
    ∃ P : Sylow 3 G, (P : Subgroup G) =
      zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G) := by
  let E := zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G)
  have hnot := cubic_plane_no_twenty_seven c x y hx hy
    ((cubic_normalizer_le_H_iff c x hx).mpr hDx)
    ((cubic_normalizer_le_H_iff (swapFactors c) y hy).mpr hDy)
  obtain ⟨he,hc⟩ := cubic_plane_data c x y hx hy
  have hp : IsPGroup 3 E := IsPGroup.of_card (n := 2) hc
  have hi : ¬ 3 ∣ E.index := by
    intro hd
    apply hnot
    have hh : 27 ∣ Nat.card E * E.index := by
      rw [hc]
      exact Nat.mul_dvd_mul_left 9 hd
    rwa [E.card_mul_index] at hh
  exact ⟨hp.toSylow hi,rfl⟩

namespace CubicTorus
variable {c} (t : CubicTorus c)

/-- Both marked cores are smallest precisely when 27 does not divide |G|. -/
theorem small_cores_iff_not_cube_dvd :
    Nat.card (cubicOddCore c t.x)=3 ∧
      Nat.card (cubicOddCore (swapFactors c) t.y)=3 ↔ ¬ 3^3 ∣ Nat.card G := by
  constructor
  · rintro ⟨hx,hy⟩
    exact cubic_plane_no_twenty_seven c t.x t.y t.x_order t.y_order
      ((cubic_normalizer_le_H_iff c t.x t.x_order).mpr hx)
      ((cubic_normalizer_le_H_iff (swapFactors c) t.y t.y_order).mpr hy)
  · intro hnot
    have hn (D : Subgroup G) (hD : Nat.card D=3 ∨ Nat.card D=27 ∨ Nat.card D=243) :
        Nat.card D=3 := by
      rcases hD with h|h|h
      · exact h
      · have hh := D.card_subgroup_dvd_card
        rw [h] at hh
        exact (hnot hh).elim
      · have hh := D.card_subgroup_dvd_card
        rw [h] at hh
        exact (hnot ((by decide : 3^3 ∣ 243).trans hh)).elim
    exact ⟨hn _ t.left_oddCore_orders,hn _ t.right_oddCore_orders⟩

/-- Sylow maximality of the literal plane detects the two smallest cores. -/
theorem cubic_plane_sylow_iff :
    (∃ P : Sylow 3 G, (P : Subgroup G) =
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)) ↔
      Nat.card (cubicOddCore c t.x)=3 ∧
        Nat.card (cubicOddCore (swapFactors c) t.y)=3 := by
  constructor
  · rintro ⟨P,hP⟩
    apply t.small_cores_iff_not_cube_dvd.mpr
    intro hd
    have hh := P.pow_dvd_card_of_pow_dvd_card hd
    have hc : Nat.card P=9 := by
      rw [hP]
      exact (cubic_plane_data c t.x t.y t.x_order t.y_order).2
    rw [hc] at hh
    norm_num at hh
  · rintro ⟨hx,hy⟩
    exact cubic_plane_sylow_of_small_cores c t.x t.y t.x_order t.y_order hx hy
end CubicTorus

include c in
/-- The three-part of the ambient order cannot be exactly 27. -/
theorem cubic_cube_dvd_fourth_power (hd : 3^3 ∣ Nat.card G) : 3^4 ∣ Nat.card G := by
  obtain ⟨t⟩ := exists_cubic_torus c
  have hsmall : ¬ (Nat.card (cubicOddCore c t.x)=3 ∧
      Nat.card (cubicOddCore (swapFactors c) t.y)=3) :=
    fun hh => (t.small_cores_iff_not_cube_dvd.mp hh) hd
  have hlarge {d : G2ThreeConfiguration G} (x : d.H₁) (hx : orderOf x=3)
      (he : Nat.card (cubicOddCore d x)=27 ∨ Nat.card (cubicOddCore d x)=243) :
      3^4 ∣ Nat.card G := by
    have hh := (cubicCentralizer d x).card_subgroup_dvd_card
    rw [cubic_centralizer_card d x hx] at hh
    rcases he with he|he <;> rw [he] at hh
    · exact (by decide : 3^4 ∣ 27*24).trans hh
    · exact (by decide : 3^4 ∣ 243*24).trans hh
  rcases t.left_oddCore_orders with hx|hx
  · rcases t.right_oddCore_orders with hy|hy
    · exact (hsmall ⟨hx,hy⟩).elim
    · exact hlarge (d := swapFactors c) t.y t.y_order hy
  · exact hlarge (d := c) t.x t.x_order hx

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
