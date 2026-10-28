module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PairedCoreJoinFixed
public import Theory.GroupTheory.PrimeRankFixedJoin
/-!
# Excluding the paired order-27 cores

The common line K is conjugate to a diagonal in the original cubic plane.
Pull that plane and its central involution back to U and v. Then U lies
in the actual Sylow P = O(C_G(K)), and v normalizes P and centralizes K.
The preceding extraspecial join J = D join E has C_J(v) = K. Thus the
pulled-back factor cubics a,b lie outside J and K. Each generates U with
K, so C_P(a) = C_P(b).

The fixed-point bound gives |C_J(a)| ≥ 27; adjoining a gives
|C_P(a)| ≥ 81. Its order divides the odd part 81 of the original marked
cubic centralizer, so equality holds. Conjugating back produces a common
order-81 Sylow subgroup of both original cubic centralizers. Both normal
odd cores D and E must lie in it, contradicting |D join E| = 243.

This excludes order-27 marked cores, not arbitrary order-27 subgroups or
Sylow order 729 in other branches. Only the simultaneous core orders 3
and 243 remain. Source: Aschbacher–Smith I.4(G1)–(G2), printed p.417;
this completes the exceptional q=3 core exclusion without the q>3 line
selection of Fong §6C. Chapter14PairedCoreExclusion is the source consumer.
The Sylow-nine branch and actual Atlas equivalence remain unproved here.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}

omit [Finite G] in
private theorem centralizer_card_equiv (f : G ≃* G) (a : G) :
    Nat.card (Subgroup.centralizer ({a}:Set G))=Nat.card (Subgroup.centralizer ({f a}:Set G)) := by
  apply Nat.card_congr
  exact Equiv.subtypeEquiv f.toEquiv (fun u => by
    simp only [mem_centralizer_singleton_iff]
    change u*a=a*u ↔ f u*f a=f a*f u
    rw [←map_mul,←map_mul,f.injective.eq_iff])

private theorem marked_core_le (d : G2ThreeConfiguration G) (x : d.H₁)
    (hx : orderOf x=3) (hc : Nat.card (cubicOddCore d x)=27)
    (Q : Subgroup G) (hQ : Nat.card Q=81) (hQC : Q≤cubicCentralizer d x) :
    cubicOddCore d x≤Q := by
  let C := cubicCentralizer d x
  let O := pPrimeCore 2 C
  let S := Q.subgroupOf C
  have hS : Nat.card S=81 := (Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv).trans hQ
  have hC : Nat.card C=648 := by rw [cubic_centralizer_card d x hx,hc]
  have hi : S.index=8 := by
    have hh := S.card_mul_index
    rw [hS,hC] at hh
    omega
  let T : Sylow 3 C := (IsPGroup.of_card (p:=3) (n:=4) hS).toSylow (by rw [hi]; decide)
  have hO : Nat.card O=27 := by
    have hh := hc
    change Nat.card (O.map C.subtype)=27 at hh
    rwa [card_map_of_injective C.subtype_injective] at hh
  have hle := (IsPGroup.of_card (p:=3) (n:=3) hO).le_sylow_of_normal T
  have hm := map_mono (f:=C.subtype) hle
  change O.map C.subtype≤(Q.subgroupOf C).map C.subtype at hm
  rwa [map_subgroupOf_eq_of_le hQC] at hm

namespace CubicTorus

/-- The final Sylow-729 case of the paired order-27 cores is impossible. -/
theorem left_oddCore_card_ne_twentySeven (t : CubicTorus c) : Nat.card (cubicOddCore c t.x)≠27 := by
  intro hc
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let J := D⊔E
  let K := D⊓E
  let P := t.commonLineCore
  let x : G := ((t.x:c.H):G)
  let y : G := ((t.y:c.H):G)
  let z : G := t.z
  let W := zpowers x ⊔ zpowers y
  have hW : Nat.card W=9 := (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  let : IsElementaryAbelian 3 W := (cubic_plane_data c t.x t.y t.x_order t.y_order).1
  have hK : Nat.card K=3 := t.oddCore_intersection_card_of_twentySeven hc
  have hP : Nat.card P=729 := t.commonLineCore_card729 hc
  have hJ : Nat.card J=243 := (t.paired_cores_join_card_normal hc).1
  obtain ⟨g,hKg,hKx,hKy⟩ := t.exists_core_intersection_diagonal hc
  let f := MulAut.conj g
  let a := f.symm x
  let b := f.symm y
  let v := f.symm z
  let U := W.map f.symm.toMonoidHom
  have hU : Nat.card U=9 := by rw [card_map_of_injective f.symm.injective]; exact hW
  have ha3 : orderOf a=3 := (f.symm.orderOf_eq x).trans (by dsimp [x]; rw [orderOf_coe,orderOf_coe,t.x_order])
  have hb3 : orderOf b=3 := (f.symm.orderOf_eq y).trans (by dsimp [y]; rw [orderOf_coe,orderOf_coe,t.y_order])
  have hv2 : orderOf v=2 := (f.symm.orderOf_eq z).trans ((orderOf_coe t.z).trans t.z_order)
  have haU : a∈U := mem_map_of_mem _ (mem_sup_left (mem_zpowers x))
  have hbU : b∈U := mem_map_of_mem _ (mem_sup_right (mem_zpowers y))
  have hKU : K≤U := by
    intro k hk
    exact ⟨f k,hKg (mem_map_of_mem f.toMonoidHom hk),f.symm_apply_apply k⟩
  have hUC : U≤Subgroup.centralizer (K:Set G) := by
    have hh := (map_mono (f:=f.symm.toMonoidHom) W.le_centralizer).trans
      (map_centralizer_le_centralizer_image (W:Set G) f.symm.toMonoidHom)
    exact hh.trans (centralizer_le hKU)
  have hUP : U≤P := by
    let C := Subgroup.centralizer (K:Set G)
    let O := pPrimeCore 2 C
    have hi : O.index=2 := (t.core_intersection_oddCore_index hc).1
    have hu : Nat.card (U.subgroupOf C)=9 :=
      (Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv).trans hU
    have hr : O.relIndex (U.subgroupOf C)=1 := Nat.eq_one_of_dvd_coprimes
      (by rw [hi,hu]; decide) (O.relIndex_dvd_index_of_normal _) (relIndex_dvd_card _ _)
    have hh := map_mono (f:=C.subtype) (relIndex_eq_one.mp hr)
    rwa [map_subgroupOf_eq_of_le hUC] at hh
  have hWH : W≤c.H := sup_le (zpowers_le.mpr t.x.val.property) (zpowers_le.mpr t.y.val.property)
  have hvK : v∈Subgroup.centralizer (K:Set G) := by
    intro k hk
    apply f.injective
    simp only [map_mul]
    rw [show f v=z from f.apply_symm_apply z]
    exact mem_centralizer_singleton_iff.mp
      (t.centralizer ▸ hWH (hKg (mem_map_of_mem f.toMonoidHom hk)))
  have hvN : v∈normalizer (P:Set G) := by
    rw [t.commonLineCore_normalizer hc]
    exact Subgroup.centralizer_le_normalizer _ hvK
  have hcomm (u : G) (hu : u∈W) : Commute v (f.symm u) := by
    apply f.injective
    simp only [map_mul]
    rw [show f v=z from f.apply_symm_apply z,f.apply_symm_apply]
    exact (mem_centralizer_singleton_iff.mp (t.centralizer ▸ hWH hu)).symm
  have hva : Commute v a := hcomm x (mem_sup_left (mem_zpowers x))
  have hvb : Commute v b := hcomm y (mem_sup_right (mem_zpowers y))
  obtain ⟨hfixed,hbound⟩ := t.paired_cores_join_fixed hc v hv2 hvN hvK
  change J ⊓ Subgroup.centralizer ({v}:Set G)=K at hfixed
  have hnot (u : G) (hu : orderOf u=3)
      (hne : K.map f.toMonoidHom≠zpowers u) : f.symm u∉K := by
    intro hm
    have hum : u∈K.map f.toMonoidHom := by
      have hh := mem_map_of_mem f.toMonoidHom hm
      change f (f.symm u)∈K.map f.toMonoidHom at hh
      rwa [f.apply_symm_apply] at hh
    apply hne
    apply Eq.symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr hum)
    rw [Nat.card_zpowers,hu,card_map_of_injective f.injective,hK]
  have hx3 : orderOf x=3 := by dsimp [x]; rw [orderOf_coe,orderOf_coe,t.x_order]
  have hy3 : orderOf y=3 := by dsimp [y]; rw [orderOf_coe,orderOf_coe,t.y_order]
  have haK : a∉K := hnot x hx3 hKx
  have hbK : b∉K := hnot y hy3 hKy
  have hCK : P≤Subgroup.centralizer (K:Set G) := le_centralizer_iff.mp
    (t.commonLineCore_centralizer hc).ge
  have hgen (u : G) (hu : u∈U) (hu3 : orderOf u=3) (huK : u∉K) : zpowers u ⊔ K=U := by
    have hn : K≤normalizer (zpowers u:Set G) := by
      apply le_trans _ (Subgroup.centralizer_le_normalizer _)
      apply le_centralizer_iff.mpr
      exact (zpowers_le.mpr (hUP hu)).trans hCK
    apply eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hu) hKU)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn
      (K.disjoint_zpowers_of_prime_order_not_mem u hu3 huK).symm,
      Nat.card_zpowers,hu3,hK,hU]
  have haGen := hgen a haU ha3 haK
  have hbGen := hgen b hbU hb3 hbK
  have hcent (u : G) (hu : zpowers u ⊔ K=U) :
      P ⊓ Subgroup.centralizer ({u}:Set G)=P ⊓ Subgroup.centralizer (U:Set G) := by
    apply le_antisymm
    · intro w hw
      refine ⟨hw.1,?_⟩
      have h1 : zpowers u≤Subgroup.centralizer ({w}:Set G) := zpowers_le.mpr
        (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hw.2).symm)
      have h2 : K≤Subgroup.centralizer ({w}:Set G) := fun k hk =>
        mem_centralizer_singleton_iff.mpr (hCK hw.1 k hk)
      intro q hq
      exact mem_centralizer_singleton_iff.mp ((hu ▸ sup_le h1 h2) hq)
    · intro w hw
      exact ⟨hw.1,mem_centralizer_singleton_iff.mpr (hw.2 u (hu ▸ mem_sup_left (mem_zpowers u))).symm⟩
  have hsame : P ⊓ Subgroup.centralizer ({a}:Set G)=P ⊓ Subgroup.centralizer ({b}:Set G) :=
    (hcent a haGen).trans (hcent b hbGen).symm
  let F := P ⊓ Subgroup.centralizer ({a}:Set G)
  have hF : Nat.card F=81 := by
    have hja : a∉J := by
      intro haJ
      exact haK (hfixed ▸ (show a∈J ⊓ Subgroup.centralizer ({v}:Set G) from
        ⟨haJ,mem_centralizer_singleton_iff.mpr hva.eq.symm⟩))
    let C := J ⊓ Subgroup.centralizer ({a}:Set G)
    have hCa : zpowers a≤Subgroup.centralizer (C:Set G) := by
      apply zpowers_le.mpr
      intro u hu
      exact mem_centralizer_singleton_iff.mp hu.2
    have hd : Disjoint C (zpowers a) := (J.disjoint_zpowers_of_prime_order_not_mem a ha3 hja).mono_left inf_le_left
    have hCF : C ⊔ zpowers a≤F := sup_le
      (inf_le_inf_right _ (sup_le (t.left_oddCore_le_commonLineCore hc) (t.right_oddCore_le_commonLineCore hc)))
      (zpowers_le.mpr ⟨hUP haU,mem_centralizer_singleton_iff.mpr rfl⟩)
    have hlo : 81≤Nat.card F := by
      have hh := card_le_of_le hCF
      rw [card_sup_eq_mul_of_normalizes_of_disjoint C (zpowers a)
        (hCa.trans (Subgroup.centralizer_le_normalizer _)) hd,Nat.card_zpowers,ha3] at hh
      have hbnd := hbound a (hUP haU) ha3 hva
      change 27≤Nat.card C at hbnd
      omega
    have hodd : Odd (Nat.card F) := (show Odd (Nat.card P) by rw [hP]; decide).of_dvd_nat
      (card_dvd_of_le inf_le_left)
    have hCaCard : Nat.card (Subgroup.centralizer ({a}:Set G))=648 := by
      rw [centralizer_card_equiv f a]
      change Nat.card (Subgroup.centralizer ({f (f.symm x)}:Set G))=648
      rw [f.apply_symm_apply]
      exact (cubic_centralizer_card c t.x t.x_order).trans (by rw [hc])
    have hdiv : Nat.card F∣81 := by
      have hh := card_dvd_of_le (show F≤Subgroup.centralizer ({a}:Set G) from inf_le_right)
      rw [hCaCard] at hh
      exact (hodd.coprime_two_right.pow_right 3).dvd_of_dvd_mul_left hh
    exact Nat.le_antisymm (Nat.le_of_dvd (by decide) hdiv) hlo
  let Q := F.map f.toMonoidHom
  have hQ : Nat.card Q=81 := by rw [card_map_of_injective f.injective,hF]
  have hQx : Q≤cubicCentralizer c t.x := by
    rintro u ⟨w,hw,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg f (mem_centralizer_singleton_iff.mp hw.2)
    change f w*x=x*f w
    simpa only [map_mul,show f a=x from f.apply_symm_apply x] using hh
  have hQy : Q≤cubicCentralizer (swapFactors c) t.y := by
    rintro u ⟨w,hw,rfl⟩
    have hw' : w∈P ⊓ Subgroup.centralizer ({b}:Set G) := hsame ▸ hw
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg f (mem_centralizer_singleton_iff.mp hw'.2)
    change f w*y=y*f w
    simpa only [map_mul,show f b=y from f.apply_symm_apply y] using hh
  have hDQ := marked_core_le c t.x t.x_order hc Q hQ hQx
  have hEQ := marked_core_le (swapFactors c) t.y t.y_order
    (t.right_oddCore_twentySeven_of_left hc) Q hQ hQy
  have hh := card_le_of_le (sup_le hDQ hEQ)
  rw [hQ,hJ] at hh
  omega

/-- The opposite original marking also cannot have core order 27. -/
theorem right_oddCore_card_ne_twentySeven (t : CubicTorus c) :
    Nat.card (cubicOddCore (swapFactors c) t.y)≠27 :=
  t.swap.left_oddCore_card_ne_twentySeven

/-- The two original cores are both minimal or both maximal. -/
theorem paired_oddCore_final_orders (t : CubicTorus c) :
    (Nat.card (cubicOddCore c t.x)=3 ∧ Nat.card (cubicOddCore (swapFactors c) t.y)=3) ∨
    (Nat.card (cubicOddCore c t.x)=243 ∧ Nat.card (cubicOddCore (swapFactors c) t.y)=243) := by
  have he := t.oddCore_card_eq
  rcases t.left_oddCore_orders with h|h|h
  · exact Or.inl ⟨h,he.symm.trans h⟩
  · exact (t.left_oddCore_card_ne_twentySeven h).elim
  · exact Or.inr ⟨h,he.symm.trans h⟩

/-- Away from Sylow-nine, both original marked cores have order 243. -/
theorem paired_oddCore_maximal_of_cube_dvd (t : CubicTorus c) (hd : 3^3∣Nat.card G) :
    Nat.card (cubicOddCore c t.x)=243 ∧ Nat.card (cubicOddCore (swapFactors c) t.y)=243 := by
  exact t.paired_oddCore_final_orders.resolve_left
    (fun h => t.small_cores_iff_not_cube_dvd.mp h hd)

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
