module
public import Theory.GroupTheory.GeneralizedFitting.ThompsonNormalizerLayer
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Maximum elementary subgroups normalize a centerless component

Suppose a component has an elementary Sylow subgroup P with |P| > 2,
and every elementary two-subgroup of Aut(L) has order at most |P|.
If a maximum elementary subgroup A moves L, the two commuting component
Sylows form an elementary group of order |P|². Adjoining A's action kernel
contradicts maximality: the stabilizer image has order at most |P| and its
index in A is at most two. Consequently J(S) normalizes L.

Both the component and its normalizer are relative to the specified overgroup.
Source application: the ordinary PSL₂ branch of Aschbacher--Smith 15.1.21,
printed pp.1097--1098. This is the elementary replacement argument at that
boundary; it does not assume normality of the component in the ambient group.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The actual component Sylow dominates every maximum elementary subgroup
that moves a centerless component. -/
theorem IsComponent.maxJ_normalizes_of_elementary_sylow_bound
    (H L S : Subgroup G) (hLH : L ≤ H) (hSH : S ≤ H)
    (hL : IsComponent H (L.subgroupOf H))
    (hz : center L=⊥) (hi : (normalizer (L : Set G)).relIndex S ≤ 2)
    (P : Sylow 2 L) [IsElementaryAbelian 2 P]
    (hPS : (P : Subgroup L).map L.subtype ≤ S) (hp : 2 < Nat.card P)
    (hb : ∀ D : Subgroup (MulAut L), IsElementaryAbelian 2 D → Nat.card D ≤ Nat.card P) :
    elementaryAbelianMaxJ S ≤ normalizer (L : Set G) := by
  let U := (P : Subgroup L).map L.subtype
  have hUL : U ≤ L := map_subtype_le _
  have hcardU : Nat.card U=Nat.card P := card_map_of_injective L.subtype_injective
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map L.subtype
  have disj (W : Subgroup G) (hWL : W ≤ L) : Disjoint W (centralizer (L : Set G)) := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hh : (⟨x,hWL hx.1⟩:L) ∈ center L :=
      mem_center_iff.mpr (fun l => Subtype.ext (hx.2 l l.property))
    exact mem_bot.mpr (congrArg (fun l : L => (l:G)) (mem_bot.mp (hz ▸ hh)))
  apply sSup_le
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2.1
  by_contra hn
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hn
  let c := MulAut.conj a
  let L' := L.map c.toMonoidHom
  let U' := U.map c.toMonoidHom
  have hLL : L ≤ centralizer (L' : Set G) := by
    let aH : H := ⟨a,hSH (hA.1 ha)⟩
    let K := L.subgroupOf H
    have hK : K.map H.subtype=L := map_subgroupOf_eq_of_le hLH
    have hmap : (K.map (MulAut.conj aH).toMonoidHom).map H.subtype=L' := by
      rw [map_map]
      have he : H.subtype.comp (MulAut.conj aH).toMonoidHom = c.toMonoidHom.comp H.subtype := rfl
      rw [he,←map_map,hK]
    have hne : K ≠ K.map (MulAut.conj aH).toMonoidHom := by
      intro he
      have hh := congrArg (map H.subtype) he
      rw [hK,hmap] at hh
      exact han (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
    have hc := congrArg (map H.subtype)
      (hL.commutator_eq_bot_of_ne (hL.map_conj aH) hne)
    rw [map_commutator,hK,hmap,Subgroup.map_bot] at hc
    exact commutator_eq_bot_iff_le_centralizer.mp hc
  have hUU : U ≤ centralizer (U' : Set G) :=
    hUL.trans (hLL.trans (centralizer_le (map_mono hUL)))
  have hU'S : U' ≤ S := by
    rintro _ ⟨u,hu,rfl⟩
    exact S.mul_mem (S.mul_mem (hA.1 ha) (hPS hu)) (S.inv_mem (hA.1 ha))
  let E := U ⊔ U'
  let : IsElementaryAbelian 2 U' := IsElementaryAbelian.map c.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp hUU)
  have hE : E ≤ S := sup_le hPS hU'S
  have hUUd : Disjoint U U' := (disj U hUL).mono_right
    ((map_mono hUL).trans (le_centralizer_iff.mp hLL))
  have hcardE : Nat.card E=Nat.card P * Nat.card P := by
    rw [show E=U⊔U' from rfl,card_sup_eq_mul_of_normalizes_of_disjoint U U'
      ((le_centralizer_iff.mp hUU).trans (Subgroup.centralizer_le_normalizer _)) hUUd,
      show U'=U.map c.toMonoidHom from rfl,(card_map_of_injective (K:=U) (f:=c.toMonoidHom) c.injective),hcardU]
  let K := A ⊓ centralizer (L : Set G)
  have hKA : K ≤ A := inf_le_left
  have hKC : K ≤ centralizer (L : Set G) := inf_le_right
  have hKC' : K ≤ centralizer (L' : Set G) := by
    intro k hk
    rintro _ ⟨l,hl,rfl⟩
    have hka : Commute k a := congrArg Subtype.val (mul_comm (⟨k,hk.1⟩:A) ⟨a,ha⟩)
    have hkl : Commute k l := (hk.2 l hl).symm
    exact (hka.mul_right hkl |>.mul_right hka.inv_right).eq.symm
  have hKE : K ≤ centralizer (E : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (hKC.trans (centralizer_le hUL)))
      (le_centralizer_iff.mp (hKC'.trans (centralizer_le (map_mono hUL))))
  have hEK : Disjoint E K := by
    apply disjoint_def.mpr
    intro x hxE hxK
    have hxprod : x ∈ (U : Set G)*(U' : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left U U'
        ((le_centralizer_iff.mp hUU).trans (Subgroup.centralizer_le_normalizer _))]
      exact hxE
    obtain ⟨u,hu,v,hv,rfl⟩ := hxprod
    have hvC : v ∈ centralizer (L : Set G) :=
      (le_centralizer_iff.mp hLL) ((map_mono hUL) hv)
    have huC : u ∈ centralizer (L : Set G) := by
      have hh := (centralizer (L : Set G)).mul_mem (hKC hxK)
        ((centralizer (L : Set G)).inv_mem hvC)
      simpa only [mul_inv_cancel_right] using hh
    have hu1 : u=1 := disjoint_def.mp (disj U hUL) hu huC
    have hvK : v ∈ K := by simpa only [hu1,one_mul] using hxK
    have hvC' := hKC' hvK
    have hv1 : v=1 := by
      obtain ⟨w,hw,rfl⟩ := hv
      have hwC : w ∈ centralizer (L : Set G) := by
        intro l hl
        apply c.injective
        exact (c.map_mul l w).trans ((hvC' (c l) (mem_map_of_mem c.toMonoidHom hl)).trans (c.map_mul w l).symm)
      exact (map_eq_one_iff c c.injective).mpr (disjoint_def.mp (disj U hUL) hw hwC)
    simp only [hu1,hv1,mul_one]
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le hKA
  have hjoin : IsElementaryAbelian 2 (E⊔K : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hKE
  have hmax := hA.2.2 (E⊔K) (sup_le hE (hKA.trans hA.1)) hjoin
  rw [card_sup_eq_mul_of_normalizes_of_disjoint E K
    (hKE.trans (Subgroup.centralizer_le_normalizer _)) hEK,hcardE] at hmax
  let D := A ⊓ normalizer (L : Set G)
  have hKD : K ≤ D := le_inf hKA (hKC.trans (Subgroup.centralizer_le_normalizer _))
  let f : D →* MulAut L := L.normalizerMonoidHom.comp (inclusion (show D ≤ normalizer (L:Set G) from inf_le_right))
  have hfker : f.ker=K.subgroupOf D := by
    ext x
    change L.normalizerMonoidHom ⟨x,x.property.2⟩=1 ↔ (x:G) ∈ K
    change (⟨x,x.property.2⟩:normalizer (L:Set G)) ∈ L.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    change (x:G) ∈ centralizer (L:Set G) ↔ (x:G) ∈ A ∧ (x:G) ∈ centralizer (L:Set G)
    exact ⟨fun hx => ⟨x.property.1,hx⟩,And.right⟩
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (show D ≤ A from inf_le_left)
  have hfbound : Nat.card f.range ≤ Nat.card P := hb f.range
    (IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hcardD : Nat.card D=Nat.card K*Nat.card f.range := by
    rw [←index_ker,←f.ker.card_mul_index,hfker,
      Nat.card_congr (subgroupOfEquivOfLe hKD).toEquiv]
  have hidx : D.relIndex A ≤ 2 := by
    change (A ⊓ normalizer (L:Set G)).relIndex A ≤ 2
    rw [inf_relIndex_left]
    exact (relIndex_le_of_le_right hA.1 index_ne_zero_of_finite).trans hi
  have hcardA : Nat.card D*D.relIndex A=Nat.card A := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) D A bot_le (show D ≤ A from inf_le_left)
  have hupper : Nat.card A ≤ Nat.card K*Nat.card P*2 := by
    rw [←hcardA,hcardD]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hfbound) hidx
  have hbound : Nat.card P*Nat.card P ≤ Nat.card P*2 := by
    apply Nat.le_of_mul_le_mul_right (c:=Nat.card K) _ Nat.card_pos
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hmax.trans hupper
  have := Nat.le_of_mul_le_mul_left hbound (Nat.card_pos (α:=P))
  omega
end Theory.GroupTheory
