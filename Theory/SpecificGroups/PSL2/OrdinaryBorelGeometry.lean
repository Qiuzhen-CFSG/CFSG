module
public import Theory.SpecificGroups.SL2.NormalBorelCore
public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.LocalStructure
public import Theory.GroupTheory.GeneralizedFitting.ThompsonNormalizerLayer
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupAction.InnerSylowNormalizer
public import Theory.ElementaryAbelian.Injective

/-!
# Binary PSL₂ Borel geometry for ordinary components

The projective Borel is two-perfect for q ≥ 4. Semilinear coverage reduces
its pointwise automorphism fixer to an inner root element; the diagonal
complement then kills that element. A nonidentity Sylow element detects the
component normalizer, so the centralizer comparison holds for relative
components without an ambient normality hypothesis.

When the field degree is odd, every two-group actor is inner. The elementary
component Sylow centralizes the component stabilizer in S, and replacement
forces J(S) into that stabilizer. The Borel consequently normalizes J(S),
including when S exchanges two components.
Source: Aschbacher--Smith 15.1.21(i), printed pp.1097--1098; the intrinsic
matrix and semilinear inputs are imported from the existing PSL₂ development.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace Theory.PSL2.OrdinaryBorel
open Matrix.ProjectiveSpecialLinearGroup OddBorel EvenBorelResidual
open BenderSuzuki.Converse
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem borel_fixer {n : ℕ} (hF : Nat.card F = 2^n) (hq : 2 < Nat.card F)
    (α : MulAut PSL(2,F)) (hfix : ∀ x ∈ borel F, α x=x) : α=1 := by
  have hU : (kernel F).map α.toMonoidHom = kernel F := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change α x ∈ kernel F
      rw [hfix x ((show kernel F ≤ borel F from le_sup_left) hx)]
      exact hx
    · intro x hx
      exact ⟨x,hx,hfix x ((show kernel F ≤ borel F from le_sup_left) hx)⟩
  obtain ⟨g,hg⟩ := Semilinear.inner_of_borel_quotient_fixed hF α hU
    (fun x hx => by rw [hfix x hx,inv_mul_cancel]; exact one_mem _)
  have hc : g ∈ centralizer ({pi F (uni (1:F))} : Set PSL(2,F)) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := hfix (unipotentHom F (Multiplicative.ofAdd (1:F))) ((show kernel F ≤ borel F from le_sup_left) ⟨_,rfl⟩)
    rw [hg] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  rw [Theory.PSL2.centralizer_root_eq one_ne_zero] at hc
  have hk : g ∈ kernel F := by
    obtain ⟨u,hu,rfl⟩ := hc
    obtain ⟨t,rfl⟩ := (mem_Unip_iff u).mp hu
    exact ⟨Multiplicative.ofAdd t,rfl⟩
  have hlarge : 1 < Nat.card (complement F) := by rw [card_torus]; omega
  let : Nontrivial (complement F) := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨c,hcne⟩ := exists_ne (1 : complement F)
  have hh := hfix c ((show complement F ≤ borel F from le_sup_right) c.property)
  rw [hg] at hh
  have hcomm : (c : PSL(2,F))*g*(c : PSL(2,F))⁻¹=g :=
    mul_inv_eq_iff_eq_mul.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hgone : g=1 := congrArg Subtype.val (fixedPointFree F c hcne ⟨g,hk⟩ hcomm)
  rw [hg,hgone,map_one]

theorem normalizer_fixer {n : ℕ} (hF : Nat.card F=2^n) (hq : 2 < Nat.card F)
    (P : Sylow 2 PSL(2,F)) (α : MulAut PSL(2,F))
    (hfix : ∀ x ∈ normalizer (P : Set PSL(2,F)), α x=x) : α=1 := by
  obtain ⟨g,_,hg⟩ := sylow_normalizer_conjugate F P
  let e := MulAut.conj g
  have hα : MulAut.congr e.symm α=1 := borel_fixer hF hq _ (by
    intro x hx
    change e.symm (α (e x))=x
    rw [hfix (e x) (hg ▸ mem_map_of_mem e.toMonoidHom hx),e.symm_apply_apply])
  exact (MulAut.congr e.symm).injective (hα.trans (map_one _).symm)

theorem normalizer_twoPerfect (hq : 4 ≤ Nat.card F) (P : Sylow 2 PSL(2,F)) :
    IsPPerfect 2 (normalizer (P : Set PSL(2,F))) :=
  (borel_isPPerfect F hq).of_surjective (sylowNormalizerEquiv F P).symm.toMonoidHom
    (sylowNormalizerEquiv F P).symm.surjective

theorem sylow_elementary (P : Sylow 2 PSL(2,F)) : IsElementaryAbelian 2 P := by
  let : IsElementaryAbelian 2 (Multiplicative F) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Multiplicative.toAdd.injective
        change (x^2).toAdd = 0
        rw [pow_two]
        exact CharTwo.add_self_eq_zero x.toAdd) }
  exact IsElementaryAbelian.of_surjective
    (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive P).toMonoidHom
    (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive P).surjective

theorem sylow_card (P : Sylow 2 PSL(2,F)) : Nat.card P = Nat.card F := by
  rw [← Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive P).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

variable {G : Type*} [_root_.Group G] [Finite G]

/-- Odd field degree makes the Borel normalize J(S), even on an orbit of two components. -/
theorem component_normalizer_thompson_of_odd
    (H L S : Subgroup G) (hLH : L ≤ H) (hSH : S ≤ H)
    (hL : IsComponent H (L.subgroupOf H)) (hS : IsPGroup 2 S)
    (hi : (normalizer (L : Set G)).relIndex S ≤ 2)
    (P : Sylow 2 L) (hPS : (P : Subgroup L).map L.subtype ≤ S)
    {n : ℕ} (hn : Odd n) (hF : Nat.card F=2^n) (hq : 2 < Nat.card F)
    (e : L ≃* PSL(2,F)) :
    (normalizer (P : Set L)).map L.subtype ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
  let Q := S ⊓ normalizer (L : Set G)
  have hQ : IsPGroup 2 Q := hS.to_le inf_le_left
  have hQL : Q ≤ normalizer (L : Set G) := inf_le_right
  have hPQ : (P : Subgroup L).map L.subtype ≤ Q :=
    le_inf hPS ((map_subtype_le _).trans L.le_normalizer)
  have hinner (s : Q) : ∃ l : L,
      L.normalizerMonoidHom ⟨s,hQL s.property⟩ = MulAut.conj l := by
    let f : Q →* MulAut PSL(2,F) := (MulAut.congr e).toMonoidHom.comp
      (L.normalizerMonoidHom.comp (inclusion hQL))
    obtain ⟨k,hk⟩ := hQ s
    have hp : f s ^ (2^k)=1 := by rw [←map_pow,hk,map_one]
    have ho : Odd (MulAut.conj : PSL(2,F) →* MulAut PSL(2,F)).range.index := by
      change Odd (Nat.card (MulAut.Outer PSL(2,F)))
      rwa [Theory.PSL2.outer_card_eq_field_degree F hF]
    exact (MulAut.congr_inner_iff e _).mp
      (MulAut.inner_of_two_pow_eq_one_of_odd_index ho (f s) hp)
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 R := sylow_elementary R
  let eP : P ≃* R := e.subgroupMap (P : Subgroup L)
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.of_injective eP.toMonoidHom eP.injective
  let E := (P : Subgroup L).map L.subtype
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map L.subtype
  have hEC : E ≤ centralizer (Q : Set G) := by
    have hc := sylowCenter_le_centralizer_of_inner_action L Q hQ hQL P hPQ hinner
    rw [(center_eq_top (G:=P)),←MonoidHom.range_eq_map,range_subtype] at hc
    exact hc
  have hz : center L=⊥ := by
    apply bot_unique
    intro l hl
    have hh : e l ∈ center PSL(2,F) := (centerCongr e ⟨l,hl⟩).property
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact mem_bot.mpr (e.injective (hh.trans e.map_one.symm))
  have hd : Disjoint E (centralizer (L : Set G)) := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hxL : x ∈ L := (map_subtype_le _ : E ≤ L) hx.1
    have hh : (⟨x,hxL⟩ : L) ∈ center L :=
      mem_center_iff.mpr (fun l => Subtype.ext (hx.2 l l.property))
    exact mem_bot.mpr (congrArg (fun l : L => (l:G)) (mem_bot.mp (hz ▸ hh)))
  have hcard : 2 < Nat.card E := by
    rw [show E=(P : Subgroup L).map L.subtype from rfl,card_map_of_injective L.subtype_injective]
    rw [Nat.card_congr (e.subgroupMap (P : Subgroup L)).toEquiv]
    change _ < Nat.card R
    rw [sylow_card R]
    exact hq
  have hJN := IsComponent.maxJ_le_relative_normalizer_of_central_elementary
    H L S E hLH hSH hL hi (map_subtype_le _) hPS hEC hd hcard
  have hJ : elementaryAbelianMaxJ Q=elementaryAbelianMaxJ S :=
    elementaryAbelianMaxJ_eq_of_intermediate S Q
      (le_inf (sSup_le fun _ hA => hA.1) hJN) inf_le_left
  rw [←hJ]
  exact (sylowNormalizer_le_normalizer_of_inner_action L Q hQ hQL P hPQ hinner).trans
    (normalizer_le_normalizer_elementaryAbelianMaxJ Q)

/-- Centralizing the Borel of a relative PSL₂ component centralizes that component. -/
theorem relative_centralizer
    (H L : Subgroup G) (hLH : L ≤ H) (hL : IsComponent H (L.subgroupOf H))
    {n : ℕ} (hF : Nat.card F=2^n) (hq : 2 < Nat.card F)
    (e : L ≃* PSL(2,F)) (P : Sylow 2 L) :
    H ⊓ centralizer ((normalizer (P : Set L)).map L.subtype : Set G) ≤
      centralizer (L : Set G) := by
  let R := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hz : center L=⊥ := by
    apply bot_unique
    intro l hl
    have hh : e l ∈ center PSL(2,F) := (centerCongr e ⟨l,hl⟩).property
    rw [BenderSuzuki.ZD.Linear.psl2_center_eq_bot,mem_bot] at hh
    exact mem_bot.mpr (e.injective (hh.trans e.map_one.symm))
  have hp : 1 < Nat.card P := by
    rw [Nat.card_congr (e.subgroupMap (P : Subgroup L)).toEquiv]
    change _ < Nat.card R
    rw [sylow_card R]
    omega
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp hp
  obtain ⟨r,hrne⟩ := exists_ne (1:P)
  let rH : H := ⟨r,hLH r.val.property⟩
  have hrnon : rH ∉ centralizer (L.subgroupOf H : Set H) := by
    intro hr
    have hh : r.val ∈ center L := mem_center_iff.mpr (fun l =>
      Subtype.ext (congrArg (fun x : H => (x:G)) (hr ⟨l,hLH l.property⟩ l.property)))
    exact hrne (Subtype.ext (mem_bot.mp (hz ▸ hh)))
  rintro x ⟨hxH,hxB⟩
  have hxN : x ∈ normalizer (L : Set G) := by
    have hh := hL.normalizes_of_noncentral_element ⊥ bot_le (⟨x,hxH⟩:H) rH
      r.val.property hrnon ((show Commute (⟨x,hxH⟩:H) rH from
        Subtype.ext (hxB r (mem_map_of_mem L.subtype
          ((P : Subgroup L).le_normalizer r.property))).symm).map (QuotientGroup.mk' ⊥))
    rwa [←subgroupOf_normalizer_eq hLH] at hh
  let α := L.normalizerMonoidHom ⟨x,hxN⟩
  have hBN : (normalizer (P : Set L)).map e.toMonoidHom = normalizer (R : Set PSL(2,F)) :=
    map_equiv_normalizer_eq (P : Subgroup L) e
  have hα : α=1 := by
    apply (MulAut.congr e).injective
    rw [map_one]
    apply normalizer_fixer hF hq R
    intro y hy
    rw [←hBN] at hy
    obtain ⟨l,hl,rfl⟩ := hy
    change e (α (e.symm (e l)))=e l
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    change x*(l:G)*x⁻¹=l
    exact mul_inv_eq_iff_eq_mul.mpr (hxB l (mem_map_of_mem L.subtype hl)).symm
  intro l hl
  have hh := congrArg Subtype.val (DFunLike.congr_fun hα (⟨l,hl⟩:L))
  change x*l*x⁻¹=l at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end Theory.PSL2.OrdinaryBorel
