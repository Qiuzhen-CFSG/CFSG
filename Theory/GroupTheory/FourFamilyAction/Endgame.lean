module
public import Theory.GroupTheory.FourFamilyAction
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# A faithful four-family normalizer endgame

A two-group acts faithfully modulo J(M) on four subgroups. If M has the
nonregular Klein four image, the four-point calculation makes its Thompson
normalizer exactly its full normalizer. Either M is the whole two-group,
or that normalizer quotient is dihedral of order eight. A crossing swap
also gives the required lower bound on the normalizer of a mixed product.

Source application: Aschbacher--Smith C.6.1, printed p.165.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory.FourFamilyAction

theorem full_normalizes_pair : fullGroup ≤ normalizer (pairGroup : Set Perm) := by
  rintro p ⟨i,rfl⟩
  apply mem_normalizer_iff.mpr
  intro p
  exact (by decide +kernel : ∀ (i : Fin 8) (p : Perm),
    (∃ j, word j = p) ↔ ∃ j, word j = doubleWord i*p*(doubleWord i)⁻¹) i p

theorem mem_pair_iff (p : Perm) : p ∈ pairGroup ↔
    (p 0 = 0 ∨ p 0 = 1) ∧ (p 1 = 0 ∨ p 1 = 1) := by
  exact (by decide +kernel : ∀ p : Perm, (∃i,word i = p) ↔
    (p 0 = 0 ∨ p 0 = 1) ∧ (p 1 = 0 ∨ p 1 = 1)) p

theorem pair_card : Nat.card pairGroup = 4 := by
  let f : Fin 4 → pairGroup := fun i => ⟨word i,⟨i,rfl⟩⟩
  have hi : Function.Injective f := by
    intro i j he
    exact (by decide +kernel : Function.Injective word) (congrArg Subtype.val he)
  have hs : Function.Surjective f := by
    rintro ⟨p,i,rfl⟩
    exact ⟨i,rfl⟩
  simpa only [Nat.card_fin] using (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm

variable {G : Type*} [Group G] [Finite G]

theorem global_endgame
    (P M : Subgroup G) (hP : IsPGroup 2 P) (hMP : M ≤ P)
    (ρ : (P ⊓ normalizer (elementaryAbelianMaxJ M : Set G) : Subgroup G) →* Perm)
    (hker : ρ.ker = (elementaryAbelianMaxJ M).subgroupOf
      (P ⊓ normalizer (elementaryAbelianMaxJ M : Set G)))
    (himage : (M.subgroupOf (P ⊓ normalizer (elementaryAbelianMaxJ M : Set G))).map ρ = pairGroup)
    (f : Fin 4 → Subgroup G)
    (hequiv : ∀ g i, f (ρ g i) = (f i).map (MulAut.conj (g : G)).toMonoidHom) :
    let S := elementaryAbelianMaxJ M
    let N := P ⊓ normalizer (S : Set G)
    let : (S.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer inf_le_right
    N = P ⊓ normalizer (M : Set G) ∧
      (M = P ∨ Nonempty ((N ⧸ S.subgroupOf N) ≃* DihedralGroup 4) ∧
        2 * Nat.card S ≤ Nat.card (P ⊓ normalizer ((f 0 ⊔ f 2 : Subgroup G) : Set G) : Subgroup G)) := by
  let S := elementaryAbelianMaxJ M
  let N := P ⊓ normalizer (S : Set G)
  have hSM : S ≤ M := sSup_le (fun _ h => h.1)
  have hSN : S ≤ N := le_inf (hSM.trans hMP) S.le_normalizer
  have hMN : M ≤ N := le_inf hMP
    (M.le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ M))
  have hNk : ρ.ker ≤ M.subgroupOf N := hker ▸ subgroupOf_mono N hSM
  have hNtwo : IsPGroup 2 N := hP.to_le inf_le_left
  have hρtwo : IsPGroup 2 ρ.range := hNtwo.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have ha : leftSwap ∈ ρ.range :=
    (map_le_range ρ (M.subgroupOf N)) (himage.symm ▸ (show leftSwap ∈ pairGroup from ⟨1,rfl⟩))
  have hb : rightSwap ∈ ρ.range :=
    (map_le_range ρ (M.subgroupOf N)) (himage.symm ▸ (show rightSwap ∈ pairGroup from ⟨2,rfl⟩))
  have hrle := twoGroup_le_fullGroup ρ.range hρtwo ha hb
  have hpre : pairGroup.comap ρ = M.subgroupOf N := by
    rw [←himage,comap_map_eq,sup_of_le_left hNk]
  have hnM : N ≤ normalizer (M : Set G) := by
    intro g hg
    apply mem_normalizer_iff.mpr
    intro m
    have hcon (g : N) (m : N) (hm : (m : G) ∈ M) :
        (g : G)*(m : G)*(g : G)⁻¹ ∈ M := by
      have hmi : ρ m ∈ pairGroup := hpre.ge hm
      have hgi : ρ g ∈ normalizer (pairGroup : Set Perm) :=
        full_normalizes_pair (hrle ⟨g,rfl⟩)
      have hmi' : ρ (g*m*g⁻¹) ∈ pairGroup := by
        rw [map_mul,map_mul,map_inv]
        exact (mem_normalizer_iff.mp hgi (ρ m)).mp hmi
      exact hpre.le hmi'
    constructor
    · intro hm
      exact hcon ⟨g,hg⟩ ⟨m,hMN hm⟩ hm
    · intro hm
      have hmN : g*m*g⁻¹ ∈ N := hMN hm
      have hm' := hcon (⟨g,hg⟩ : N)⁻¹ ⟨g*m*g⁻¹,hmN⟩ hm
      simp only [Subgroup.coe_inv,inv_inv] at hm'
      simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hm' 
  have hN : N = P ⊓ normalizer (M : Set G) := by
    apply le_antisymm (le_inf inf_le_left hnM)
    exact le_inf inf_le_left
      (inf_le_right.trans (normalizer_le_normalizer_elementaryAbelianMaxJ M))
  refine ⟨hN,?_⟩
  rcases pair_or_full ρ.range hρtwo ha hb with he | he
  · left
    have hMN' : N ≤ M := by
      intro g hg
      exact hpre.le (he ▸ (show ρ (⟨g,hg⟩ : N) ∈ ρ.range from ⟨⟨g,hg⟩,rfl⟩))
    let : Group.IsNilpotent P := hP.isNilpotent
    have hself : normalizer (M.subgroupOf P : Set P) = M.subgroupOf P := by
      apply le_antisymm _ le_normalizer
      rw [←subgroupOf_normalizer_eq hMP]
      intro g hg
      exact hMN' (hN.symm ▸ (show (g : G) ∈ P ⊓ normalizer (M : Set G) from ⟨g.property,hg⟩))
    have ht := normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := P)) _ hself
    exact le_antisymm hMP (subgroupOf_eq_top.mp ht)
  · right
    let : (S.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer inf_le_right
    have e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange ρ).trans (MulEquiv.subgroupCongr he))
    obtain ⟨ed⟩ := fullGroup_dihedral
    refine ⟨⟨e.trans ed⟩,?_⟩
    obtain ⟨g,hg⟩ := (show crossSwap ∈ ρ.range from he.symm ▸
      (show crossSwap ∈ fullGroup from ⟨4,rfl⟩))
    let B := P ⊓ normalizer ((f 0 ⊔ f 2 : Subgroup G) : Set G)
    have hSB : S ≤ B := by
      apply le_inf (hSM.trans hMP)
      intro s hs
      have hsN := hSN hs
      have hsρ : ρ (⟨s,hsN⟩ : N) = 1 := show (⟨s,hsN⟩ : N) ∈ ρ.ker from hker.symm ▸ hs
      have hn (i : Fin 4) : s ∈ normalizer (f i : Set G) := by
        apply mem_normalizer_iff_map_conj_eq.mpr
        change (f i).map (MulAut.conj s).toMonoidHom = f i
        simpa only [hsρ,Equiv.Perm.one_apply] using (hequiv ⟨s,hsN⟩ i).symm
      exact (normalizer_inf_normalizer_le_normalizer_sup (f 0) (f 2)) ⟨hn 0,hn 2⟩
    have hgB : (g : G) ∈ B := by
      refine ⟨g.property.1,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
      change (f 0 ⊔ f 2).map (MulAut.conj (g : G)).toMonoidHom = _
      rw [Subgroup.map_sup,←hequiv g 0,←hequiv g 2,hg]
      change f 2 ⊔ f 0 = f 0 ⊔ f 2
      exact sup_comm _ _
    have hgS : (g : G) ∉ S := by
      intro hs
      have hh : ρ g = 1 := show g ∈ ρ.ker from hker.symm ▸ hs
      rw [hg] at hh
      exact (by decide +kernel : crossSwap ≠ 1) hh
    have hproper : S < B := lt_of_le_of_ne hSB (by intro he; exact hgS (he.symm ▸ hgB))
    have hi : 2 ≤ S.relIndex B := by
      have hp : 0 < S.relIndex B := (show 0 < (S.subgroupOf B).index from Nat.card_pos)
      have hn : S.relIndex B ≠ 1 := fun he => hproper.not_ge (relIndex_eq_one.mp he)
      omega
    have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) S B bot_le hSB
    rw [relIndex_bot_left,relIndex_bot_left] at hcard
    change 2 * Nat.card S ≤ Nat.card B
    nlinarith

end Theory.GroupTheory.FourFamilyAction
