module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.Coprimality
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosure
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.SmallSylow

/-!
# The size of the original nonnormal full module

The two distinct conjugate C-components have commuting images in the
actual conjugation action on the full module. The ambient two-core acts
trivially. Each component image is a nontrivial simple perfect group, so
its order is divisible by four. Their commuting, centerless product
therefore forces sixteen to divide the automorphism-group order. This
is impossible for an elementary abelian two-group of order at most eight.

The result supplies the large-module branch of the odd-core argument in
4.4.8. It uses no irreducibility choice and no model marking on the module.
Source: Aschbacher--Smith, 1.2.1--2 and 4.4.8, printed pp.503--504,620,
combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10

private theorem four_dvd_simple_perfect (S : Type*) [Group S] [Finite S]
    [IsSimpleGroup S] [Group.IsPerfect S] : 4 ∣ Nat.card S := by
  let P : Sylow 2 S := Classical.choice inferInstance
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have hlarge := CFSG.Quasithin.Chapter1.Section02.IndexTwo.two_lt_card_sylow_of_simple_perfect P
  have htwo : 2 ≤ n := by
    by_contra hh
    have hh' : n ≤ 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh'
    rw [←hn] at hp
    norm_num at hp
    omega
  exact (show 2 ^ 2 ∣ Nat.card P by rw [hn]; exact pow_dvd_pow 2 htwo).trans
    P.toSubgroup.card_subgroup_dvd_card

private theorem small_aut_not_sixteen (V : Type*) [Group V] [Finite V]
    [IsElementaryAbelian 2 V] (hsmall : Nat.card V ≤ 8) :
    ¬ 16 ∣ Nat.card (MulAut V) := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  have hbound : n ≤ 3 := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ n)
    rw [←hn] at hp
    norm_num at hp
    omega
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow V n hn]
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

private theorem simple_perfect_center (S : Type*) [Group S]
    [IsSimpleGroup S] [Group.IsPerfect S] : center S = ⊥ := by
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h)).elim

private theorem map_conjugate {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A : Subgroup G) (t : G) :
    (A.conjBy t).map f = (A.map f).conjBy (f t) := by
  change (A.map (MulAut.conj t).toMonoidHom).map f =
    (A.map f).map (MulAut.conj (f t)).toMonoidHom
  rw [map_map,map_map]
  congr 1
  ext a
  simp

private theorem component_image_simple {G H : Type*} [Group G] [Finite G] [Group H]
    (A : Subgroup G) (hA : A.IsCComponent) [IsSimpleGroup (A ⧸ pCore 2 A)]
    (f : G →* H) (hcore : pCore 2 G ≤ f.ker) (hne : A.map f ≠ ⊥) :
    IsSimpleGroup (A.map f) := by
  let : Nontrivial (A.map f) := (A.map f).nontrivial_iff_ne_bot.mpr hne
  let g := f.subgroupMap A
  have hg : pCore 2 A ≤ g.ker := by
    intro a ha
    apply Subtype.ext
    exact hcore (pCoreIn_le_of_subnormal 2 hA.subnormal (mem_map_of_mem A.subtype ha))
  let q : (A ⧸ pCore 2 A) →* A.map f := QuotientGroup.lift _ g hg
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨b,rfl⟩ := f.subgroupMap_surjective A a
    exact ⟨QuotientGroup.mk' (pCore 2 A) b,rfl⟩
  exact IsSimpleGroup.isSimpleGroup_of_surjective q hq

private theorem sixteen_dvd_pair_image {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] (A : Subgroup G) (hA : A.IsCComponent)
    [IsQuasisimple (A ⧸ pCore 2 A)] [IsSimpleGroup (A ⧸ pCore 2 A)]
    (t : G) (ht : t ∉ normalizer (A : Set G))
    (f : G →* H) (hcore : pCore 2 G ≤ f.ker) (hne : A.map f ≠ ⊥) :
    16 ∣ Nat.card H := by
  let B := A.map f
  let C := B.conjBy (f t)
  let : IsSimpleGroup B := component_image_simple A hA f hcore hne
  let := hA.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := f.subgroupMap A) (f.subgroupMap_surjective A)
  let e : B ≃* C := (MulAut.conj (f t)).subgroupMap B
  let : IsSimpleGroup C := e.symm.isSimpleGroup
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hc0 : ⁅A,A.conjBy t⁆ ≤ pCore 2 G := by
    have hc := TwoOrbitThree.quotient_pair_commutes hA t ht
    rw [←map_conjugate,←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at hc
    exact hc
  have hc : ⁅B,C⁆ = ⊥ := by
    change ⁅A.map f,(A.map f).conjBy (f t)⁆ = ⊥
    rw [←map_conjugate,←map_commutator,Subgroup.map_eq_bot_iff]
    exact hc0.trans hcore
  obtain ⟨eBC,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting B C
    (disjoint_of_commuting_of_center_eq_bot hc (simple_perfect_center B))
    (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hd : 16 ∣ Nat.card (B ⊔ C : Subgroup H) := by
    rw [←Nat.card_congr eBC.toEquiv,Nat.card_prod]
    exact Nat.mul_dvd_mul (four_dvd_simple_perfect B) (four_dvd_simple_perfect C)
  exact hd.trans (B ⊔ C).card_subgroup_dvd_card

open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original full module in a nonnormal setup has more than eight elements. -/
theorem source_nonnormal_fullModule_card_gt_eight
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    8 < Nat.card D.fullModule := by
  classical
  let M := D.maximalLocal
  let V := D.fullModule
  let A := L.subgroupOf M
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  let f : M →* MulAut V := V.normalizerMonoidHom.comp
    (inclusion D.maximalLocal_normalizes_fullModule)
  have hcore : pCore 2 M ≤ f.ker := by
    intro m hm
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change (m : G) * (v : G) * (m : G)⁻¹ = v
    obtain ⟨v',hv',hv⟩ := D.fullModule_le_reduced hu v.property
    have hc := congrArg Subtype.val
      (reducedPSubgroup_le_centralizer_pCore 2 M hv' m hm)
    change (m : G) * (v' : G) = (v' : G) * (m : G) at hc
    change (v' : G) = (v : G) at hv
    rw [hv] at hc
    rw [hc,mul_inv_cancel_right]
  have hne : A.map f ≠ ⊥ := by
    intro he
    have hLC : L ≤ centralizer (V : Set G) := by
      intro l hl v hv
      have hi : f ⟨l,hLM hl⟩ = 1 := mem_bot.mp
        (he ▸ mem_map_of_mem f (show (⟨l,hLM hl⟩ : M) ∈ A from hl))
      have hh := congrArg (fun a : MulAut V => (a ⟨v,hv⟩ : G)) hi
      change l * v * l⁻¹ = v at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    exact source_full_moved_ne_bot D
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hLC))
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  let tM : M := ⟨t,hTM ht⟩
  have htnM : tM ∉ normalizer (A : Set M) := by
    rw [←subgroupOf_normalizer_eq hLM]
    exact htn
  let e : (A ⧸ pCore 2 A) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM) (pCore_map_iso 2 _)
  let := D.quasisimple
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv e.symm
  let Q := L ⧸ pCore 2 L
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let eQ : (Q ⧸ center Q) ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq (source_nonnormal_component_core_center D hn)).trans
      QuotientGroup.quotientBot
  let : IsSimpleGroup Q := eQ.symm.isSimpleGroup
  let : IsSimpleGroup (A ⧸ pCore 2 A) := e.isSimpleGroup
  have h16 := sixteen_dvd_pair_image A D.component_in_maximalLocal tM htnM f hcore hne
  by_contra hh
  exact small_aut_not_sixteen V (Nat.le_of_not_gt hh) h16

end CFSG.Quasithin.Chapter10
