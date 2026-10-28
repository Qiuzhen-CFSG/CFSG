module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ModuleGeometry
public import Theory.Representation.BinaryOffender.RankOneCentralizer
public import CFSG.Quasithin.ChapterE.Section06.Obstructions
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.Setup
public import CFSG.Quasithin.ChapterE.Section06.Defs
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Cases


/-!
# The common L₃ subspace geometry in 12.4.8

Every nonidentity element of the marked four-dimensional L₃ action fixes
at most a plane: a larger fixed space would give rank-one displacement,
hence an involution, contrary to the proved B.4.8 involution calculation.
Thus a hyperplane, or a plane together with the fixed line it misses,
has trivial pointwise stabilizer in the actual normalizer action.

The original L-action kernel is a two-group. Since T normalizes L and
supplements it in LT, the kernel on LT is also a two-group. Normality
then identifies its Sylow intersection with C_T(V), so LT normalizes
C_T(V). Together with source 1.2.7 this establishes the genuine E.6.1
hypotheses. Every escaping hyperplane and each of its planes belongs to
Γ, and E.6.5 gives the same literal Sylow subgroup in both centralizers.

This is the common preparation for the three cases, not their exclusion.
Source: Aschbacher–Smith, Lemma 12.4.8, first two paragraphs, printed p.815.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE
open Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

theorem marked_fixed_finrank_le_two (E : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥) (b : BinaryLinearThree.Group) (hb : b ≠ 1) :
    letI := D.elementary
    Module.finrank (ZMod 2) (fixedSpace E.action (zpowers b)) ≤ 2 := by
  let _ := D.elementary
  by_contra! hdim
  have hsum := fixedCodim_add_finrank E.action (zpowers b)
  rw [module_finrank_four E hne, fixedCodim_zpowers_eq_displacement_rank] at hsum
  have hle : Module.finrank (ZMod 2) (LinearMap.range (E.action b - LinearMap.id)) ≤ 1 := by
    omega
  have hnonzero : Module.finrank (ZMod 2)
      (LinearMap.range (E.action b - LinearMap.id)) ≠ 0 := by
    intro hz
    have he : E.action b = LinearMap.id :=
      sub_eq_zero.mp (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
    exact hb (action_injective E (he.trans (map_one E.action).symm))
  have hr : Module.finrank (ZMod 2) (LinearMap.range (E.action b - LinearMap.id)) = 1 := by
    omega
  have hsq : b ^ 2 = 1 := by
    apply action_injective E
    apply LinearMap.ext
    intro v
    have hf := fixes_displacement_of_commute_rank_one E.action b b hr (Commute.refl b) v
    rw [map_sub, ZModModule.sub_eq_add, ZModModule.sub_eq_add] at hf
    have hf' := add_right_cancel (hf.trans (add_comm (E.action b v) v))
    simpa only [pow_two, map_mul, Module.End.mul_apply, map_one,
      Module.End.one_apply] using hf'
  have hi := (involution_linear_plane E hne b (orderOf_eq_prime hsq hb)).2
  omega

theorem local_centralizer_of_card_gt_four (E : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hN : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v)
    (W : Subgroup G) (hWV : W ≤ V) (hW : 4 < Nat.card W) :
    normalizer (V : Set G) ⊓ centralizer (W : Set G) = centralizer (V : Set G) := by
  let _ := D.elementary
  apply le_antisymm
  · rintro n ⟨hn, hnW⟩
    obtain ⟨l, hl, hact⟩ := hN n hn
    let b := E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l, hl⟩)
    have hconj (v : Additive V) : ((E.action b v).toMul : G) =
        n * (v.toMul : G) * n⁻¹ :=
      (E.conjugation ⟨l, hl⟩ v).trans (hact v.toMul v.toMul.property).symm
    have hb : b = 1 := by
      by_contra hb
      have hf := marked_fixed_finrank_le_two E hne b hb
      let f : W → fixedSpace E.action (zpowers b) := fun w =>
        ⟨Additive.ofMul ⟨w, hWV w.property⟩, by
          rw [mem_fixedSpace_zpowers_iff]
          apply Additive.toMul.injective
          apply Subtype.ext
          rw [hconj]
          change n * (w : G) * n⁻¹ = (w : G)
          rw [← hnW w w.property, mul_inv_cancel_right]⟩
      have hinj : Function.Injective f := by
        intro x y he
        exact Subtype.ext (congrArg (fun z => (z.val.toMul : G)) he)
      have hc := Nat.card_le_card_of_injective f hinj
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := fixedSpace E.action (zpowers b)), Nat.card_zmod] at hc
      have hp : 2 ^ Module.finrank (ZMod 2) (fixedSpace E.action (zpowers b)) ≤ 2 ^ 2 :=
        Nat.pow_le_pow_right (by decide) hf
      omega
    intro v hv
    have he := hconj (Additive.ofMul ⟨v, hv⟩)
    rw [hb, map_one] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  · exact le_inf (Subgroup.centralizer_le_normalizer _) (centralizer_le hWV)

omit [Finite G] in
theorem normalizer_centralizes_fixed
    (hN : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v) :
    normalizer (V : Set G) ≤ centralizer (fixedSubgroup L V : Set G) := by
  intro n hn v hv
  obtain ⟨l, hl, he⟩ := hN n hn
  have hh := he v hv.1
  change n * v * n⁻¹ = l * v * l⁻¹ at hh
  rw [hv.2 l hl, mul_inv_cancel_right] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem local_centralizer_of_plane (E : SLThreeExtension D)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hN : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v)
    (W : Subgroup G) (hWV : W ≤ V) (hW : Nat.card W = 4)
    (hout : ¬ fixedSubgroup L V ≤ W) :
    normalizer (V : Set G) ⊓ centralizer (W : Set G) = centralizer (V : Set G) := by
  let J := W ⊔ fixedSubgroup L V
  have hJ : 4 < Nat.card J := by
    by_contra! hsmall
    have he : W = J := eq_of_le_of_card_ge le_sup_left (by omega)
    exact hout (he.symm ▸ (show fixedSubgroup L V ≤ J from le_sup_right))
  have hJV : J ≤ V := sup_le hWV inf_le_left
  have hlocal := local_centralizer_of_card_gt_four E hne hN J hJV hJ
  apply le_antisymm
  · rintro n ⟨hn, hc⟩
    apply hlocal.le
    refine ⟨hn, ?_⟩
    have hWC : W ≤ centralizer ({n} : Set G) := by
      intro w hw
      exact mem_centralizer_singleton_iff.mpr (hc w hw)
    have hZC : fixedSubgroup L V ≤ centralizer ({n} : Set G) := by
      intro z hz
      exact mem_centralizer_singleton_iff.mpr (normalizer_centralizes_fixed hN hn z hz)
    intro j hj
    exact mem_centralizer_singleton_iff.mp ((sup_le hWC hZC) hj)
  · exact le_inf (Subgroup.centralizer_le_normalizer _) (centralizer_le hWV)

theorem module_card (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥) :
    Nat.card V = 16 := by
  let _ := D.elementary
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  rw [Nat.card_zmod, module_finrank_four E hne] at hc
  exact hc

theorem hyperplane_card (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1) : Nat.card U = 8 := by
  let _ := D.elementary
  have hi : U.relIndex V = 2 := by
    rw [relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank, hcor, pow_one]
  have hc : Nat.card U * U.relIndex V = Nat.card V := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) U V bot_le hUV
  rw [hi, module_card E hne] at hc
  omega

theorem plane_card {U U₀ : Subgroup G}
    (hU : Nat.card U = 8) [IsElementaryAbelian 2 U]
    (hU₀U : U₀ ≤ U) (hcor : subgroupCorank U U₀ = 1) : Nat.card U₀ = 4 := by
  have hi : U₀.relIndex U = 2 := by
    rw [relIndex_eq_two_pow_quotient_finrank, ← subgroupCorank_eq_quotient_finrank, hcor, pow_one]
  have hc : Nat.card U₀ * U₀.relIndex U = Nat.card U := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) U₀ U bot_le hU₀U
  rw [hi, hU] at hc
  omega

theorem escaping_subspaces
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥)
    (hN : ∀ n ∈ normalizer (V : Set G), ∃ l ∈ L,
      ∀ v ∈ V, MulAut.conj n v = MulAut.conj l v)
    {U : Subgroup G} (hUV : U ≤ V) (hcor : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (V : Set G)) :
    Nat.card U = 8 ∧ ¬ fixedSubgroup L V ≤ U ∧
      normalizer (V : Set G) ⊓ centralizer (U : Set G) = centralizer (V : Set G) ∧
      U ∈ Section06.obstructionFamily (normalizer (V : Set G)) V ∧
      ∀ U₀ ≤ U, subgroupCorank U U₀ = 1 →
        Nat.card U₀ = 4 ∧ ¬ fixedSubgroup L V ≤ U₀ ∧
        normalizer (V : Set G) ⊓ centralizer (U₀ : Set G) = centralizer (V : Set G) ∧
        U₀ ∈ Section06.obstructionFamily (normalizer (V : Set G)) V := by
  let _ := D.elementary
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUV
  have hU := hyperplane_card E hne hUV hcor
  obtain ⟨z, _, hz, hM, hMV, _⟩ :=
    fixed_involution_setup_of_card_two h D structural (E.fixed_card_eq_two hne)
  have hZC : centralizer (fixedSubgroup L V : Set G) ≤ normalizer (V : Set G) := by
    rw [← hMV, hM]
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact (hx z (by rw [hz]; exact mem_zpowers z)).symm
  have hout : ¬ fixedSubgroup L V ≤ U :=
    fun hin => hescape ((centralizer_le hin).trans hZC)
  have hCU := local_centralizer_of_card_gt_four E hne hN U hUV (by omega)
  have hCV : normalizer (V : Set G) ⊓ centralizer (V : Set G) = centralizer (V : Set G) :=
    inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _)
  refine ⟨hU, hout, hCU, ⟨hUV, ?_, hescape,
    Section06.oddCentralizerCondition_of_eq (hCU.trans hCV.symm)⟩, ?_⟩
  · intro he
    rw [he, card_bot] at hU
    omega
  · intro U₀ hU₀U hcor₀
    have hc := plane_card hU hU₀U hcor₀
    have hout₀ : ¬ fixedSubgroup L V ≤ U₀ := fun hin => hout (hin.trans hU₀U)
    have hCU₀ := local_centralizer_of_plane E hne hN U₀ (hU₀U.trans hUV) hc hout₀
    refine ⟨hc, hout₀, hCU₀, hU₀U.trans hUV, ?_, ?_,
      Section06.oddCentralizerCondition_of_eq (hCU₀.trans hCV.symm)⟩
    · intro he
      rw [he, card_bot] at hc
      omega
    · exact fun hin => hescape ((centralizer_le hU₀U).trans hin)

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter12.Section04.SmallFusion
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in
theorem join_normalizes_sylow_centralizer (E : SLThreeExtension D)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    L ⊔ (T : Subgroup G) ≤ normalizer (sylowCentralizer (T : Subgroup G) V : Set G) := by
  let _ := D.elementary
  let H := L ⊔ (T : Subgroup G)
  have hHN : H ≤ normalizer (V : Set G) := sup_le D.normalizes hTV
  let f : H →* MulAut V := V.normalizerMonoidHom.comp (inclusion hHN)
  let R := L.subgroupOf H
  let S : Sylow 2 H := T.subtype le_sup_right
  let e : R ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let : R.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  have hgen : R ⊔ (S : Subgroup H) = ⊤ := by
    change L.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hk : IsPGroup 2 (f.comp R.subtype).ker := by
    have hep : IsPGroup 2 ((pCore 2 L).comap e.toMonoidHom) :=
      (pCore_isPGroup (p := 2) (G := L)).comap_of_injective e.toMonoidHom e.injective
    apply hep.to_le
    intro x hx
    change f (x : H) = 1 at hx
    let b := E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) (e x))
    have hb : b = 1 := by
      apply action_injective E
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [map_one]
      change ((E.action b v).toMul : G) = (v.toMul : G)
      rw [E.conjugation]
      exact congrArg (fun a : MulAut V => (a v.toMul : G)) hx
    change e x ∈ pCore 2 L
    apply (QuotientGroup.eq_one_iff (N := pCore 2 L) (e x)).mp
    exact E.quotientEquiv.injective (hb.trans (map_one E.quotientEquiv).symm)
  have hp : IsPGroup 2 f.ker := f.kernel_isPGroup_of_normal_supplement R S S.isPGroup' hgen hk
  have hKT : f.ker ≤ (S : Subgroup H) := hp.le_sylow_of_normal S
  have he : f.ker.map H.subtype = sylowCentralizer (T : Subgroup G) V := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      refine ⟨hKT hy, ?_⟩
      intro v hv
      have hh := congrArg (fun a : MulAut V => (a ⟨v, hv⟩ : G)) hy
      change (y : G) * v * (y : G)⁻¹ = v at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro x hx
      let y : H := ⟨x, (le_sup_right : (T : Subgroup G) ≤ H) hx.1⟩
      refine ⟨y, ?_, rfl⟩
      change f y = 1
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      change x * (v : G) * x⁻¹ = (v : G)
      rw [← hx.2 v v.property, mul_inv_cancel_right]
  rw [← he]
  apply le_normalizer_iff.mpr
  intro x hx y hy
  obtain ⟨y, hy, rfl⟩ := hy
  exact ⟨(⟨x, hx⟩ : H) * y * (⟨x, hx⟩ : H)⁻¹,
    (inferInstance : f.ker.Normal).conj_mem y hy ⟨x, hx⟩, rfl⟩

theorem source_hypothesisE61
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥) :
    HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (V : Set G)) V := by
  have hs := structural G T L h
  have hOrbit : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit L _)
    exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) L le_rfl hs.1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    h.simpleQTKE T h.maximal_faithful.1
  obtain ⟨z, hz, hfix, hM, hMV, _⟩ :=
    fixed_involution_setup_of_card_two h D structural (E.fixed_card_eq_two hne)
  have hmax : IsMaximalTwoLocal (normalizer (V : Set G)) := by
    simpa only [hOrbit, hMV] using hu.normalizer_maximal
  have hTV := (hs.2.2 V D).1
  refine ⟨h.simpleQTKE, hmax, hTV, D.ne_bot, D.elementary, D.le_sylow,
    (normal_subgroupOf_iff_le_normalizer D.le_sylow).mpr hTV, ?_, ?_⟩
  · intro g hg
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp hg)
  · intro N hN hle
    have he : N = normalizer (L : Set G) := by
      simpa only [hOrbit] using hu.normalizer_unique N hN
        ((le_inf (le_inf (sup_le D.normalizes hTV) (sup_le D.normalizes hTV))
          (join_normalizes_sylow_centralizer E hs.1 hTV)).trans hle)
    exact he.trans hMV

/-- The actual E.6.5 application to U and every hyperplane U₀ of U.
Both Sylow subgroups have ambient image C_T(V); no conjugacy replacement
or alternative two-subgroup is introduced. -/
theorem Configuration.sylow_centralizers {U : Subgroup G}
    (c : Configuration T L V U) :
    Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
        (centralizer (U : Set G)) ∧
      ∀ U₀ ≤ U, subgroupCorank U U₀ = 1 →
        Chapter1.IsSylowIn 2 (sylowCentralizer (T : Subgroup G) V)
          (centralizer (U₀ : Set G)) := by
  have hE := source_hypothesisE61 c.hypothesis c.structural
    c.extension c.fixed_nontrivial
  have hg := escaping_subspaces c.hypothesis c.structural c.extension
    c.fixed_nontrivial c.normalizer_action c.le_module c.corank c.escape
  exact ⟨hE.sylow_obstruction hg.2.2.2.1, fun U₀ hU₀ hcor =>
    hE.sylow_obstruction (hg.2.2.2.2 U₀ hU₀ hcor).2.2.2⟩

end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
