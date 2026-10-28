module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldQrc
public import Theory.GroupAction.BinarySingerRegularity
public import Theory.ElementaryAbelian.SingerCubicBound

/-!
# The original Hermitian degree bound and small Cartan generation

The plus torus acts regularly on the nonidentity elements of its literal
omega-span. The original Sylow subgroup normalizes the torus preimage
(T intersect L)Dplus, and T intersect L centralizes that span. Hence the
entire action image normalizes the regular cyclic torus image; normalization
of Dplus itself is unnecessary. The Singer involution bound and the proved
qrc cubic bound give at most sixteen vectors, so the original degree is at
most eight. Its already proved divisibility by four leaves four or eight.

The actual small-generation consumers at those two degrees supply the
cubic/quintic factors. This removes the numerical-output premise throughout
the Hermitian escape branch. The original omega-span model remains explicit;
selecting that model among the source alternatives is a separate obligation.

Source: Aschbacher--Smith 5.1.6(4), pp.632--633, and its 5.2.2 application,
p.647 (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
open scoped IsMulCommutative
open Representation.OrthogonalFourMinus.FiniteModel
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
local instance (s : ℕ) : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

omit [Finite G] in
private theorem image_normalizes_torus
    {J U D X : Subgroup G} (hJ : J ≤ normalizer (X : Set G))
    (hUJ : U ≤ J) (hDJ : D ≤ J)
    (hUC : U ≤ centralizer (X : Set G))
    (hn : J ≤ normalizer ((U ⊔ D : Subgroup G) : Set G)) :
    internalActionImage J X hJ ≤
      normalizer ((internalActionImage D X (hDJ.trans hJ)) : Set (MulAut X)) := by
  let f := actionHom J X hJ
  have hU : (U.subgroupOf J).map f = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    change U.subgroupOf J ≤ (actionHom J X hJ).ker
    rw [actionHom_ker]
    exact fun _ hx => hUC hx
  have hD : (D.subgroupOf J).map f = internalActionImage D X (hDJ.trans hJ) := by
    rw [←inclusion_range hDJ,←MonoidHom.range_comp]
    rfl
  have he : ((U ⊔ D).subgroupOf J).map f =
      internalActionImage D X (hDJ.trans hJ) := by
    rw [subgroupOf_sup hUJ hDJ,Subgroup.map_sup,hU,bot_sup_eq,hD]
  rintro a ⟨j,rfl⟩
  rw [←he]
  apply ((U ⊔ D).subgroupOf J).le_normalizer_map f
  apply mem_map_of_mem f
  exact (le_normalizer_comap J.subtype) (hn j.property)

/-- Zero core of the actual plus-torus join bounds the original degree,
using the regular torus image and the literal qrc action. -/
theorem Input.hermitian_degree_le_eight_of_plus_zero_core
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s] (hs : 1 < s)
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s))
    (hDA : D ≤ A) (hDc : Nat.card D = 2^s-1)
    (hz : (D ⊔ H).pCoreIn 2 = ⊥) : n ≤ 8 := by
  let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) D
  let J := D ⊔ (T : Subgroup G)
  let U := (T : Subgroup G) ⊓ L
  let hq := h.hermitian_plus_qrc_hypotheses hH c s hs hm hDA hDc
  let := hq.module_elementary
  have hg := h.hermitian_plus_span c s hm hDA hDc
  have hJ : J ≤ normalizer (X : Set G) := hq.module_normalized
  let f := actionHom D X (le_sup_left.trans hJ)
  let C := internalActionImage D X (le_sup_left.trans hJ)
  obtain ⟨F,_,_,_,_,⟨e⟩⟩ := c.left_equiv_units h.linear h.sylow_normalizes
  let : IsCyclic A := isCyclic_of_injective e.toMonoidHom e.injective
  let : IsCyclic D := isCyclic_of_injective (inclusion hDA) (inclusion_injective hDA)
  let : IsCyclic C := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [actionHom_ker]
    apply _root_.eq_bot_iff.mpr
    intro d hd
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hg.2.2.2 ▸ (show (d:G) ∈ D ⊓ centralizer (X : Set G) from
      ⟨d.property,hd⟩))
  have hregD := Theory.GroupAction.faithful_cyclic_binary_singer_regular f hfi hs hDc hg.2.1
  have hreg : ∀ v w : X, v ≠ 1 → w ≠ 1 → ∃! a : C, a.val v = w := by
    intro v w hv hw
    obtain ⟨d,hd,hu⟩ := hregD v w hv hw
    refine ⟨f.rangeRestrict d,hd,?_⟩
    intro a ha
    obtain ⟨b,hb⟩ := f.rangeRestrict_surjective a
    rw [←hb] at ha ⊢
    exact congrArg f.rangeRestrict (hu b ha)
  have hTB : (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) :=
    (le_inf h.sylow_normalizes
      ((le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
        inf_normalizer_le_normalizer_inf |>.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ normalizer ((U ⊔ D : Subgroup G) : Set G) :=
    hTB.trans (Prime.cartan_subgroup_preimage_normalized c h.sylow_normalizes h.linear hDA)
  have hUC : U ≤ centralizer (X : Set G) := by
    apply le_centralizer_iff.mp
    change conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) D ≤ _
    rw [hg.1]
    exact inf_le_right
  have hN : internalActionImage J X hJ ≤ normalizer (C : Set (MulAut X)) :=
    image_normalizes_torus hJ (inf_le_left.trans le_sup_right) le_sup_left hUC
      (sup_le (le_sup_right.trans (U ⊔ D).le_normalizer) hTN)
  have hc := regular_cyclic_normalizer_cubic_card_le C (internalActionImage J X hJ)
    hreg hN (imageRepresentation J X hJ) (fun _ _ => rfl)
      (h.hermitian_plus_cubicRatio_le_two hH c s hs hm hDA hDc hz)
  rw [hg.2.1] at hc
  have hs4 : s ≤ 4 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have he := h.exponent_of_hermitian_model s hm
  omega

/-- Universal local control and escape force degree four or eight in the
original Hermitian omega-span branch. -/
theorem Input.hermitian_degree_four_or_eight_of_escape
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hn : 2 < n)
    (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G)) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s)) : n = 4 ∨ n = 8 := by
  obtain ⟨hfour,Dm,Dp,hjoin,hmc,hpc,hcentral,hcore,hmN,hzero⟩ :=
    h.hermitian_torus_of_escape hH c hn hcontrol hescape s hm
  have he := h.exponent_of_hermitian_model s hm
  have hs : 1 < s := by omega
  have hDc : Nat.card Dp = 2^s-1 := by simpa only [show n/2=s by omega] using hpc
  have hb := h.hermitian_degree_le_eight_of_plus_zero_core hH c s hs hm
    (hjoin ▸ le_sup_right) hDc hzero
  omega

/-- The actual degree-four/eight factor constructions now discharge small
Cartan generation in this branch, without a numerical reduction premise. -/
theorem Input.cartanSmallGeneration_of_hermitian_escape
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hn : 2 < n)
    (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G)) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s)) : CartanSmallGeneration A H n := by
  rcases h.hermitian_degree_four_or_eight_of_escape hH c hn hcontrol hescape s hm with he | he
  · exact h.cartanSmallGeneration_of_degree_two_or_four hH c (Or.inr he)
  · subst n
    exact h.cartanSmallGeneration_of_hermitian_degree_eight_model hH c s hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
