module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenSetup
public import CFSG.Quasithin.Chapter15.Section02.InvolutionLayers
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan

/-!
# The terminal contradiction for the literal chosen module

We transport the local normal-closure calculation through the subtype of the
actual member `H` of `HStar`. Thus the orbit span is precisely `conjugateSpan H V`
and its core is precisely `twoCoreIn H`. The prepared chosen module supplies
elementarity of that span. The source overlap theorem then makes the two
endpoint planes disjoint, and the two E.3.6 applications give the contradiction.

This is a conditional endgame, not a proof of all of Section 15.2. Its remaining
inputs are the distinguished plane and its normality (15.2.11--15), containment
of the Sylow involutions (15.2.25), the global parameter bound (15.2.26), the
overlap implication (15.2.27(3)), and the corank-one critical pair on p.1120.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.2.28 and
the terminal argument, printed pp.1119--1120.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section02

open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor ChapterE

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Original 15.2.28 on the literal ambient orbit span and embedded local core. -/
theorem source_chosen_involution_bound
    (T : Sylow 2 G) (H V S ZS : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hVH : V ≤ H)
    (hST : S ≤ (T : Subgroup G)) (hZV : ZS ≤ V)
    (hHZ : H ≤ normalizer (ZS : Set G))
    (hTS : ∀ x ∈ (T : Subgroup G), x ^ 2 = 1 → x ∈ S)
    (hcomm : ⁅V, S⁆ ≤ ZS) :
    ⁅conjugateSpan H V, involutionGenerated (twoCoreIn H)⁆ ≤ ZS := by
  have hSH : S ≤ H := hST.trans hTH
  have hZH : ZS ≤ H := hZV.trans hVH
  let : (ZS.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHZ
  have hQT : pCore 2 H ≤ (T : Subgroup G).subgroupOf H :=
    pCore_isPGroup.le_sylow_of_normal (T.subtype hTH)
  have hc : ⁅V.subgroupOf H, S.subgroupOf H⁆ ≤ ZS.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hVH, map_subgroupOf_eq_of_le hSH]
    exact hcomm
  have hb := source_local_normalClosure_involution_bound H
    (V.subgroupOf H) (pCore 2 H) ((T : Subgroup G).subgroupOf H)
    (S.subgroupOf H) (ZS.subgroupOf H) hQT
    (fun x hx hx2 => hTS x hx (congrArg H.subtype hx2)) hc
  rw [normalClosure_subgroupOf_eq_conjugateSpanBy V H hVH,
    map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hVH),
    map_subgroupOf_eq_of_le hZH] at hb
  simpa only [conjugateSpan_eq, twoCoreIn] using hb

/-- The literal source application; the orbit-span and disjoint-plane inputs of
the earlier critical-pair lemma are derived, rather than assumed. -/
theorem source_chosen_contradiction_of_critical_pair
    (T : Sylow 2 G) {M Mc V : Subgroup G} (hsource : ChosenSmallSource T M Mc V)
    (H ZS : Subgroup G) (hgeometry : ChosenPlaneGeometry hsource H ZS)
    (hTS : ∀ x ∈ (T : Subgroup G), x ^ 2 = 1 →
      x ∈ (T : Subgroup G) ⊓ centralizer (ZS : Set G))
    (hcomm : ⁅V, (T : Subgroup G) ⊓ centralizer (ZS : Set G)⁆ ≤ ZS)
    (hs : letI := hsource.prepared.elementary; 1 < globalS V)
    (hoverlap : ∀ g : G, ZS ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (g : G)
    (hfirst : subgroupCorank V (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) ≤ 1)
    (hsecond : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) ≤ 1)
    (hmove : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : False := by
  let := hsource.prepared.elementary
  have hH := hgeometry.outside
  let := (hsource.prepared.chief_data hsource.ambient T hsource.empty
    hsource.maximal hsource.centralizing H hH).1
  have hVH : V ≤ H := (hsource.prepared.inside_core H hH).trans (twoCore_le H)
  have hVU : V ≤ conjugateSpan H V := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hcenters : ZS ⊓ ZS.map (MulAut.conj g).toMonoidHom = ⊥ := by
    by_contra hn
    apply hmove (hoverlap g ?_)
    intro he
    exact hn (bot_unique
      ((inf_le_inf_left ZS (map_mono hgeometry.plane_le)).trans he.le))
  exact source_critical_pair_false_of_involution_bound V (twoCoreIn H)
    (conjugateSpan H V) ZS g hs hVU hfirst hsecond
    (source_chosen_involution_bound T H V
      ((T : Subgroup G) ⊓ centralizer (ZS : Set G)) ZS hH.1.1.2 hVH inf_le_left
      hgeometry.plane_le hgeometry.normalized hTS hcomm)
    hcenters hmove

end CFSG.Quasithin.Chapter15.Section02
