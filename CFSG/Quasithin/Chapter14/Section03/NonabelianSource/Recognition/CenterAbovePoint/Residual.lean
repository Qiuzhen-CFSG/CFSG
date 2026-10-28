module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NumericalGeometry
public import CFSG.Quasithin.ChapterG.Section10.TwoCore
public import Theory.GroupTheory.PResidual.ConjugateSpan
public import Theory.GroupTheory.PResidual.NontrivialImage

/-!
# The actual center-conjugate residual in original 14.3.15

Put K=O²(⟨Z(U)ᵍᴴ⟩). Earlier center geometry proves that K centralizes
Z(U). Triviality of the dotted two-core makes its dotted image nontrivial.
The central automorphism kernel theorem shows that its dotted and starred
kernels coincide. Finally, normality and the binary spanning seed show
that K cannot lie in the original M. The last theorem constructs this
entire configuration directly from the original selected rank-two prefix.

Source: Aschbacher--Smith 12.8.13(3), 14.3.15, printed pp.855,995.
-/

public section
open Subgroup Theory.GroupTheory Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
variable {T : Sylow 2 G} {V : Subgroup G} {L M : Subgroup G}

@[expose] noncomputable def centerConjugateSpan (F : InvariantFlag T V 2) (g : G) : Subgroup G :=
  conjugateSpanBy (conjugate F.ZU g) F.H

@[expose] noncomputable def centerConjugateResidual (F : InvariantFlag T V 2) (g : G) : Subgroup G :=
  (pResidual 2 (centerConjugateSpan F g)).map (centerConjugateSpan F g).subtype

omit [Finite G] in
theorem centerConjugateSpan_le_H (F : InvariantFlag T V 2) (g : G)
    (hg : conjugate F.ZU g ≤ F.H) : centerConjugateSpan F g ≤ F.H :=
  conjugateSpanBy_le_self hg

omit [Finite G] in
theorem centerConjugateResidual_le_H (F : InvariantFlag T V 2) (g : G)
    (hg : conjugate F.ZU g ≤ F.H) : centerConjugateResidual F g ≤ F.H :=
  (map_subtype_le _).trans (centerConjugateSpan_le_H F g hg)

omit [Finite G] in
theorem centerConjugateResidual_normalized (F : InvariantFlag T V 2) (g : G) :
    F.H ≤ normalizer (centerConjugateResidual F g : Set G) :=
  le_sup_left.trans (embedded_residual_conjugateSpanBy_normalized _ _)

omit [Finite G] in
theorem centerConjugateResidual_centralizes (F : InvariantFlag T V 2) (g : G)
    (hc : ⁅F.ZU,conjugate F.ZU g⁆ = ⊥) :
    centerConjugateResidual F g ≤ centralizer (F.ZU : Set G) := by
  apply (map_subtype_le _).trans
  apply le_centralizer_iff.mp
  exact le_centralizer_conjugateSpanBy_of_normalizes F.ZU (conjugate F.ZU g) F.H
    F.H_normalizes_ZU (commutator_eq_bot_iff_le_centralizer.mp hc)

theorem rankTwo_centers_commute (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ⁅F.ZU,conjugate F.ZU g⁆ = ⊥ := by
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨_,_,_,_,hIG,hIN,_⟩ := F.binary_generation (by decide) L h.L_normalizes_seed
    (h.binarySeedAction_surjective F) h.centralizer hcomm hsquare hspan hne g hgP hgH
  let B := F.localKernel_markedForm (by decide) d.two d.frattini_point hcomm
  have hc := F.binary_source_center_calculations (by decide) L h.L_normalizes_seed
    ((pResidual_eq_top_iff 2 L).mp h.L_residual) h.sylow_normalizes_L
    (h.binarySeedAction_surjective F) (fun hn => by omega) h.centralizer d.seed_center
    hcomm hsquare hspan hne g hgP hgH d.tilde_kernel B
  have hdis := (F.parabolic_displaced_centers (by decide) L h.L_normalizes_seed
    d.seed_center g hgP hgH).1
  exact (F.rankTwo_centers L g (F.P_le_seed_normalizer L h.L_normalizes_seed hgP)
    (h.sylowOmega_eq_point F) (F.binary_U_le_sylow (by decide) hsquare)
    ((F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN))
    d.seed_center hdis hc.2.1).2.2

theorem centerConjugateResidual_dot_ne_bot (F : InvariantFlag T V 2) (g : G)
    (hg : conjugate F.ZU g ≤ F.H)
    (hc : pCore 2 F.TerminalHdot = ⊥)
    (hne : F.terminalDot (conjugate F.ZU g) ≠ ⊥) :
    F.terminalDot (centerConjugateResidual F g) ≠ ⊥ := by
  let J := centerConjugateSpan F g
  have hJH : J ≤ F.H := centerConjugateSpan_le_H F g hg
  let JH := J.subgroupOf F.H
  let : JH.Normal := (normal_subgroupOf_iff_le_normalizer hJH).mpr
    (le_normalizer_conjugateSpanBy _ _)
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hJne : JH.map q ≠ ⊥ := by
    intro hb
    apply hne
    apply le_bot_iff.mp
    exact (map_mono (comap_mono (le_conjugateSpanBy _ _))).trans hb.le
  have hr := embedded_pResidual_image_ne_bot_of_pCore_eq_bot 2 JH q
    (QuotientGroup.mk'_surjective _) hc hJne
  have he : ((pResidual 2 JH).map JH.subtype).map F.H.subtype =
      centerConjugateResidual F g := by
    rw [map_embedded_pResidual, map_subgroupOf_eq_of_le hJH]
    rfl
  have he' : (centerConjugateResidual F g).subgroupOf F.H =
      (pResidual 2 JH).map JH.subtype := by
    rw [← he, subgroupOf, comap_map_eq_self_of_injective F.H.subtype_injective]
  change ((centerConjugateResidual F g).subgroupOf F.H).map q ≠ ⊥
  rwa [he']

theorem rankTwo_center_residual_geometry (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hZ : F.ZU ≠ F.Vi 1) :
    centerConjugateResidual F g ≤ F.H ∧
    F.H ≤ normalizer (centerConjugateResidual F g : Set G) ∧
    centerConjugateResidual F g ≤ centralizer (F.ZU : Set G) ∧
    F.terminalDot (centerConjugateResidual F g) ≠ ⊥ := by
  have hg := F.conjugate_center_le_H g (F.P_le_seed_normalizer L h.L_normalizes_seed hgP)
  refine ⟨centerConjugateResidual_le_H F g hg,centerConjugateResidual_normalized F g,
    centerConjugateResidual_centralizes F g (rankTwo_centers_commute h F d hne g hgP hgH),?_⟩
  apply centerConjugateResidual_dot_ne_bot F g hg hyp.twoCore_eq_bot
  exact F.terminalDot_center_ne_bot g hg
    (rankTwo_terminal_center_kernel h F d hne g hgP hgH)
    (lt_of_le_of_ne (F.point_le_ZU (by decide)) (Ne.symm hZ))


open scoped commutatorElement
/-- Fixing both the center and the central quotient leaves only the two-core. -/
theorem terminal_kernel_centralizer_le_core (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] (d : ClosureGeometry F) :
    (centralizer (F.ZU : Set G)).subgroupOf F.H ⊓ F.terminalHatAction.ker ≤ pCore 2 F.H := by
  have huk : F.uAction.ker ≤ pCore 2 F.H := by
    rw [← d.tilde_kernel]
    intro h hh
    apply (F.mem_localTildeAction_ker_iff F.H le_rfl h).mpr
    intro u hu
    have he := congrArg (fun a : MulAut F.U => (a ⟨u,hu⟩ : G)) hh
    change (h : G) * u * (h : G)⁻¹ = u at he
    have hz : ⁅(h : G),u⁆ = 1 := by
      rw [commutatorElement_def,he,mul_inv_cancel]
    exact hz ▸ (F.Vi 1).one_mem
  let a := (automorphismPair (center F.U)).comp F.uAction
  have hp : IsPGroup 2 a.ker :=
    (isPGroup_automorphism_pair_kernel (center F.U) (d.two.to_subgroup _)).comap_of_ker_isPGroup
      F.uAction (pCore_isPGroup.to_le huk)
  have ha : a.ker ≤ pCore 2 F.H := le_sSup ⟨inferInstance,hp⟩
  apply le_trans _ ha
  intro h hh
  change automorphismPair (center F.U) (F.uAction h) = 1
  rw [automorphismPair_apply]
  apply Prod.ext
  · apply MulEquiv.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    change (h : G) * (z : G) * (h : G)⁻¹ = (z : G)
    have hz := hh.1 (z : G) (mem_map_of_mem F.U.subtype z.property)
    exact mul_inv_eq_iff_eq_mul.mpr hz.symm
  · exact hh.2

/-- On a center-centralizing subgroup, the dotted and starred quotient maps
have exactly the same kernel, on the original subgroup of H. -/
theorem terminal_restricted_kernel_eq_core (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] (d : ClosureGeometry F)
    (A : Subgroup G) (hc : A ≤ centralizer (F.ZU : Set G)) :
    A.subgroupOf F.H ⊓ F.terminalHatAction.ker = A.subgroupOf F.H ⊓ pCore 2 F.H := by
  apply le_antisymm
  · exact le_inf inf_le_left
      ((inf_le_inf (comap_mono hc) le_rfl).trans (terminal_kernel_centralizer_le_core F d))
  · exact inf_le_inf le_rfl (F.pCore_le_uhatAction_ker_of_tilde_kernel (by decide) d.tilde_kernel)

/-- The actual residual in 14.3.15 has identical dotted and starred kernels. -/
theorem rankTwo_center_residual_kernel (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (centerConjugateResidual F g).subgroupOf F.H ⊓ F.terminalHatAction.ker =
      (centerConjugateResidual F g).subgroupOf F.H ⊓ pCore 2 F.H :=
  terminal_restricted_kernel_eq_core F d _
    (centerConjugateResidual_centralizes F g (rankTwo_centers_commute h F d hne g hgP hgH))

/-- A normal subgroup preserving the original seed acts trivially on U/Z(U).
The seed image is a binary line and its full orbit spans the central quotient. -/
theorem terminalDot_eq_bot_of_normalizes_seed (F : InvariantFlag T V 2)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (A : Subgroup G) (hAH : A ≤ F.H)
    (hHA : F.H ≤ normalizer (A : Set G)) (hAV : A ≤ normalizer (V : Set G)) :
    F.terminalDot A = ⊥ := by
  let : (A.subgroupOf F.H).Normal := (normal_subgroupOf_iff_le_normalizer hAH).mpr hHA
  let C := F.terminalDot A
  let : C.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hline : finrank (ZMod 2) (hatSpace F V) = 1 := by
    have hh := finrank_hatSpace_plane F (by decide) d.seed_center
    exact (congrArg (fun A : Subgroup G => finrank (ZMod 2) (hatSpace F A)) F.last).symm.trans hh
  let S := hatSpace F V
  let : Nontrivial S := Module.nontrivial_of_finrank_pos (by rw [hline]; decide)
  obtain ⟨v,hv⟩ := exists_ne (0 : S)
  have hv0 : (v : Additive F.Uhat) ≠ 0 := fun he => hv (Subtype.ext he)
  have hspan : S = Submodule.span (ZMod 2) {(v : Additive F.Uhat)} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hline v.property hv0
  have hfix (c : C) : F.terminalRepresentation c (v : Additive F.Uhat) = v := by
    obtain ⟨a,ha,hac⟩ := c.property
    have hastable : F.terminalRepresentation c (v : Additive F.Uhat) ∈ S := by
      change (F.terminalRepresentation c (v : Additive F.Uhat)).toMul ∈ hatImage F V
      obtain ⟨u,hu,he⟩ := v.property
      rw [←hac,F.terminalRepresentation_apply_mk,←he,F.terminalHatAction_apply_mk]
      refine ⟨_,?_,rfl⟩
      exact (mem_normalizer_iff.mp (hAV ha) (u : G)).mp hu
    have hanonzero : F.terminalRepresentation c (v : Additive F.Uhat) ≠ 0 := by
      intro he
      apply hv0
      have hh := congrArg (F.terminalRepresentation (c : F.TerminalHdot)⁻¹) he
      simpa only [← Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
        Module.End.one_apply,map_zero] using hh
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp (hspan.le hastable)
    have hb0 : b ≠ 0 := by intro hh; exact hanonzero (by simpa [hh] using hb.symm)
    have hb1 : b = 1 := (by decide : ∀ b : ZMod 2, b ≠ 0 → b = 1) b hb0
    simpa [hb1] using hb.symm
  have horbit := terminal_orbit_span F (v : Additive F.Uhat)
    (hspan.symm.trans (congrArg (fun A : Subgroup G => hatSpace F A) F.last).symm)
  let D := Representation.fixedSubrepresentationOfNormal F.terminalRepresentation C
  have hvD : (v : Additive F.Uhat) ∈ D := hfix
  have htop : D.toSubmodule = ⊤ := by
    apply top_unique
    rw [←horbit]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact D.apply_mem_toSubmodule a hvD
  have hker : C ≤ F.terminalRepresentation.ker := by
    intro c hc
    apply LinearMap.ext
    intro w
    have hw : w ∈ D := by change w ∈ D.toSubmodule; rw [htop]; trivial
    exact hw ⟨c,hc⟩
  exact bot_unique (hker.trans_eq
    ((MonoidHom.ker_eq_bot_iff _).mpr F.terminalRepresentation_injective))

/-- The residual surviving the dotted action cannot lie in the original M. -/
theorem rankTwo_center_residual_not_le_M (h : RankTwoHypothesis K T L M)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hne : ¬ IsMulCommutative F.U)
    (g : G) [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hZ : F.ZU ≠ F.Vi 1) : ¬ centerConjugateResidual F g ≤ M := by
  obtain ⟨hKH,hHK,_,hK⟩ := rankTwo_center_residual_geometry h F d hne g hgP hgH hyp hZ
  intro hKM
  exact hK (terminalDot_eq_bot_of_normalizes_seed F d _ hKH hHK
    (hKM.trans RankTwoHypothesis.M_normalizes_seed))


/-- The concrete normal residual used in the center-above-point branch. -/
structure CenterAbovePointResidual (F : InvariantFlag T V 2) (g : G) (M : Subgroup G) : Prop where
  le_H : centerConjugateResidual F g ≤ F.H
  normalized : F.H ≤ normalizer (centerConjugateResidual F g : Set G)
  centralizes : centerConjugateResidual F g ≤ centralizer (F.ZU : Set G)
  dot_ne_bot : F.terminalDot (centerConjugateResidual F g) ≠ ⊥
  kernel_eq : (centerConjugateResidual F g).subgroupOf F.H ⊓ F.terminalHatAction.ker =
    (centerConjugateResidual F g).subgroupOf F.H ⊓ pCore 2 F.H
  not_le_M : ¬ centerConjugateResidual F g ≤ M

open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
/-- The source constructs K, both actual quotient maps, and every earlier
geometry input directly from the original selected rank-two prefix. -/
theorem source_center_above_point_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ∃ hs : IsElementaryAbelian 2 (rankTwoSeed T M), letI := hs
    ∃ F : InvariantFlag T (rankTwoSeed T M) 2,
      F.Vi 1 = centralInvolutions T ∧ F.H = Mc ∧
      F.U = conjugateSpanBy (localModule T M) Mc ∧
    ∃ _d : ClosureGeometry F, ∃ he : IsElementaryAbelian 2 F.Uhat, letI := he
    ∃ g : G, g ∈ F.P (sourceResidual M Mc) ∧ g ∉ F.H ∧
    ∃ hx : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := hx
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat), ∃ v : Additive F.Uhat,
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple F.TerminalHdot) ∧
      (F.ZU ≠ F.Vi 1 → CenterAbovePointResidual F g M) := by
  obtain ⟨hs,F,hpoint,hH,hU,d,he,g,hgP,hgH,hx,B,v,hyp,hcover⟩ :=
    source_terminal_hypothesis hG T hempty hM hu hmany hcard e hne
  let := hs
  let := he
  let := hx
  have hn : ¬ IsMulCommutative F.U := hU ▸ hne
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  refine ⟨hs,F,hpoint,hH,hU,d,he,g,hgP,hgH,hx,B,v,hyp,hcover,?_⟩
  intro hZ
  obtain ⟨hKH,hHK,hKC,hK⟩ := rankTwo_center_residual_geometry h F d hn g hgP hgH hyp hZ
  exact ⟨hKH,hHK,hKC,hK,rankTwo_center_residual_kernel h F d hn g hgP hgH,
    rankTwo_center_residual_not_le_M h F d hn g hgP hgH hyp hZ⟩


end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
