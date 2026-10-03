module

public import Stellmacher.DirectProductCommutator
public import Stellmacher.BaumannNormalizer
public import Stellmacher.CentralizerQuotientAction
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.GlobalBaumannThreeCore
public import Stellmacher.MaxElementaryOffender
public import Stellmacher.SectionOne.LemmaOneSeven
public import Stellmacher.SectionOne.OneSevenIdentification
public import Stellmacher.SectionOne.SelectedProductIrreducibleSupport
public import Stellmacher.SectionThree.ResidualImageIrreducible
public import Stellmacher.SectionThree.ThreeNineAmbientPromotion
public import Stellmacher.SectionThree.SylowOddNormalSupplement
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The selected-factor dichotomy in Stellmacher (3.9)

This module proves the final representation-theoretic dichotomy used in
Stellmacher's Lemma (3.9).  For the faithful quotient action
`H / C_H(V)` on the normal elementary abelian subgroup `V`, assume that
the two local residuals survive the quotient, neither local Baumann subgroup
lies in its two-core, and the image of `S` has trivial intersection with
the quotient two-core.  Then either the two residuals have the same
commutator on `Ω₁(Z(S))`, or each of the two residuals centralizes the
commutator produced by the other.

The proof first promotes each barred residual into the ambient three-core and
uses the global Baumann theorem to identify its commutator with the image of
the Thompson subgroup.  The local (1.7) package embeds both residuals in the
derived subgroup of a selected internal product of `SL₂(2)` factors.
Stellmacher (3.3) makes their nontrivial elementary abelian images irreducible.
The selected-product support theorem then gives equality or disjoint support.
Finally, the common centralizer-quotient action API transports equality or
fixed-point containment back through `V ≤ H ≤ G`, yielding the two
commutator alternatives stated below.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), Lemma (3.9), p. 24; see
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionThree

universe u

open BenderSuzuki.External

private theorem le_normalizer_twoCoreAmbient_selected
    {G : Type u} [Group G] (P : Subgroup G) :
    P ≤ Subgroup.normalizer (twoCoreAmbient P : Set G) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 P))).mp
  rw [subgroupOf_map_subtype_eq]
  infer_instance

private theorem isSylowSubgroupIn_map_range_selected
    {G X : Type*} [Group G] [Group X] [Finite G]
    (f : G →* X) (T : Sylow 2 G) :
    IsSylowSubgroupIn ((T : Subgroup G).map f) f.range := by
  let fr : G →* f.range := f.rangeRestrict
  let U : Sylow 2 f.range := T.mapSurjective f.rangeRestrict_surjective
  refine ⟨U, ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map]
  congr 1

private theorem normal_subgroupOf_range_of_normal_selected
    {G X : Type*} [Group G] [Group X]
    (f : G →* X) (N : Subgroup G) (hN : N.Normal) :
    ((N.map f).subgroupOf f.range).Normal := by
  let fr : G →* f.range := f.rangeRestrict
  have hmap : N.map fr = (N.map f).subgroupOf f.range := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, hnx⟩
      refine ⟨n, hn, ?_⟩
      exact Subtype.ext hnx
  rw [← hmap]
  exact hN.map fr f.rangeRestrict_surjective

private theorem isElementaryAbelian_of_le_selected
    {G : Type*} [Group G] {p : ℕ} (A E : Subgroup G)
    (hE : IsElementaryAbelian p E) (hAE : A ≤ E) :
    IsElementaryAbelian p A := by
  refine
    { toIsMulCommutative := ⟨⟨?_⟩⟩
      exponent_dvd_p := ?_ }
  · intro x y
    let xE : E := ⟨x, hAE x.property⟩
    let yE : E := ⟨y, hAE y.property⟩
    apply Subtype.ext
    simpa [xE, yE] using congrArg (fun z : E => (z : G))
      (hE.toIsMulCommutative.is_comm.comm xE yE)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    let xE : E := ⟨x, hAE x.property⟩
    have hx := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      hE.exponent_dvd_p xE
    apply Subtype.ext
    simpa [xE] using congrArg (fun z : E => (z : G)) hx

private theorem thompson_not_le_actionKernel_selected
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P H : Subgroup G)
    (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hPH : P ≤ H) (hsolvP : Group.IsSolvable P)
    (T : Sylow 2 H) (hST : S ≤ sylowAmbient T)
    (hJ : elementaryAbelianMaxJ S =
      elementaryAbelianMaxJ (sylowAmbient T))
    (V C : Subgroup H) (hVnormal : V.Normal)
    (hVelem : IsElementaryAbelian 2 V)
    (hCdef : C = Subgroup.centralizer (V : Set H))
    (hCnormal : C.Normal)
    (hRnotC : ¬ twoResidualAmbient P ≤ C.map H.subtype)
    (hBnot : ¬ S ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) ≤
        twoCoreAmbient P) :
    ¬ elementaryAbelianMaxJ S ≤ C.map H.subtype := by
  classical
  let _ : V.Normal := hVnormal
  let _ : IsElementaryAbelian 2 V := hVelem
  let _ : C.Normal := hCnormal
  let _ : Group.IsSolvable P := hsolvP
  let J₀ : Subgroup G := elementaryAbelianMaxJ S
  let JH : Subgroup H := elementaryAbelianMaxJ (T : Subgroup H)
  let B : Subgroup G := S ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient J₀ : Set G)
  have hSH : S ≤ H := hST.trans (Subgroup.map_subtype_le (T : Subgroup H))
  have hR₀H : twoResidualAmbient P ≤ H :=
    (Subgroup.map_subtype_le _).trans hPH
  have hJHmap : JH.map H.subtype = J₀ := by
    calc
      JH.map H.subtype = elementaryAbelianMaxJ (sylowAmbient T) :=
        (elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective
          (T : Subgroup H)).symm
      _ = J₀ := hJ.symm
  have hVT : V ≤ (T : Subgroup H) :=
    (IsElementaryAbelian.isPGroup 2 V).le_sylow_of_normal T
  intro hJ₀C
  have hJHC : JH ≤ C := by
    intro j hj
    have hjJ₀ : (j : G) ∈ J₀ := by
      rw [← hJHmap]
      exact Subgroup.mem_map_of_mem H.subtype hj
    rcases hJ₀C hjJ₀ with ⟨c, hc, hcj⟩
    have hcj' : c = j := H.subtype_injective hcj
    simpa [hcj'] using hc
  have hJHcentV : JH ≤ Subgroup.centralizer (V : Set H) := by
    simpa [← hCdef] using hJHC
  have hVcentJH : V ≤ Subgroup.centralizer (JH : Set H) :=
    Subgroup.le_centralizer_iff.mp hJHcentV
  have hVomegaJH : V ≤ omegaOneCenterAmbient JH :=
    elementary_centralizer_maxJ_le_omegaCenter (T : Subgroup H) V
      hVT hVcentJH
  have hVomegaJ₀ : V.map H.subtype ≤ omegaOneCenterAmbient J₀ := by
    calc
      V.map H.subtype ≤ (omegaOneCenterAmbient JH).map H.subtype :=
        Subgroup.map_mono hVomegaJH
      _ = omegaOneCenterAmbient (JH.map H.subtype) :=
        (omegaOneCenterAmbient_map_injective H.subtype
          H.subtype_injective JH).symm
      _ = omegaOneCenterAmbient J₀ := by rw [hJHmap]
  have hBC : B ≤ C.map H.subtype := by
    intro b hb
    let bH : H := ⟨b, hSH hb.1⟩
    refine ⟨bH, ?_, rfl⟩
    rw [hCdef]
    change ∀ v : H, v ∈ V → v * bH = bH * v
    intro v hv
    apply H.subtype_injective
    exact Subgroup.mem_centralizer_iff.mp hb.2 (v : G)
      (hVomegaJ₀ (Subgroup.mem_map_of_mem H.subtype hv))
  have hBnormal : (B.subgroupOf S).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact S.le_normalizer.trans (normalizer_le_normalizer_baumann S)
  have hcomm : ⁅twoResidualAmbient P, B⁆ = twoResidualAmbient P :=
    (lemma_three_four S h P hP B ⟨inf_le_left, hBnormal⟩ hsolvP).resolve_left
      (by simpa [B, J₀] using hBnot)
  have hCambNormalH : ((C.map H.subtype).subgroupOf H).Normal := by
    simpa [subgroupOf_map_subtype_eq] using hCnormal
  have hHnormC : H ≤ Subgroup.normalizer (C.map H.subtype : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le C)).mp hCambNormalH
  apply hRnotC
  rw [← hcomm]
  exact (Subgroup.commutator_mono le_rfl hBC).trans
    ((Subgroup.le_normalizer_iff_commutator_le_right).mp
      (hR₀H.trans hHnormC))

/-- The selected-factor alternative concluding Stellmacher's Lemma (3.9). -/
public theorem threeNine_selected_factor_dichotomy
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (P₁ P₂ H : Subgroup G)
    (hP₁ : P₁ ∈ PSet (⊤ : Subgroup G) S)
    (hP₂ : P₂ ∈ PSet (⊤ : Subgroup G) S)
    (hH : H = P₁ ⊔ P₂)
    (hsolv₁ : Group.IsSolvable P₁) (hsolv₂ : Group.IsSolvable P₂)
    (T : Sylow 2 H) (hST : S ≤ sylowAmbient T)
    (hsolv : Group.IsSolvable H)
    (hJ : elementaryAbelianMaxJ S =
      elementaryAbelianMaxJ (sylowAmbient T))
    (V C : Subgroup H)
    (hVdef : V = Subgroup.normalClosure
      ((omegaOneCenterAmbient S).subgroupOf H : Set H))
    (hVnormal : V.Normal) (hVelem : IsElementaryAbelian 2 V)
    (hCdef : C = Subgroup.centralizer (V : Set H)) (hCnormal : C.Normal)
    (hR₁C : ¬ twoResidualAmbient P₁ ≤ C.map H.subtype)
    (hR₂C : ¬ twoResidualAmbient P₂ ≤ C.map H.subtype)
    (hB₁ : ¬ S ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) ≤
        twoCoreAmbient P₁)
    (hB₂ : ¬ S ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) ≤
        twoCoreAmbient P₂)
    (hbarCore :
      letI : C.Normal := hCnormal
      let q : H →* H ⧸ C := QuotientGroup.mk' C
      (S.subgroupOf H).map q ⊓ pCore 2 (H ⧸ C) = ⊥) :
    ((⁅⁅omegaOneCenterAmbient S, twoResidualAmbient P₁⁆,
          twoResidualAmbient P₂⁆ = ⊥ ∧
      ⁅⁅omegaOneCenterAmbient S, twoResidualAmbient P₂⁆,
          twoResidualAmbient P₁⁆ = ⊥) ∨
      ⁅omegaOneCenterAmbient S, twoResidualAmbient P₁⁆ =
        ⁅omegaOneCenterAmbient S, twoResidualAmbient P₂⁆) := by
  classical
  let _ : C.Normal := hCnormal
  let _ : V.Normal := hVnormal
  let _ : IsElementaryAbelian 2 V := hVelem
  let _ : Group.IsSolvable H := hsolv
  let _ : Group.IsSolvable P₁ := hsolv₁
  let _ : Group.IsSolvable P₂ := hsolv₂
  let q : H →* H ⧸ C := QuotientGroup.mk' C
  let X : Type u := H ⧸ C
  let R₁₀ : Subgroup G := twoResidualAmbient P₁
  let R₂₀ : Subgroup G := twoResidualAmbient P₂
  let J₀ : Subgroup G := elementaryAbelianMaxJ S
  let SH : Subgroup H := S.subgroupOf H
  let Sbar : Subgroup X := SH.map q
  let R₁ : Subgroup X := (R₁₀.subgroupOf H).map q
  let R₂ : Subgroup X := (R₂₀.subgroupOf H).map q
  let JH : Subgroup H := J₀.subgroupOf H
  let Jbar : Subgroup X := JH.map q
  let P₁H : Subgroup H := P₁.subgroupOf H
  let P₂H : Subgroup H := P₂.subgroupOf H
  let P₁bar : Subgroup X := P₁H.map q
  let P₂bar : Subgroup X := P₂H.map q
  have hSP₁ : S ≤ P₁ := by
    obtain ⟨U, hU⟩ := hP₁.1.2.1
    rw [← hU]
    exact Subgroup.map_subtype_le _
  have hSP₂ : S ≤ P₂ := by
    obtain ⟨U, hU⟩ := hP₂.1.2.1
    rw [← hU]
    exact Subgroup.map_subtype_le _
  have hP₁H : P₁ ≤ H := by rw [hH]; exact le_sup_left
  have hP₂H : P₂ ≤ H := by rw [hH]; exact le_sup_right
  have hSH : S ≤ H := hSP₁.trans hP₁H
  have hR₁₀H : R₁₀ ≤ H := (Subgroup.map_subtype_le _).trans hP₁H
  have hR₂₀H : R₂₀ ≤ H := (Subgroup.map_subtype_le _).trans hP₂H
  have hJ₀S : J₀ ≤ S := sSup_le fun A hA => hA.1
  have hJ₀H : J₀ ≤ H := hJ₀S.trans hSH
  have hJHdef : JH = J₀.subgroupOf H := rfl
  have hJbarSbar : Jbar ≤ Sbar := by
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hJ₀S)
  have hJ₀p : IsPGroup 2 J₀ :=
    h.2.2.to_le hJ₀S
  have hJbarp : IsPGroup 2 Jbar := by
    exact (hJ₀p.of_equiv
      (Subgroup.subgroupOfEquivOfLe hJ₀H).symm).map q
  have hR₁ne : R₁ ≠ ⊥ := by
    intro hbot
    apply hR₁C
    intro r hr
    let rH : H := ⟨r, hR₁₀H hr⟩
    have hrker : rH ∈ q.ker := by
      apply (Subgroup.map_eq_bot_iff (f := q) (R₁₀.subgroupOf H)).mp
        (by simpa [R₁] using hbot)
      exact hr
    rw [QuotientGroup.ker_mk'] at hrker
    exact ⟨rH, hrker, rfl⟩
  have hR₂ne : R₂ ≠ ⊥ := by
    intro hbot
    apply hR₂C
    intro r hr
    let rH : H := ⟨r, hR₂₀H hr⟩
    have hrker : rH ∈ q.ker := by
      apply (Subgroup.map_eq_bot_iff (f := q) (R₂₀.subgroupOf H)).mp
        (by simpa [R₂] using hbot)
      exact hr
    rw [QuotientGroup.ker_mk'] at hrker
    exact ⟨rH, hrker, rfl⟩
  have hJ₀notC : ¬ J₀ ≤ C.map H.subtype :=
    thompson_not_le_actionKernel_selected S h P₁ H hP₁ hP₁H hsolv₁ T hST
      hJ V C hVnormal hVelem hCdef hCnormal hR₁C hB₁
  have hcore₁S : twoCoreAmbient P₁ ≤ S := by
    obtain ⟨U, hU⟩ := hP₁.1.2.1
    calc
      twoCoreAmbient P₁ = (pCore 2 P₁).map P₁.subtype := rfl
      _ ≤ (U : Subgroup P₁).map P₁.subtype :=
        Subgroup.map_mono
          ((pCore_isPGroup (p := 2) (G := P₁)).le_sylow_of_normal U)
      _ = S := hU
  have hcore₂S : twoCoreAmbient P₂ ≤ S := by
    obtain ⟨U, hU⟩ := hP₂.1.2.1
    calc
      twoCoreAmbient P₂ = (pCore 2 P₂).map P₂.subtype := rfl
      _ ≤ (U : Subgroup P₂).map P₂.subtype :=
        Subgroup.map_mono
          ((pCore_isPGroup (p := 2) (G := P₂)).le_sylow_of_normal U)
      _ = S := hU
  have hsomeNoncore :
      ¬ J₀ ≤ twoCoreAmbient P₁ ∨
        ¬ J₀ ≤ twoCoreAmbient P₂ := by
    by_contra hnone
    push Not at hnone
    have hP₁normJ : P₁ ≤ Subgroup.normalizer (J₀ : Set G) := by
      intro g hg
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      apply elementaryAbelianMaxJ_map_eq_of_le S (MulAut.conj g)
      exact (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hnone.1).trans
        (by
          have hnorm := Subgroup.mem_normalizer_iff_map_conj_eq.mp
            (le_normalizer_twoCoreAmbient_selected P₁ hg)
          change (twoCoreAmbient P₁).map (MulAut.conj g).toMonoidHom =
            twoCoreAmbient P₁ at hnorm
          rw [hnorm]
          exact hcore₁S)
    have hP₂normJ : P₂ ≤ Subgroup.normalizer (J₀ : Set G) := by
      intro g hg
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      apply elementaryAbelianMaxJ_map_eq_of_le S (MulAut.conj g)
      exact (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hnone.2).trans
        (by
          have hnorm := Subgroup.mem_normalizer_iff_map_conj_eq.mp
            (le_normalizer_twoCoreAmbient_selected P₂ hg)
          change (twoCoreAmbient P₂).map (MulAut.conj g).toMonoidHom =
            twoCoreAmbient P₂ at hnorm
          rw [hnorm]
          exact hcore₂S)
    have hHnormJ : H ≤ Subgroup.normalizer (J₀ : Set G) := by
      rw [hH]
      exact sup_le hP₁normJ hP₂normJ
    have hJHnormal : JH.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₀H).mpr hHnormJ
    have hJbarNormal : Jbar.Normal := hJHnormal.map q
      (QuotientGroup.mk'_surjective C)
    have hJbarCore : Jbar ≤ pCore 2 X := le_sSup ⟨hJbarNormal, hJbarp⟩
    have hJbarBot : Jbar = ⊥ := by
      have hcap : Sbar ⊓ pCore 2 X = ⊥ := by
        simpa [Sbar, SH, q, X] using hbarCore
      apply le_bot_iff.mp
      rw [← hcap]
      exact le_inf hJbarSbar hJbarCore
    apply hJ₀notC
    intro j hj
    let jH : H := ⟨j, hJ₀H hj⟩
    refine ⟨jH, ?_, rfl⟩
    rw [← QuotientGroup.ker_mk' C]
    exact (Subgroup.map_eq_bot_iff (f := q) JH).mp
      (by simpa [Jbar] using hJbarBot)
      (Subgroup.mem_subgroupOf.mpr hj)
  have hR₁core (hJ₁ : ¬ J₀ ≤ twoCoreAmbient P₁) :
      R₁ ≤ pCore 3 X := by
    change ((twoResidualAmbient P₁).subgroupOf H).map q ≤
      pCore 3 (H ⧸ C)
    exact threeNine_residual_image_le_threeCore S h P₁ H hP₁ hP₁H
      hsolv₁ T hST hsolv hJ V C hVnormal hVelem hCdef hCnormal hR₁C
      hJ₁ hbarCore
  have hR₂core (hJ₂ : ¬ J₀ ≤ twoCoreAmbient P₂) :
      R₂ ≤ pCore 3 X := by
    change ((twoResidualAmbient P₂).subgroupOf H).map q ≤
      pCore 3 (H ⧸ C)
    exact threeNine_residual_image_le_threeCore S h P₂ H hP₂ hP₂H
      hsolv₂ T hST hsolv hJ V C hVnormal hVelem hCdef hCnormal hR₂C
      hJ₂ hbarCore
  have hP₁decomp : R₁ ⊔ Sbar = P₁bar := by
    change (R₁₀.subgroupOf H).map q ⊔ SH.map q = P₁H.map q
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hR₁₀H hSH,
      twoResidual_sup_sylowImage hP₁.1.2.1]
  have hP₂decomp : R₂ ⊔ Sbar = P₂bar := by
    change (R₂₀.subgroupOf H).map q ⊔ SH.map q = P₂H.map q
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hR₂₀H hSH,
      twoResidual_sup_sylowImage hP₂.1.2.1]
  have hPjoin : P₁bar ⊔ P₂bar = ⊤ := by
    have hsubjoin : P₁H ⊔ P₂H = ⊤ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hP₁H,
        Subgroup.map_subgroupOf_eq_of_le hP₂H, ← hH]
      simpa only [← MonoidHom.range_eq_map] using
        (Subgroup.range_subtype (H := H)).symm
    rw [← Subgroup.map_sup, hsubjoin]
    exact Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective C)
  let fP₁ : P₁ →* X := q.comp (Subgroup.inclusion hP₁H)
  have hfP₁range : fP₁.range = P₁bar := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨⟨p, hP₁H p.property⟩, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  obtain ⟨UP₁, hUP₁⟩ := hP₁.1.2.1
  have hU₁mapH : (UP₁ : Subgroup P₁).map
      (Subgroup.inclusion hP₁H) = SH := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (y : G) ∈ S
      rw [← hUP₁]
      exact ⟨y, hy, rfl⟩
    · intro hx
      change (x : G) ∈ S at hx
      rw [← hUP₁] at hx
      obtain ⟨y, hy, heq⟩ := hx
      exact ⟨y, hy, Subtype.ext heq⟩
  have hU₁map : (UP₁ : Subgroup P₁).map fP₁ = Sbar := by
    rw [show fP₁ = q.comp (Subgroup.inclusion hP₁H) from rfl,
      ← Subgroup.map_map, hU₁mapH]
  have hSylow₁bar : IsSylowSubgroupIn Sbar P₁bar := by
    have hs := isSylowSubgroupIn_map_range_selected fP₁ UP₁
    simpa [hfP₁range, hU₁map] using hs
  let fP₂ : P₂ →* X := q.comp (Subgroup.inclusion hP₂H)
  have hfP₂range : fP₂.range = P₂bar := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨⟨p, hP₂H p.property⟩, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  obtain ⟨UP₂, hUP₂⟩ := hP₂.1.2.1
  have hU₂mapH : (UP₂ : Subgroup P₂).map
      (Subgroup.inclusion hP₂H) = SH := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (y : G) ∈ S
      rw [← hUP₂]
      exact ⟨y, hy, rfl⟩
    · intro hx
      change (x : G) ∈ S at hx
      rw [← hUP₂] at hx
      obtain ⟨y, hy, heq⟩ := hx
      exact ⟨y, hy, Subtype.ext heq⟩
  have hU₂map : (UP₂ : Subgroup P₂).map fP₂ = Sbar := by
    rw [show fP₂ = q.comp (Subgroup.inclusion hP₂H) from rfl,
      ← Subgroup.map_map, hU₂mapH]
  have hSylow₂bar : IsSylowSubgroupIn Sbar P₂bar := by
    have hs := isSylowSubgroupIn_map_range_selected fP₂ UP₂
    simpa [hfP₂range, hU₂map] using hs
  have hO₃odd : ¬ 2 ∣ Nat.card (pCore 3 X) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).mp
      (pCore_isPGroup (p := 3) (G := X))
    rw [hn]
    exact Nat.prime_two.coprime_iff_not_dvd.mp
      ((show Nat.Coprime 2 3 by decide).pow_right n)
  have hglobalSylow₁ (hJ₁ : ¬ J₀ ≤ twoCoreAmbient P₁) :
      IsSylowSubgroupIn Sbar (⊤ : Subgroup X) := by
    have hgen : pCore 3 X ⊔ P₂bar = ⊤ := by
      apply top_unique
      rw [← hPjoin]
      apply sup_le
      · rw [← hP₁decomp]
        exact sup_le ((hR₁core hJ₁).trans le_sup_left)
          ((show Sbar ≤ P₂bar by rw [← hP₂decomp]; exact le_sup_right).trans
            le_sup_right)
      · exact le_sup_right
    have hs := isSylowSubgroupIn_normal_odd_sup
      (pCore 3 X) P₂bar Sbar (pCore_normal (p := 3)) hO₃odd hSylow₂bar
    rwa [hgen] at hs
  have hglobalSylow₂ (hJ₂ : ¬ J₀ ≤ twoCoreAmbient P₂) :
      IsSylowSubgroupIn Sbar (⊤ : Subgroup X) := by
    have hgen : pCore 3 X ⊔ P₁bar = ⊤ := by
      apply top_unique
      rw [← hPjoin]
      apply sup_le
      · exact le_sup_right
      · rw [← hP₂decomp]
        exact sup_le ((hR₂core hJ₂).trans le_sup_left)
          ((show Sbar ≤ P₁bar by rw [← hP₁decomp]; exact le_sup_right).trans
            le_sup_right)
    have hs := isSylowSubgroupIn_normal_odd_sup
      (pCore 3 X) P₁bar Sbar (pCore_normal (p := 3)) hO₃odd hSylow₁bar
    rwa [hgen] at hs
  have hglobalSylow : IsSylowSubgroupIn Sbar (⊤ : Subgroup X) :=
    hsomeNoncore.elim hglobalSylow₁ hglobalSylow₂
  obtain ⟨SX₀, hSX₀⟩ := hglobalSylow
  let SX : Sylow 2 X := SX₀.mapSurjective
    (f := (⊤ : Subgroup X).subtype) (by
    intro x
    exact ⟨⟨x, trivial⟩, rfl⟩)
  have hSX : (SX : Subgroup X) = Sbar := by
    change (SX₀ : Subgroup (⊤ : Subgroup X)).map
      (⊤ : Subgroup X).subtype = Sbar
    exact hSX₀
  have hcoreX : pCore 2 X = ⊥ := by
    apply le_bot_iff.mp
    have hOS : pCore 2 X ≤ Sbar := by
      rw [← hSX]
      exact (pCore_isPGroup (p := 2) (G := X)).le_sylow_of_normal SX
    have hcap : Sbar ⊓ pCore 2 X = ⊥ := by
      simpa [Sbar, SH, q, X] using hbarCore
    rw [← hcap]
    exact le_inf hOS le_rfl
  let JT : Subgroup H := elementaryAbelianMaxJ (T : Subgroup H)
  let B₀ : Subgroup G := S ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient J₀ : Set G)
  let BH : Subgroup H := B₀.subgroupOf H
  have hJTmap : JT.map H.subtype = J₀ := by
    calc
      JT.map H.subtype = elementaryAbelianMaxJ (sylowAmbient T) :=
        (elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective
          (T : Subgroup H)).symm
      _ = J₀ := hJ.symm
  have hJHeq : JH = JT := by
    apply Subgroup.map_injective H.subtype_injective
    rw [hJHdef, Subgroup.map_subgroupOf_eq_of_le hJ₀H, hJTmap]
  have hSHleT : SH ≤ (T : Subgroup H) := by
    intro s hs
    have hsT : (s : G) ∈ sylowAmbient T := hST hs
    obtain ⟨t, ht, heq⟩ := hsT
    have hts : t = s := H.subtype_injective heq
    rw [← hts]
    exact show t ∈ (T : Subgroup H) from ht
  have hVT : V ≤ (T : Subgroup H) :=
    (IsElementaryAbelian.isPGroup 2 V).le_sylow_of_normal T
  have hJTBH : JT ≤ BH := by
    intro j hj
    apply Subgroup.mem_subgroupOf.mpr
    have hjJ₀ : (j : G) ∈ J₀ := by
      rw [← hJTmap]
      exact Subgroup.mem_map_of_mem H.subtype hj
    refine ⟨hJ₀S hjJ₀, ?_⟩
    change (j : G) ∈ Subgroup.centralizer
      (omegaOneCenterAmbient J₀ : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 (j : G) hjJ₀ |>.symm
  have hBHT : BH ≤ (T : Subgroup H) := by
    exact (Subgroup.subgroupOf_mono H inf_le_left).trans hSHleT
  have hOmegaJTmap : (omegaOneCenterAmbient JT).map H.subtype =
      omegaOneCenterAmbient J₀ := by
    calc
      (omegaOneCenterAmbient JT).map H.subtype =
          omegaOneCenterAmbient (JT.map H.subtype) :=
        (omegaOneCenterAmbient_map_injective H.subtype
          H.subtype_injective JT).symm
      _ = omegaOneCenterAmbient J₀ := by rw [hJTmap]
  have hBHcent : BH ≤ Subgroup.centralizer
      (omegaOneCenterAmbient JT : Set H) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply H.subtype_injective
    have hb₀ : (b : G) ∈ B₀ := hb
    exact Subgroup.mem_centralizer_iff.mp hb₀.2 (z : G)
      (by rw [← hOmegaJTmap]; exact Subgroup.mem_map_of_mem H.subtype hz)
  have hker : q.ker = Subgroup.centralizer (V : Set H) := by
    rw [QuotientGroup.ker_mk', hCdef]
  have hJTne : JT.map q ≠ ⊥ := by
    intro hbot
    apply hJ₀notC
    intro j hj
    let jH : H := ⟨j, hJ₀H hj⟩
    refine ⟨jH, ?_, rfl⟩
    rw [← QuotientGroup.ker_mk' C]
    apply (Subgroup.map_eq_bot_iff (f := q) JH).mp
      (by rw [hJHeq, hbot])
    exact Subgroup.mem_subgroupOf.mpr hj
  have hJTBHmap : JT.map q = BH.map q :=
    globalBaumann_image_eq_maxJImage T V hVnormal hVelem hVT hsolv q
      (QuotientGroup.mk'_surjective C) hker hcoreX BH hJTBH hBHT
      hBHcent hJTne
  have hJbarJT : Jbar = JT.map q := by
    change JH.map q = JT.map q
    exact congrArg (Subgroup.map q) hJHeq
  have hJbarBH : Jbar = BH.map q := hJbarJT.trans hJTBHmap
  have hB₀H : B₀ ≤ H := inf_le_left.trans hSH
  have hB₀normalS : (B₀.subgroupOf S).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact S.le_normalizer.trans (normalizer_le_normalizer_baumann S)
  have hcomm₁₀ : ⁅R₁₀, B₀⁆ = R₁₀ :=
    (lemma_three_four S h P₁ hP₁ B₀ ⟨inf_le_left, hB₀normalS⟩ hsolv₁).resolve_left
      (by simpa [B₀, J₀] using hB₁)
  have hcomm₂₀ : ⁅R₂₀, B₀⁆ = R₂₀ :=
    (lemma_three_four S h P₂ hP₂ B₀ ⟨inf_le_left, hB₀normalS⟩ hsolv₂).resolve_left
      (by simpa [B₀, J₀] using hB₂)
  have hcomm₁H : ⁅R₁₀.subgroupOf H, BH⁆ = R₁₀.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hR₁₀H,
      show BH.map H.subtype = B₀ from
        Subgroup.map_subgroupOf_eq_of_le hB₀H]
    exact hcomm₁₀
  have hcomm₂H : ⁅R₂₀.subgroupOf H, BH⁆ = R₂₀.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hR₂₀H,
      show BH.map H.subtype = B₀ from
        Subgroup.map_subgroupOf_eq_of_le hB₀H]
    exact hcomm₂₀
  have hcomm₁B : ⁅R₁, BH.map q⁆ = R₁ := by
    have hm := congrArg (Subgroup.map q) hcomm₁H
    simpa [R₁, Subgroup.map_commutator] using hm
  have hcomm₂B : ⁅R₂, BH.map q⁆ = R₂ := by
    have hm := congrArg (Subgroup.map q) hcomm₂H
    simpa [R₂, Subgroup.map_commutator] using hm
  have hglobal₁ := globalBaumann_threeCore T V hVnormal hVelem hVT hsolv q
    (QuotientGroup.mk'_surjective C) hker hcoreX BH hJTBH hBHT hBHcent
    hJTne R₁ hcomm₁B.symm
  have hglobal₂ := globalBaumann_threeCore T V hVnormal hVelem hVT hsolv q
    (QuotientGroup.mk'_surjective C) hker hcoreX BH hJTBH hBHT hBHcent
    hJTne R₂ hcomm₂B.symm
  let _ := centralizerQuotientAction V hVnormal q
    (QuotientGroup.mk'_surjective C) hker
  let TX : Sylow 2 X := T.mapSurjective (QuotientGroup.mk'_surjective C)
  have hSbarTX : Sbar ≤ (TX : Subgroup X) := by
    rw [show (TX : Subgroup X) = (T : Subgroup H).map q by
      exact Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective C) T]
    exact Subgroup.map_mono hSHleT
  have hTX : (TX : Subgroup X) = Sbar := by
    calc
      (TX : Subgroup X) = (SX : Subgroup X) :=
        SX.is_maximal' TX.isPGroup' (hSX ▸ hSbarTX)
      _ = Sbar := hSX
  have hJbarne : Jbar ≠ ⊥ := by
    rw [hJbarJT]
    exact hJTne
  have hevenX : Even (Nat.card X) := by
    have hTXne : (TX : Subgroup X) ≠ ⊥ := by
      intro hbot
      apply hJbarne
      exact bot_unique (hbot ▸ hJbarSbar.trans_eq hTX.symm)
    have htwo : 2 ∣ Nat.card TX := by
      rcases TX.isPGroup'.card_eq_or_dvd with hone | htwo
      · exact False.elim (hTXne ((Subgroup.eq_bot_iff_card _).mpr hone))
      · exact htwo
    exact even_iff_two_dvd.mpr
      (htwo.trans (TX : Subgroup X).card_subgroup_dvd_card)
  have hsec : SectionOne.Hypotheses X V :=
    ⟨Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective C),
      hevenX,
      centralizerQuotientAction_faithful V hVnormal q
        (QuotientGroup.mk'_surjective C) hker,
      hcoreX⟩
  let I := {A : Subgroup H //
    A ∈ elementaryAbelianMaxSubgroups (T : Subgroup H)}
  let Aq : I → Subgroup X := fun A => A.val.map q
  have hAq (A : I) : SectionOne.oneA (V := V) (TX : Subgroup X) (Aq A) := by
    have hA := centralizerQuotientAction_maxElementary_map_mem_oneA
      (T : Subgroup H) V A.val hVnormal hVT A.property q
      (QuotientGroup.mk'_surjective C) hker
    rw [show (TX : Subgroup X) = (T : Subgroup H).map q by
      exact Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective C) T]
    exact hA
  have hJgen : Jbar = ⨆ A : I, Aq A := by
    rw [hJbarJT]
    apply le_antisymm
    · apply Subgroup.map_le_iff_le_comap.mpr
      apply sSup_le
      intro A hA
      exact Subgroup.map_le_iff_le_comap.mp
        (le_iSup Aq (⟨A, hA⟩ : I))
    · exact iSup_le fun A => Subgroup.map_mono (le_sSup A.property)
  let E : Subgroup X := ⁅SectionOne.oddCore X, Jbar⁆ ⊔ Jbar
  obtain ⟨hJinf, hEN, hEnorm, n, D, hprod, hinj, hD, _hDN, hmodule⟩ :=
    SectionOne.offender_generated_selected_product hsec TX Aq hAq Jbar hJgen
  change IsInternalDirectProductFamily E D at hprod
  let N := SectionOne.oneSevenGenerated (G := X) (V := V)
  let _ : N.Normal := (SectionOne.oneSeven_global_product hsec TX).1
  have hJN : Jbar ≤ N := (show Jbar ≤ E from le_sup_right).trans hEN
  have hweak : ∀ b : X,
      Jbar.map (MulAut.conj b).toMonoidHom ≤ (TX : Subgroup X) →
        Jbar.map (MulAut.conj b).toMonoidHom = Jbar := by
    intro b hb
    rw [hJbarJT] at hb ⊢
    simpa [JT, TX, Sylow.coe_mapSurjective] using weakly_closed_map_of_surjective
      T (elementaryAbelianMaxJ (T : Subgroup H))
      (sSup_le fun A hA => hA.1)
      (fun g hg => elementaryAbelianMaxJ_map_eq_of_le
        (T : Subgroup H) (MulAut.conj g) hg)
      q (QuotientGroup.mk'_surjective C) b hb
  have hNE : N ≤ Subgroup.normalizer (E : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEN).mp hEnorm
  have hJE : Subgroup.normalizer (Jbar : Set X) ≤
      Subgroup.normalizer (E : Set X) := by
    let W := SectionOne.oddCore X
    let _ : W.Normal := pPrimeCore_normal
    intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hW : W.map (MulAut.conj b).toMonoidHom = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (show b ∈ Subgroup.normalizer (W : Set X) by
          rw [Subgroup.normalizer_eq_top]
          trivial)
    have hJb : Jbar.map (MulAut.conj b).toMonoidHom = Jbar :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hb
    change (⁅W, Jbar⁆ ⊔ Jbar).map (MulAut.conj b).toMonoidHom =
      ⁅W, Jbar⁆ ⊔ Jbar
    rw [Subgroup.map_sup, Subgroup.map_commutator, hW, hJb]
  have hEnormal : E.Normal :=
    normal_of_normalized_by_normal_and_weakly_closed_normalizer
      TX N Jbar E (hJbarSbar.trans_eq hTX.symm) hJN hweak hNE hJE
  let _ : E.Normal := hEnormal
  have hcomm₁J : ⁅R₁, Jbar⁆ = R₁ := by
    rw [hJbarBH]
    exact hcomm₁B
  have hcomm₂J : ⁅R₂, Jbar⁆ = R₂ := by
    rw [hJbarBH]
    exact hcomm₂B
  have hthreeCoreOdd : pCore 3 X ≤ SectionOne.oddCore X := by
    apply le_sSup
    refine ⟨pCore_normal, ?_⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 3)).mp
      (pCore_isPGroup (p := 3) (G := X))
    rw [hm]
    exact (show Nat.Coprime 2 3 by decide).pow_right m
  have hR₁odd : R₁ ≤ SectionOne.oddCore X :=
    hglobal₁.1.trans hthreeCoreOdd
  have hR₂odd : R₂ ≤ SectionOne.oddCore X :=
    hglobal₂.1.trans hthreeCoreOdd
  have hR₁E : R₁ ≤ E := by
    rw [← hcomm₁J]
    exact (Subgroup.commutator_mono hR₁odd le_rfl).trans le_sup_left
  have hR₂E : R₂ ≤ E := by
    rw [← hcomm₂J]
    exact (Subgroup.commutator_mono hR₂odd le_rfl).trans le_sup_left
  have hR₁derived : R₁ ≤ (commutator E).map E.subtype := by
    rw [Subgroup.map_subtype_commutator, ← hcomm₁J]
    exact Subgroup.commutator_mono hR₁E le_sup_right
  have hR₂derived : R₂ ≤ (commutator E).map E.subtype := by
    rw [Subgroup.map_subtype_commutator, ← hcomm₂J]
    exact Subgroup.commutator_mono hR₂E le_sup_right
  let RD : Subgroup X := (commutator E).map E.subtype
  have hRDelem : IsElementaryAbelian 3 RD :=
    SectionOne.internalOneSevenProduct_derived_isElementaryAbelian E D hprod hD
  have hR₁elem : IsElementaryAbelian 3 R₁ :=
    isElementaryAbelian_of_le_selected R₁ RD hRDelem hR₁derived
  have hR₂elem : IsElementaryAbelian 3 R₂ :=
    isElementaryAbelian_of_le_selected R₂ RD hRDelem hR₂derived
  have hR₁mapH : (twoResidualSubgroup P₁).map
      (Subgroup.inclusion hP₁H) = R₁₀.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hR₁₀H]
    change (twoResidualSubgroup P₁).map P₁.subtype = R₁₀
    rfl
  have hR₂mapH : (twoResidualSubgroup P₂).map
      (Subgroup.inclusion hP₂H) = R₂₀.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hR₂₀H]
    change (twoResidualSubgroup P₂).map P₂.subtype = R₂₀
    rfl
  have hR₁map : (twoResidualSubgroup P₁).map fP₁ = R₁ := by
    rw [show fP₁ = q.comp (Subgroup.inclusion hP₁H) from rfl,
      ← Subgroup.map_map, hR₁mapH]
  have hR₂map : (twoResidualSubgroup P₂).map fP₂ = R₂ := by
    rw [show fP₂ = q.comp (Subgroup.inclusion hP₂H) from rfl,
      ← Subgroup.map_map, hR₂mapH]
  have hS₁mapH : (S.subgroupOf P₁).map
      (Subgroup.inclusion hP₁H) = SH := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hSH]
    change (S.subgroupOf P₁).map P₁.subtype = S
    exact Subgroup.map_subgroupOf_eq_of_le hSP₁
  have hS₂mapH : (S.subgroupOf P₂).map
      (Subgroup.inclusion hP₂H) = SH := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hSH]
    change (S.subgroupOf P₂).map P₂.subtype = S
    exact Subgroup.map_subgroupOf_eq_of_le hSP₂
  have hS₁map : (S.subgroupOf P₁).map fP₁ = (TX : Subgroup X) := by
    rw [show fP₁ = q.comp (Subgroup.inclusion hP₁H) from rfl,
      ← Subgroup.map_map, hS₁mapH]
    exact hTX.symm
  have hS₂map : (S.subgroupOf P₂).map fP₂ = (TX : Subgroup X) := by
    rw [show fP₂ = q.comp (Subgroup.inclusion hP₂H) from rfl,
      ← Subgroup.map_map, hS₂mapH]
    exact hTX.symm
  have hR₁irred : IsIrreducibleSection (TX : Subgroup X) ⊥ R₁ := by
    have hi := pSet_residual_image_irreducible S h P₁ hP₁ hsolv₁
      fP₁ R₁ hR₁map hR₁ne hR₁elem
    rwa [hS₁map] at hi
  have hR₂irred : IsIrreducibleSection (TX : Subgroup X) ⊥ R₂ := by
    have hi := pSet_residual_image_irreducible S h P₂ hP₂ hsolv₂
      fP₂ R₂ hR₂map hR₂ne hR₂elem
    rwa [hS₂map] at hi
  have hres₁normal : (twoResidualSubgroup P₁).Normal := by
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal
      (fun N => Subgroup.normal_iInf_normal (fun hN => hN.1))
  have hres₂normal : (twoResidualSubgroup P₂).Normal := by
    unfold twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal
      (fun N => Subgroup.normal_iInf_normal (fun hN => hN.1))
  have hR₁normalPbar : (R₁.subgroupOf P₁bar).Normal := by
    rw [← hfP₁range, ← hR₁map]
    exact normal_subgroupOf_range_of_normal_selected
      fP₁ (twoResidualSubgroup P₁) hres₁normal
  have hR₂normalPbar : (R₂.subgroupOf P₂bar).Normal := by
    rw [← hfP₂range, ← hR₂map]
    exact normal_subgroupOf_range_of_normal_selected
      fP₂ (twoResidualSubgroup P₂) hres₂normal
  have hR₁inv : IsConjugateInvariantBy R₁ (TX : Subgroup X) := by
    have hR₁P : R₁ ≤ P₁bar := by rw [← hP₁decomp]; exact le_sup_left
    have hTP : (TX : Subgroup X) ≤ P₁bar := by
      rw [hTX, ← hP₁decomp]
      exact le_sup_right
    have hnorm : P₁bar ≤ Subgroup.normalizer (R₁ : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hR₁P).mp hR₁normalPbar
    intro t r hr
    exact (Subgroup.mem_normalizer_iff.mp (hnorm (hTP t.property)) r).mp hr
  have hR₂inv : IsConjugateInvariantBy R₂ (TX : Subgroup X) := by
    have hR₂P : R₂ ≤ P₂bar := by rw [← hP₂decomp]; exact le_sup_left
    have hTP : (TX : Subgroup X) ≤ P₂bar := by
      rw [hTX, ← hP₂decomp]
      exact le_sup_right
    have hnorm : P₂bar ≤ Subgroup.normalizer (R₂ : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hR₂P).mp hR₂normalPbar
    intro t r hr
    exact (Subgroup.mem_normalizer_iff.mp (hnorm (hTP t.property)) r).mp hr
  have hsupport : R₁ = R₂ ∨
      (commutatorAction R₂ V ≤ FixedPoints.subgroup R₁ V ∧
        commutatorAction R₁ V ≤ FixedPoints.subgroup R₂ V) :=
    SectionOne.selectedProduct_irreducible_eq_or_cross_fixed
      hsec TX E Jbar R₁ R₂ hEnormal hJinf hcomm₁J hcomm₂J
      hR₁inv hR₂inv hR₁irred hR₂irred D hprod hinj hD hmodule
      hR₁derived hR₂derived
  let Z₀ : Subgroup G := omegaOneCenterAmbient S
  let ZH : Subgroup H := Z₀.subgroupOf H
  have hZ₀H : Z₀ ≤ H := by
    intro z hz
    exact hSH ((mem_omegaOneCenterAmbient_iff S z).mp hz |>.1)
  have hZHmap : ZH.map H.subtype = Z₀ :=
    Subgroup.map_subgroupOf_eq_of_le hZ₀H
  have hZHV : ZH ≤ V := by
    rw [hVdef]
    exact Subgroup.le_normalClosure
  let ZV : Subgroup V := ZH.subgroupOf V
  have hZVmap : ZV.map V.subtype = ZH :=
    Subgroup.map_subgroupOf_eq_of_le hZHV
  have hR₁Hmap : (R₁₀.subgroupOf H).map H.subtype = R₁₀ :=
    Subgroup.map_subgroupOf_eq_of_le hR₁₀H
  have hR₂Hmap : (R₂₀.subgroupOf H).map H.subtype = R₂₀ :=
    Subgroup.map_subgroupOf_eq_of_le hR₂₀H
  rcases hsupport with hReq | hcross
  · right
    have hacteq :
        commutatorSubgroup R₁ V ZV = commutatorSubgroup R₂ V ZV := by
      rw [hReq]
    change commutatorSubgroup ((R₁₀.subgroupOf H).map q) V ZV =
      commutatorSubgroup ((R₂₀.subgroupOf H).map q) V ZV at hacteq
    have hm := congrArg (Subgroup.map V.subtype) hacteq
    rw [centralizerQuotientAction_commutatorSubgroup_image_map
        V hVnormal q (QuotientGroup.mk'_surjective C) hker
        (R₁₀.subgroupOf H) ZV,
      centralizerQuotientAction_commutatorSubgroup_image_map
        V hVnormal q (QuotientGroup.mk'_surjective C) hker
        (R₂₀.subgroupOf H) ZV,
      hZVmap] at hm
    have hmG := congrArg (Subgroup.map H.subtype) hm
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      hZHmap, hR₁Hmap, hR₂Hmap] at hmG
    simpa [Z₀, R₁₀, R₂₀] using hmG
  · left
    have htopV : (⊤ : Subgroup V).map V.subtype = V := by
      simpa only [← MonoidHom.range_eq_map] using
        (Subgroup.range_subtype (H := V))
    have hcross₂₁ := Subgroup.map_mono (f := V.subtype) hcross.1
    change (commutatorSubgroup ((R₂₀.subgroupOf H).map q) V ⊤).map
        V.subtype ≤
      (FixedPoints.subgroup ((R₁₀.subgroupOf H).map q) V).map
        V.subtype at hcross₂₁
    rw [centralizerQuotientAction_commutatorSubgroup_image_map
        V hVnormal q (QuotientGroup.mk'_surjective C) hker
        (R₂₀.subgroupOf H) ⊤,
      centralizerQuotientAction_fixedPoints_image_map
        V hVnormal q (QuotientGroup.mk'_surjective C) hker
        (R₁₀.subgroupOf H),
      htopV] at hcross₂₁
    have hcross₁₂ := Subgroup.map_mono (f := V.subtype) hcross.2
    change (commutatorSubgroup ((R₁₀.subgroupOf H).map q) V ⊤).map
        V.subtype ≤
      (FixedPoints.subgroup ((R₂₀.subgroupOf H).map q) V).map
        V.subtype at hcross₁₂
    rw [centralizerQuotientAction_commutatorSubgroup_image_map
        V hVnormal q (QuotientGroup.mk'_surjective C) hker
        (R₁₀.subgroupOf H) ⊤,
      centralizerQuotientAction_fixedPoints_image_map
        V hVnormal q (QuotientGroup.mk'_surjective C) hker
        (R₂₀.subgroupOf H),
      htopV] at hcross₁₂
    have hfirstH : ⁅⁅ZH, R₁₀.subgroupOf H⁆, R₂₀.subgroupOf H⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact (Subgroup.commutator_mono hZHV le_rfl).trans
        hcross₁₂ |>.trans inf_le_right
    have hsecondH : ⁅⁅ZH, R₂₀.subgroupOf H⁆, R₁₀.subgroupOf H⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact (Subgroup.commutator_mono hZHV le_rfl).trans
        hcross₂₁ |>.trans inf_le_right
    have hfirstG := congrArg (Subgroup.map H.subtype) hfirstH
    have hsecondG := congrArg (Subgroup.map H.subtype) hsecondH
    rw [Subgroup.map_commutator, Subgroup.map_commutator,
      hZHmap, hR₁Hmap, hR₂Hmap, Subgroup.map_bot] at hfirstG hsecondG
    constructor
    · simpa [Z₀, R₁₀, R₂₀] using hfirstG
    · simpa [Z₀, R₁₀, R₂₀] using hsecondG

end Stellmacher.SectionThree
