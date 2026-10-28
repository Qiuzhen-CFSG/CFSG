module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.ConjugateSpanCentralizer
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The extraspecial residual exclusion in E.2.17

Let `J` be the canonical normal core of the minimal-parabolic maximal
subgroup `M`. The source hypothesis that `O²(M)` centralizes the chosen
`V` implies that the normal subgroup `O²(J)` centralizes the whole span
`U = ⟨Bᴴ⟩`, for `B ≤ V`. Thus the actual action on `U/Z` kills `O²(J)`.

When the residual of `H/O₂(H)` is extraspecial of odd prime three,
B.6.8 identifies `J`'s image with its center, which is its derived subgroup.
Surjective commutator transport identifies the image of `J` in the actual
action with the derived subgroup of the action's residual. That image is
both a two-group and a three-group, so it is trivial. The action residual
is therefore abelian and cannot be the extraspecial alternative of D.2.17.

The final theorem uses the literal quotient `H/C_H(U/Z)`. Its sole remaining
section-action input is `[U,O₂(H)] ≤ Z`, supplied by the shared E.2.17
structural reduction. No normalization of the original pair core by the
ambient Sylow subgroup, or desired commutator-generation identity, is assumed.

Source: Aschbacher--Smith, E.2.17, printed pp.229--230, solvable case.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.DihedralCubic
open ChapterB
variable {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]

omit [Finite H] in
/-- The original two-residual centralization propagates from `V` to the
conjugate span of its marked subgroup `B`. -/
theorem core_residual_centralizes_span
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤)
    (V B : Subgroup H) (hB : B ≤ V)
    (hc : (pResidual 2 (minimalParabolicMax T hP)).map
      (minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    (pResidual 2 (minimalParabolicCore T hP)).map
      (minimalParabolicCore T hP).subtype ≤
        centralizer (conjugateSpanBy B ⊤ : Set H) := by
  let J := minimalParabolicCore T hP
  have hJM : J ≤ minimalParabolicMax T hP := normalCore_le _
  apply le_centralizer_conjugateSpanBy_of_normalizes
  · exact le_normalizer_of_normal.trans
      (normalizer_le_normalizer_characteristic_image J (pResidual 2 J))
  · exact (embedded_pResidual_mono 2 hJM).trans (hc.trans (centralizer_le hB))

omit [Finite G] in
/-- The original extraspecial residual has abelian image in every actual
span action killing `O₂(H)`. The canonical core and all maps are retained. -/
theorem source_twentyseven_action_residual_commutative
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    [IsExtraspecial 3 (pResidual 2 (H ⧸ pCore 2 H))]
    (V B : Subgroup H) (hB : B ≤ V)
    (hc : (pResidual 2 (minimalParabolicMax T hP)).map
      (minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H))
    (f : H →* G) (hf : Function.Surjective f)
    (hO : pCore 2 H ≤ f.ker)
    (hU : centralizer (conjugateSpanBy B ⊤ : Set H) ≤ f.ker) :
    IsMulCommutative (pResidual 2 G) := by
  let J := minimalParabolicCore T hP
  let X := (pResidual 2 J).map J.subtype
  let π := QuotientGroup.mk' (pCore 2 H)
  let K := pResidual 2 (H ⧸ pCore 2 H)
  let P := pResidual 2 G
  let fbar : (H ⧸ pCore 2 H) →* G := QuotientGroup.lift _ f hO
  have hbar : Function.Surjective fbar := by
    intro y
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨π x,rfl⟩
  have hcomp : fbar.comp π = f := rfl
  have hK : K.map fbar = P := map_pResidual_of_surjective 2 fbar hbar
  have hJ : J.map π = ⁅K,K⁆ := by
    obtain ⟨p,hp,ho,hres,hq,hphi,rest⟩ := minimalParabolic_solvable_structure T hP hs
    rw [← hres] at hphi
    change J.map π = _ at hphi
    rw [hphi,Stellmacher.frattiniAmbient,
      IsExtraspecial.frattini_eq_center (p := 3),
      ← IsExtraspecial.commutator_eq_center (p := 3),map_subtype_commutator]
  have hJf : J.map f = ⁅P,P⁆ := by
    rw [← hcomp,← map_map,hJ,map_commutator,hK]
  have hX : X ≤ f.ker :=
    (core_residual_centralizes_span T hP V B hB hc).trans hU
  let g := f.subgroupMap J
  have hXg : pResidual 2 J ≤ g.ker := by
    intro j hj
    apply Subtype.ext
    exact hX (mem_map_of_mem J.subtype hj)
  have htwo : IsPGroup 2 (J.map f) :=
    ((pResidual_le_iff_isPGroup_quotient 2 g.ker).mp hXg).of_equiv
      (QuotientGroup.quotientKerEquivOfSurjective g (f.subgroupMap_surjective J))
  have hthree : IsPGroup 3 P := hK ▸ (IsExtraspecial.isPGroup 3 K).map fbar
  have hdis := htwo.disjoint_of_coprime hthree (by decide : Nat.Coprime 2 3)
  have hJbot : J.map f = ⊥ := by
    apply bot_unique
    intro x hx
    exact hdis.le_bot ⟨hx, (commutator_le_left P P) (hJf ▸ hx)⟩
  have hcomm : ⁅P,P⁆ = ⊥ := hJf.symm.trans hJbot
  apply (commutator_eq_bot_iff P).mp
  apply bot_unique
  have hh : (_root_.commutator P).map P.subtype = ⊥ := by
    rw [map_subtype_commutator,hcomm]
  have hk := (map_eq_bot_iff (_root_.commutator P)).mp hh
  simpa only [(MonoidHom.ker_eq_bot_iff P.subtype).mpr P.subtype_injective] using hk

/-- Exclude the extraspecial action alternative using the original marked
source centralization, without a module-model or dimension hypothesis. -/
theorem source_twentyseven_action_exclusion
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    [IsExtraspecial 3 (pResidual 2 (H ⧸ pCore 2 H))]
    (V B : Subgroup H) (hB : B ≤ V)
    (hc : (pResidual 2 (minimalParabolicMax T hP)).map
      (minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H))
    (f : H →* G) (hf : Function.Surjective f)
    (hO : pCore 2 H ≤ f.ker)
    (hU : centralizer (conjugateSpanBy B ⊤ : Set H) ≤ f.ker) :
    ¬ IsExtraspecial 3 (pResidual 2 G) := by
  intro he
  let := he
  have hm := source_twentyseven_action_residual_commutative T hP hs V B hB hc f hf hO hU
  have hz : center (pResidual 2 G) = ⊥ :=
    (IsExtraspecial.commutator_eq_center (p := 3)).symm.trans
      ((commutator_eq_bot_iff _).mpr hm)
  have hh := IsExtraspecial.center_order_p 3 (pResidual 2 G)
  rw [hz,card_bot] at hh
  omega

/-- The literal `H/C_H(U/Z)` consumer. The shared structural commutator bound
supplies the two-core action kernel, and ordinary centralizers act trivially
automatically. This discharges the extraspecial `K⁺` alternative of E.2.17. -/
theorem source_twentyseven_section_exclusion
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    [IsExtraspecial 3 (pResidual 2 (H ⧸ pCore 2 H))]
    (V B U Z : Subgroup H) [U.Normal] [Z.Normal] (hB : B ≤ V)
    (hU : U = conjugateSpanBy B ⊤)
    (hc : (pResidual 2 (minimalParabolicMax T hP)).map
      (minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H))
    (hO : ⁅U,pCore 2 H⁆ ≤ Z) :
    let := centralizerModulo_top_normal U Z
    ¬ IsExtraspecial 3 (pResidual 2 (H ⧸ centralizerModulo ⊤ U Z)) := by
  let := centralizerModulo_top_normal U Z
  let C := centralizerModulo ⊤ U Z
  let f := QuotientGroup.mk' C
  apply source_twentyseven_action_exclusion T hP hs V B hB hc f
    (QuotientGroup.mk'_surjective C)
  · rw [QuotientGroup.ker_mk']
    intro x hx
    exact mem_centralizerModulo_iff.mpr ⟨mem_top x, fun u hu =>
      hO (commutator_mem_commutator hu hx)⟩
  · rw [QuotientGroup.ker_mk',← hU]
    intro x hx
    refine mem_centralizerModulo_iff.mpr ⟨mem_top x,?_⟩
    intro u hu
    rw [commutatorElement_eq_one_iff_mul_comm.mpr ((mem_centralizer_iff.mp hx) u hu)]
    exact Z.one_mem
end CFSG.Quasithin.ChapterE.DihedralCubic
