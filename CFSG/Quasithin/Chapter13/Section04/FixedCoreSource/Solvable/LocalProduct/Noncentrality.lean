module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ThompsonNormalizer
public import Stellmacher.BaumannMap

/-!
# The centralizing alternative and the earlier Baumann bound

If J(R) centralizes the actual reduced module V_H, the literal identity
C_R(V_H)=O₂(H) lets B.2.10 identify the Baumann subgroup of R with that
of O₂(H). Thus H normalizes the original ambient Baumann subgroup.
An earlier bound N_G(Baum(R))≤M contradicts the escape H≰M and proves
noncentrality. The second theorem applies this to the actual residual
intersection, using R as the preimage in T of an action-image two-core.

The core-centralizer equality and Baumann bound remain explicit source
inputs. The A₆-block alternative need not satisfy that bound and still
requires its separate source contradiction. This file does not establish
all of 13.4.8. Both that alternative and the local product remain with
qt-d-1341-solvable-source; final earlier-source discharge stays with
qt-d-1341-fixed-core-source.
Source: Aschbacher–Smith 13.4.8, first two paragraphs, printed p.904;
B.2.10 supplies the centralizing alternative, printed p.77.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The earlier Baumann-normalizer bound excludes the centralizing branch of
B.2.10 in the original escaping centralizer. The block branch is separate. -/
theorem centralizer_thompson_noncentral_of_baumann_bound
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hcore : R ⊓ centralizer (centralizerOmegaOrbit T z : Set G) =
      (centralizer ({z} : Set G)).pCoreIn 2)
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G)) :
    ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G) := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let := hU.elementary
  have hRH : R ≤ H := hRT.trans (original_sylow_le_centralizer hz)
  have hQR : H.pCoreIn 2 ≤ R := hcore ▸ inf_le_left
  have hUR : U ≤ R.subgroupOf H :=
    fun _ hx => hQR (centralizerOmegaOrbit_le_core h₀ hz hz1 hx)
  have hQRi : pCore 2 H ≤ R.subgroupOf H := by
    intro x hx
    exact hQR (mem_map_of_mem H.subtype hx)
  have hcorei : pCore 2 H = R.subgroupOf H ⊓ centralizer (U : Set H) := by
    ext x
    have hp : x ∈ pCore 2 H ↔ x.val ∈ H.pCoreIn 2 :=
      (mem_map_iff_mem H.subtype_injective).symm
    rw [hp, ← hcore]
    constructor
    · rintro ⟨hr, hc⟩
      exact ⟨hr, fun u hu => Subtype.ext (hc u.val hu)⟩
    · rintro ⟨hr, hc⟩
      refine ⟨hr, fun u hu => ?_⟩
      exact congrArg Subtype.val (hc ⟨u, centralizerOmegaOrbit_le hz hu⟩ hu)
  intro hJ
  have hmapJ : (elementaryAbelianMaxJ (R.subgroupOf H)).map H.subtype =
      elementaryAbelianMaxJ R := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hRH]
  have hJi : ChapterB.thompsonJ (R.subgroupOf H) 0 ≤ centralizer (U : Set H) := by
    rw [ChapterB.thompsonJ_zero]
    intro x hx u hu
    exact Subtype.ext (hJ (hmapJ ▸ mem_map_of_mem H.subtype hx) u.val hu)
  have hn := (ChapterB.lemma_B_2_10_centralizing U (R.subgroupOf H)
    hUR hQRi hcorei hJi).2.2.2
  have hmapB : (ChapterB.baumann (R.subgroupOf H)).map H.subtype = ChapterB.baumann R := by
    change ((R.subgroupOf H) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (R.subgroupOf H)) : Set H)).map H.subtype = _
    rw [baumann_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hRH]
    rfl
  apply hout
  apply le_trans _ hB
  rw [← hmapB]
  let := hn
  have hh := (map_mono (show (⊤ : Subgroup H) ≤ normalizer
    (ChapterB.baumann (R.subgroupOf H) : Set H) from le_normalizer_of_normal)).trans
      ((ChapterB.baumann (R.subgroupOf H)).le_normalizer_map H.subtype)
  simpa only [← MonoidHom.range_eq_map, range_subtype] using hh

/-- In the earlier Baumann-bound branch, the literal action-core construction
and centralizing alternative discharge both local premises of the residual
intersection theorem. The A₆-block branch is not assumed to satisfy this bound. -/
theorem centralizer_thompson_residual_disjoint_of_baumann_bound
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    {K : Type*} [Group K] (f : T →* K) (R : Subgroup G)
    (hR : R = ((pCore 2 K).comap f).map (T : Subgroup G).subtype)
    (hcore : R ⊓ centralizer (centralizerOmegaOrbit T z : Set G) =
      (centralizer ({z} : Set G)).pCoreIn 2)
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (A : Subgroup G) (hAN : A ≤ normalizer (R : Set G)) :
    let H := centralizer ({z} : Set G)
    let U := (centralizerOmegaOrbit T z).subgroupOf H
    letI := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    let I := ((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q
    Disjoint ((pResidual 2 I).map I.subtype) ((A.subgroupOf H).map q) := by
  have hRT : R ≤ T := by
    rw [hR]
    exact map_subtype_le _
  have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hcore hB hout
  exact centralizer_thompson_residual_disjoint_action_core h₀ hz hz1 f R hR
    (hcore.symm.le.trans inf_le_left) hJ hsolv A hAN

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
