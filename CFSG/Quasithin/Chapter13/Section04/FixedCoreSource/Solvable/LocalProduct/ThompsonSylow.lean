module
public import CFSG.Quasithin.ChapterB.Section02.RelativeThompsonSylow
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ThompsonFactors

/-!
# The original centralizer Thompson image is Sylow in its span

Apply the relative Thompson theorem in the literal H=C_G(z), with the
original ambient Sylow restricted to H and U=⟨Ω₁(Z(T))^H⟩. The proof
transports J(R), its normal span, and its normalization through subgroup
inclusions, then uses the actual quotient H/C_H(U). The three-rank bound
comes from the original two-local H.

This supplies the source p.905 Sylow claim for the centralizer used in
13.4.9, independently of the invalid general stable-family saturation
claim. The containment O₂(H)≤R, normalization of the source R₁, and its
noncentrality remain explicit local-product inputs owned by
qt-d-1341-solvable-source; final earlier-source discharge remains with
qt-d-1341-fixed-core-source. No quotient is silently replaced by I/O₂(I).
Source: Aschbacher–Smith, 13.4.8–9, printed pp.905–906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual Thompson image is a Sylow subgroup of its actual normal span. -/
theorem centralizer_thompson_span_sylow
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G))) :
    let H := centralizer ({z} : Set G)
    let U := (centralizerOmegaOrbit T z).subgroupOf H
    letI := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    let I := ((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype =
      ((elementaryAbelianMaxJ R).subgroupOf H).map q := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let := hU.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  have hq := QuotientGroup.mk'_surjective (centralizer (U : Set H))
  have hker : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' _
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hRH : R ≤ H := hRT.trans hTH
  have hUR : U ≤ R.subgroupOf H :=
    fun _ hx => hQR (centralizerOmegaOrbit_le_core h₀ hz hz1 hx)
  have hmapJ : (elementaryAbelianMaxJ (R.subgroupOf H)).map H.subtype =
      elementaryAbelianMaxJ R := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hRH]
  have hJi : ¬ elementaryAbelianMaxJ (R.subgroupOf H) ≤ q.ker := by
    rw [hker]
    intro hc
    apply hJ
    rw [← hmapJ]
    rintro x ⟨a, ha, rfl⟩ v hv
    exact congrArg Subtype.val
      ((hc ha) ⟨v, centralizerOmegaOrbit_le hz hv⟩ hv)
  have hspan : conjugateSpanBy (elementaryAbelianMaxJ (R.subgroupOf H)) ⊤ =
      (conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_conjugateSpanBy, hmapJ, ← MonoidHom.range_eq_map, H.range_subtype,
      map_subgroupOf_eq_of_le]
    exact conjugateSpanBy_le_self ((sSup_le fun _ hA => hA.1).trans hRH)
  have hJsub : elementaryAbelianMaxJ (R.subgroupOf H) =
      (elementaryAbelianMaxJ R).subgroupOf H := by
    have hJH : elementaryAbelianMaxJ R ≤ H :=
      (sSup_le fun _ hA => hA.1).trans hRH
    apply map_injective H.subtype_injective
    rw [hmapJ, map_subgroupOf_eq_of_le hJH]
  have hnorm : ((T.subtype hTH : Sylow 2 H) : Subgroup H) ≤
      normalizer (R.subgroupOf H : Set H) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro r
    exact mem_normalizer_iff.mp (hnR ht) r.val
  have hrank : primeRank 3 H ≤ 2 :=
    (isQuasithin_iff_twoLocal.mp h₀.qtke.quasithin) H
      (isTwoLocal_involution_centralizer
        (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1))
      3 (by decide) (by decide)
  have hs := ChapterB.relative_thompson_span_sylow U (R.subgroupOf H) (T.subtype hTH)
    hUR (fun _ hx => hRT hx) hnorm q hq hker hJi hsolv hU.quotient_pCore_eq_bot hrank
  rw [hspan] at hs
  simpa only [hJsub] using hs

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
