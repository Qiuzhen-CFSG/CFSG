module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ThompsonSylow
public import Theory.GroupTheory.SymmetricThreeSylowNormalizer

/-!
# The odd-residual intersection in the original centralizer quotient

The actual image of J(R) is Sylow in its normal span I*, and that span
is S₃ or S₃×S₃. Its Sylow is self-normalizing. Consequently its odd
two-residual has trivial intersection with any image of an original
actor normalizing R. In the ordinary A₆ branch the actor is the source L₁.

The ambient actor is restricted to the literal H=C_G(z), then mapped by
H→H/C_H(⟨Ω₁(Z(T))^H⟩); the normalizer and residual use those exact maps.
No ambient normality of L₁ or replacement by a model subgroup is used.
The source facts that T and L₁ normalize R, the containment of O₂(H),
and noncentrality still require discharge by qt-d-1341-solvable-source.
The exceptional covering-A₆ case and construction of the local product
also remain with that owner. Final earlier-source assembly stays with
qt-d-1341-fixed-core-source.
Source: Aschbacher–Smith 13.4.8, second paragraph on printed p.905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The source odd-residual intersection vanishes for every original actor
normalizing R, in particular for L₁ in the ordinary A₆ branch. -/
theorem centralizer_thompson_residual_disjoint_normalizing_actor
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (A : Subgroup G) (hAN : A ≤ normalizer (R : Set G)) :
    let H := centralizer ({z} : Set G)
    let U := (centralizerOmegaOrbit T z).subgroupOf H
    letI := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    let I := ((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q
    Disjoint ((pResidual 2 I).map I.subtype) ((A.subgroupOf H).map q) := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let I := ((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q
  let J := ((elementaryAbelianMaxJ R).subgroupOf H).map q
  have hm := centralizer_thompson_span_models h₀ hz hz1 R hRT hQR hJ hsolv
  obtain ⟨P, hP⟩ := centralizer_thompson_span_sylow h₀ hz hz1 R hRT hnR hQR hJ hsolv
  have hd : Disjoint ((pResidual 2 I).map I.subtype) (normalizer (J : Set _)) :=
    SymmetricThreeSylowNormalizer.residual_image_disjoint_normalizer I J hm P hP
  apply hd.mono_right
  have hJH : elementaryAbelianMaxJ R ≤ H :=
    (sSup_le fun _ hB => hB.1).trans (hRT.trans (original_sylow_le_centralizer hz))
  have hAi : A.subgroupOf H ≤ normalizer ((elementaryAbelianMaxJ R).subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hJH]
    exact subgroupOf_mono H (hAN.trans (normalizer_le_normalizer_elementaryAbelianMaxJ R))
  exact (map_mono hAi).trans (((elementaryAbelianMaxJ R).subgroupOf H).le_normalizer_map q)

/-- Use the literal source convention: R is the preimage in the original T
of the two-core of its original local action image. Normalization by T is
then a consequence of the construction, not an additional premise. -/
theorem centralizer_thompson_residual_disjoint_action_core
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    {K : Type*} [Group K] (f : T →* K)
    (R : Subgroup G)
    (hR : R = ((pCore 2 K).comap f).map (T : Subgroup G).subtype)
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
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
  have hnR : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    rw [hR]
    have hh := (map_mono (show (⊤ : Subgroup T) ≤ normalizer ((pCore 2 K).comap f : Set T)
      from le_normalizer_of_normal)).trans
        (((pCore 2 K).comap f).le_normalizer_map (T : Subgroup G).subtype)
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  exact centralizer_thompson_residual_disjoint_normalizing_actor h₀ hz hz1
    R hRT hnR hQR hJ hsolv A hAN

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
