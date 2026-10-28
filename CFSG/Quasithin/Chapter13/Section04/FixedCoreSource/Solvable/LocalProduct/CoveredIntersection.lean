module

public import Theory.GroupTheory.SymmetricThreeCubicNormality
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.Noncentrality
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Marking
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.QuotientActions

/-!
# Excluding the covered central direction from the Thompson residual

The literal L₀ = O²(O₂,Z(L)) has cubic two-core quotient when the original
quotient center has order three. The five-dimensional core marking proves
that L₀ centralizes V. Its Sylow normalization is inherited from L.

If its image met the Thompson odd residual, the cubic-normality theorem
would make that image normal in H/C_H(V_H). In the two-core-kernel case,
normality lifts to L₀, since O₂(H) lies in the original Sylow and normalizes
L₀. Earlier local uniqueness then forces H ≤ N_G(L), contradicting escape.
All quotient maps and the original central residual are retained.

The full L₁ intersection is treated in CoveredResidual using the earlier
13.3.9 input. Noncentrality in the A₆-block case, the larger action kernel,
local product assembly and the marked geometry remain with
qt-d-1341-solvable-source; final earlier-source discharge remains with
qt-d-1341-fixed-core-source.
Source: Aschbacher–Smith 13.4.8, printed p.905; Notation13.2.1, p.877.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Stellmacher Chapter14.Section03.FaithfulSource
open Section08
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual central cubic cover gives the intrinsic quotient of L₀. -/
theorem covered_zero_core_card
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    Nat.card (zero L ⧸ pCore 2 (zero L)) = 3 := by
  have hpre : Source.starImage L (ResidualPlacement.centralPreimage L) = center (L ⧸ pCore 2 L) := by
    unfold Source.starImage ResidualPlacement.centralPreimage
    rw [← comap_subtype,comap_map_eq_self_of_injective L.subtype_injective,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hr : residual (center (L ⧸ pCore 2 L)) = center (L ⧸ pCore 2 L) := by
    apply le_antisymm (residual_le _)
    intro x hx
    have ho := orderOf_dvd_natCard (⟨x,hx⟩ : center (L ⧸ pCore 2 L))
    rw [hc] at ho
    exact ⟨⟨x,hx⟩,mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right ho),rfl⟩
  have hs : Source.starImage L (zero L) = center (L ⧸ pCore 2 L) := by
    rw [zero,star_residual L (ResidualPlacement.centralPreimage L) (map_subtype_le _),hpre,hr]
  have hn : (Source.starImage L (zero L)).Normal := by rw [hs]; infer_instance
  exact (Nat.card_congr (normalStarEquiv L (zero L) (zero_le L) hn).toEquiv).trans
    (by rwa [hs])

omit [Finite G] in
/-- The original five-dimensional marking makes L₀ centralize V. -/
theorem covered_zero_centralizes_core (D : ChosenModule T L V) (m : CoreMarking D) :
    zero L ≤ centralizer (V : Set G) := by
  apply (residual_le _).trans
  rintro _ ⟨l,hl,rfl⟩ v hv
  have hk : QuotientGroup.mk' (centralCore L) l = 1 :=
    (QuotientGroup.eq_one_iff l).mpr hl
  have he := m.equivariant l ⟨v,hv⟩
  rw [hk,map_one] at he
  have hm : V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ ⟨v,hv⟩ = ⟨v,hv⟩ :=
    m.coordinate.injective (Multiplicative.toAdd.injective he)
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hm)).symm

/-- The literal L₀ image is disjoint from the Thompson odd residual. -/
theorem centralizer_thompson_residual_disjoint_covered_zero
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (v : V) (hz : v.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hz1 : v.val ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hQR : (centralizer ({v.val} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T v.val : Set G))
    (hsolv : Group.IsSolvable (centralizer ({v.val} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T v.val).subgroupOf
      (centralizer ({v.val} : Set G)) : Set (centralizer ({v.val} : Set G))) =
      pCore 2 (centralizer ({v.val} : Set G)))
    (hcover : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G)) :
    let H := centralizer ({v.val} : Set G)
    let U := (centralizerOmegaOrbit T v.val).subgroupOf H
    letI := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
    let q := QuotientGroup.mk' (centralizer (U : Set H))
    let I := ((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q
    Disjoint ((pResidual 2 I).map I.subtype) (((zero L).subgroupOf H).map q) := by
  let H := centralizer ({v.val} : Set G)
  let U := (centralizerOmegaOrbit T v.val).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  let N := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let I := (N.subgroupOf H).map q
  let A := (zero L).subgroupOf H
  let B := A.map q
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hAH : zero L ≤ H := (covered_zero_centralizes_core D m).trans
    (centralizer_le (Set.singleton_subset_iff.mpr v.property))
  have hTN : (T : Subgroup G) ≤ normalizer (zero L : Set G) :=
    D.sylow_normalizes_component.trans (normalizer_le_zero_normalizer L)
  let S := T.subtype hTH
  have hSA : (S : Subgroup H) ≤ normalizer (A : Set H) := by
    rw [← subgroupOf_normalizer_eq hAH]
    exact subgroupOf_mono H hTN
  have hA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 (ResidualPlacement.centralPreimage L)).of_surjective
    (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  have hB : IsPPerfect 2 B := hA.of_surjective (q.subgroupMap A) (q.subgroupMap_surjective A)
  have hQ : q.ker = pCore 2 H := (QuotientGroup.ker_mk' _).trans hkernel
  have hQN : q.ker ≤ normalizer (A : Set H) := by
    rw [hQ]
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSA
  have hcard := covered_zero_core_card hcover
  have horder : ∃ n : ℕ, Nat.card B ∣ 3 * 2 ^ n := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := zero L)).exists_card_eq
    have ha : Nat.card (zero L) = 3 * 2 ^ n := by
      rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 (zero L)),hcard,hn]
    refine ⟨n,(card_map_dvd A q).trans ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv,ha]
  have hnB : ¬ B.Normal := by
    intro hb
    let := hb
    have hk : IsPGroup 2 q.ker := hQ ▸ pCore_isPGroup
    have he := comap_normalizer_map_of_pPerfect q A hA hk hQN
    rw [normalizer_eq_top,comap_top] at he
    have hnA : A.Normal := normalizer_eq_top_iff.mp he.symm
    have hnZ : H ≤ normalizer (zero L : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hAH).mp hnA
    have hne : zero L ≠ ⊥ := by
      intro hz
      rw [hz] at hcard
      have hc : Nat.card ((⊥ : Subgroup G) ⧸ pCore 2 (⊥ : Subgroup G)) = 1 := Nat.card_unique
      omega
    apply hout
    exact hnZ.trans (h.normal_subgroup_normalizer_le D.sylow_normalizes_component
      ((zero_le L).trans le_sup_left) hne
      ((sup_le L.le_normalizer D.sylow_normalizes_component).trans (normalizer_le_zero_normalizer L)))
  have hNH : N ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  let : (N.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr
    (le_normalizer_conjugateSpanBy _ _)
  let : I.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  exact SymmetricThreeCubicNormality.residual_disjoint_of_not_normal I B
    (centralizer_thompson_span_models h₀ hz hz1 R hRT hQR hJ hsolv)
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) hB horder
    ((map_mono hSA).trans (A.le_normalizer_map q)) hnB

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
