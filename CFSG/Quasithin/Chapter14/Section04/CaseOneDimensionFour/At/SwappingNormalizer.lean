module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.SwappingNormalizer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At.SwappingGeometry

/-!
# The remaining relative normalizer in the swapping branch at the original G,T

Put A=⟨s,[U,s]⟩=Jₑ(T∩L), K=O²(H) and Q=O₂(H), with the literal
subgroups and selected involution from the original flag. The image of N_K(A)
modulo Q has order dividing nine. Since it fixes the original flag point of A,
its faithful action has order dividing 1344, which excludes image order nine.
The checked compatible split-pair contradiction excludes image order three.
Consequently N_K(A)≤Q. The already established T-normalization and H=KT now
give the exact equality N_H(A)=T.

This extension specializes the existing source argument to the actual
`HigherRankHypothesis` and to `Structural1222At` and `Theorem12213At`.
The universal interfaces remain unchanged. Earlier Chapter 12 inputs keep
their original producers; final recognition still requires I.4.5.
Source: Aschbacher–Smith, 14.4.3–5, printed pp.1006–1008.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour.SplitImage
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (setup : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgL : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hswap : (q.left.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom =
      q.right.map F.U.subtype)
include d setup structural alternatives hne hZ hcard g hgL hgP hgH q hsX hs hout hswap

/-- The residual normalizer has trivial image modulo the actual two-core.
The possible image orders divide nine; fixation of the marked point excludes
nine, and the compatible split-pair contradiction excludes three. -/
theorem source_swapping_residual_normalizer_le_core :
    (pResidual 2 F.H).map F.H.subtype ⊓
      normalizer ((zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆ : Subgroup G) : Set G) ≤
        F.H.pCoreIn 2 := by
  let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
  let K := (pResidual 2 F.H).map F.H.subtype
  let R := K ⊓ normalizer (A : Set G)
  let Q := F.H.pCoreIn 2
  have hRH : R ≤ F.H := inf_le_left.trans (map_subtype_le _)
  let π := QuotientGroup.mk' (pCore 2 F.H)
  have hQi : Q.subgroupOf F.H = pCore 2 F.H :=
    comap_map_eq_self_of_injective F.H.subtype_injective _
  have hi : Q.relIndex R = Nat.card ((R.subgroupOf F.H).map π) := by
    rw [← relIndex_subgroupOf hRH, hQi]
    simpa only [π, QuotientGroup.ker_mk'] using (relIndex_ker (R.subgroupOf F.H) π)
  have hRK : R.subgroupOf F.H ≤ pResidual 2 F.H := by
    rintro x ⟨⟨y,hy,he⟩,_⟩
    exact (Subtype.ext he : y = x) ▸ hy
  have hd9 : Q.relIndex R ∣ 9 := by
    rw [hi, ← (source_residual_nine d setup structural alternatives F hne hZ hcard).2]
    exact card_dvd_of_le (map_mono hRK)
  obtain ⟨P,z,hpoint,⟨parabolic⟩⟩ := source_parabolic_generators_of_swapping
    d setup structural alternatives F hne hZ hcard g hgP hgH q s hsX hs hout hswap
  have hz : z ≠ 1 := by
    intro he
    have hp := F.card 1 (by decide)
    rw [hpoint, he] at hp
    norm_num at hp
  have hfix : R ≤ centralizer ({(z : G)} : Set G) := by
    rw [← F.H_eq_centralizer (by decide) (z : G) hpoint]
    exact hRH
  obtain ⟨_,hAe,hAc⟩ := q.elementary_sixteen_of_swap F.U s
    (congrArg Subtype.val hs) hout hswap
  let : IsElementaryAbelian 2 A := hAe
  have hd1344 := NormalizerAction.sylowImage_card_dvd_of_fixed_point_sixteen A R hAc z hz hfix
  have hCQ : R ⊓ centralizer (A : Set G) ≤ Q :=
    (inf_le_inf_right _ inf_le_left).trans
      (source_swapping_residual_centralizer d setup structural alternatives F hne hZ hcard
        q s (congrArg Subtype.val hs) hout hswap)
  have hd : Q.relIndex R ∣ Nat.card (QuaternionResidual.image A R) := by
    rw [QuaternionResidual.card_image_eq_relIndex A R inf_le_right,
      ← inf_relIndex_right (centralizer (A : Set G)) R]
    exact relIndex_dvd_of_le_left R (by simpa only [inf_comm] using hCQ)
  have hc := Nat.mem_divisors.mpr ⟨hd9, (by decide : (9 : ℕ) ≠ 0)⟩
  rw [show (9 : ℕ).divisors = {1,3,9} by decide] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  apply relIndex_eq_one.mp
  rcases hc with hc | hc | hc
  · exact hc
  · exact False.elim ((source_swapping_outer_index_ne_three d setup structural alternatives
      F hne hZ hcard g hgP hgH q s hsX hs hout hswap hgL) hc)
  · have hbad := hd.trans hd1344
    rw [hc] at hbad
    norm_num at hbad

/-- In the remaining swapping branch the full relative normalizer is exactly
the original Sylow subgroup. This uses H=O²(H)T and the literal residual bound. -/
theorem source_swapping_normalizer_eq_sylow :
    F.H ⊓ normalizer
      ((zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆ : Subgroup G) : Set G) =
        (T : Subgroup G) := by
  let A := zpowers (s : G) ⊔ ⁅F.U,zpowers (s : G)⁆
  let K := (pResidual 2 F.H).map F.H.subtype
  have hTN : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (source_swapping_thompson d setup structural alternatives F hne hZ hcard
      g hgP hgH q s hsX hs hout hswap).2
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := (pCore_isPGroup (p := 2) (G := F.H)).le_sylow_of_normal
      (T.subtype (F.invariant 1))
    rintro _ ⟨x,hx,rfl⟩
    exact hh hx
  have hRN : K ⊓ normalizer (A : Set G) ≤ (T : Subgroup G) :=
    (source_swapping_residual_normalizer_le_core d setup structural alternatives
      F hne hZ hcard g hgL hgP hgH q s hsX hs hout hswap).trans hQT
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (F.invariant 1).trans (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F.H (pResidual 2 F.H)))
  apply le_antisymm _ (le_inf (F.invariant 1) hTN)
  rintro x ⟨hxH,hxN⟩
  have hx : x ∈ (K : Set G) * ((T : Subgroup G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left K (T : Subgroup G) hTK]
    exact (source_normalizer_factors d setup structural alternatives F hne hZ hcard).2 ▸ hxH
  obtain ⟨k,hk,t,ht,rfl⟩ := hx
  have hkN : k ∈ normalizer (A : Set G) := by
    have he := (normalizer (A : Set G)).mul_mem hxN
      ((normalizer (A : Set G)).inv_mem (hTN ht))
    simpa only [mul_inv_cancel_right] using he
  exact (T : Subgroup G).mul_mem (hRN ⟨hk,hkN⟩) ht

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry DimensionFour.SplitImage
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.At
