module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.SingleFactor
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.Noncentrality
public import CFSG.Quasithin.ChapterB.Section02.RelativeThompsonPlane

/-!
# The S₃ quotient and moved plane in the original centralizer

The relative Thompson calculation applies to the actual centralizer
H=C_G(z), its omega-center orbit, and the original R₁. Transport through
H's subtype preserves the literal ambient commutator. The selected S₃
factor consequently gives |[V_H,I]|=4 and binary rank two, together with
I/O₂(I)≅S₃ for I=⟨J(R₁)^H⟩.

The final endpoint derives the local core-centralizer equality from
C_H(V_H)=O₂(H), then uses the earlier Baumann-normalizer bound to prove
Thompson noncentrality. Thus neither of those local steps is a callback
in that endpoint. The A₆-block branch need not satisfy the Baumann bound;
it, the larger-kernel case, H=L₁IT, and the chamber construction remain
with qt-d-1341-solvable-source. Earlier source order, normalization and
13.4.4 inputs retain final discharge with qt-d-1341-fixed-core-source.

Source: Aschbacher–Smith, 13.4.8(2), printed pp.904–905; the actual
H=C_G(z), V_H=⟨Ω₁(Z(T))^H⟩ application is 13.4.9, printed p.906.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Stellmacher Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The single action factor moves an order-four subgroup of the literal centralizer module. -/
theorem centralizer_thompson_commutator_card_of_single_factor
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hmodel :
      let H := centralizer ({z} : Set G)
      let U := (centralizerOmegaOrbit T z).subgroupOf H
      letI := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
      let q := QuotientGroup.mk' (centralizer (U : Set H))
      Nonempty ((((conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H).map q) ≃*
        Equiv.Perm (Fin 3))) :
    Nat.card (⁅centralizerOmegaOrbit T z,
      conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))⁆ : Subgroup G) = 4 := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let := hU.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set H))
  have hq := QuotientGroup.mk'_surjective (centralizer (U : Set H))
  have hker : q.ker = centralizer (U : Set H) := QuotientGroup.ker_mk' _
  have hRH : R ≤ H := hRT.trans (original_sylow_le_centralizer hz)
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
    rintro x ⟨a,ha,rfl⟩ v hv
    exact congrArg Subtype.val (hc ha ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)
  have hspan : conjugateSpanBy (elementaryAbelianMaxJ (R.subgroupOf H)) ⊤ =
      (conjugateSpanBy (elementaryAbelianMaxJ R) H).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_conjugateSpanBy, hmapJ, ← MonoidHom.range_eq_map, H.range_subtype,
      map_subgroupOf_eq_of_le]
    exact conjugateSpanBy_le_self ((sSup_le fun _ hA => hA.1).trans hRH)
  have hm : Nonempty (((conjugateSpanBy (elementaryAbelianMaxJ (R.subgroupOf H)) ⊤).map q) ≃*
      Equiv.Perm (Fin 3)) := by
    rw [hspan]
    exact hmodel
  have hc := ChapterB.relative_thompson_span_commutator_card U (R.subgroupOf H) hUR
    q hq hker hJi hsolv hU.quotient_pCore_eq_bot hm
  let N := conjugateSpanBy (elementaryAbelianMaxJ (R.subgroupOf H)) ⊤
  have hmap : (⁅U,N⁆ : Subgroup H).map H.subtype =
      ⁅centralizerOmegaOrbit T z,conjugateSpanBy (elementaryAbelianMaxJ R) H⁆ := by
    rw [map_commutator, map_subgroupOf_eq_of_le (centralizerOmegaOrbit_le hz)]
    dsimp only [N]
    rw [map_conjugateSpanBy, hmapJ, ← MonoidHom.range_eq_map, H.range_subtype]
  rw [← hmap, card_map_of_injective H.subtype_injective]
  exact hc

/-- Both clauses of 13.4.8(2) in the two-core-kernel branch, with literal L₁ and I. -/
theorem centralizer_thompson_single_factor_data_of_firstResidual
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z).subgroupOf
      (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) =
      pCore 2 (centralizer ({z} : Set G)))
    (horder : ∃ m n : ℕ, Nat.card (firstCentralizerResidual L z) ∣ 2 ^ m * 3 ^ n)
    (hthree : 3 ∣ Nat.card (firstCentralizerResidual L z))
    (hAN : firstCentralizerResidual L z ≤ normalizer (R : Set G)) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
    Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z,I⁆ : Subgroup G) = 2 := by
  have hAmove := firstCentralizerResidual_noncentral_of_twoCore_kernel hkernel hthree
  have hm := centralizer_thompson_single_factor_of_twoCore_kernel h₀ hz hz1 R hRT hnR hQR hJ
    hsolv hkernel (firstCentralizerResidual L z) ((firstCentralizerResidual_le L z).trans inf_le_right)
    (firstCentralizerResidual_twoPerfect L z) horder hAN hAmove
  have hc := centralizer_thompson_commutator_card_of_single_factor h₀ hz hz1 R hRT hQR hJ hsolv hm
  refine ⟨centralizer_thompson_core_quotient_of_firstResidual h₀ hz hz1 R hRT hnR hQR hJ
    hsolv hkernel horder hthree hAN, ?_⟩
  change Nat.log 2 _ = 2
  rw [hc]
  decide

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Stellmacher Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The earlier Baumann bound supplies Thompson movement before the single-factor application. -/
theorem centralizer_single_factor_data_of_baumann_bound
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (R : Subgroup G) (hRT : R ≤ T)
    (hnR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hQR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ R)
    (hsolv : Group.IsSolvable (centralizer ({z} : Set G)))
    (hkernel : centralizer ((centralizerOmegaOrbit T z).subgroupOf
      (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))) =
      pCore 2 (centralizer ({z} : Set G)))
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hout : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (horder : ∃ m n : ℕ, Nat.card (firstCentralizerResidual L z) ∣ 2 ^ m * 3 ^ n)
    (hthree : 3 ∣ Nat.card (firstCentralizerResidual L z))
    (hAN : firstCentralizerResidual L z ≤ normalizer (R : Set G)) :
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) (centralizer ({z} : Set G))
    Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z,I⁆ : Subgroup G) = 2 := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  have hRH : R ≤ H := hRT.trans (original_sylow_le_centralizer hz)
  have hcore : R ⊓ centralizer (centralizerOmegaOrbit T z : Set G) = H.pCoreIn 2 := by
    apply le_antisymm
    · intro a ha
      have hc : (⟨a,hRH ha.1⟩ : H) ∈ centralizer (U : Set H) := by
        intro v hv
        exact Subtype.ext (ha.2 v.val hv)
      exact mem_map_of_mem H.subtype (hkernel ▸ hc)
    · intro a ha
      refine ⟨hQR ha, ?_⟩
      obtain ⟨b,hb,rfl⟩ := ha
      have hc : b ∈ centralizer (U : Set H) := hkernel.symm ▸ hb
      intro v hv
      exact congrArg Subtype.val (hc ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)
  have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hcore hB hout
  exact centralizer_thompson_single_factor_data_of_firstResidual h₀ hz hz1 R hRT hnR hQR hJ
    hsolv hkernel horder hthree hAN

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
