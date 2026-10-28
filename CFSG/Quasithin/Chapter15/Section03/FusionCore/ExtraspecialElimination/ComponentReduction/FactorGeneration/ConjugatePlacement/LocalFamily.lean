module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.LocalTransfer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.SectionConstruction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.Core
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The edge intersection and inheritance by local overgroups

The earlier factorization C_M(Z) = C_M(V)T places O²(C_Y(Z)) in C_Y(V).
Residual monotonicity and two-perfectness identify this L₁ with
Y₀ = O²(C_Y(V)). The residual–Sylow supplement gives C_Y(Z) ≤ L₁T,
so H ∩ YT = L₁T whenever H centralizes Z and contains L₁T.

Every Y₀T ≤ K ≤ H outside M inherits membership in the genuine local
family: the Sylow subgroup carries the nontrivial O₂(H) into O₂(K).
Theta descends by the existing monotonicity theorem. The same supplement
argument puts C_Y(V) in K, retaining 15.3.48's extraspecial side condition.
Both U_K = localSpan ZS K and V_K = localSpan V K are elementary abelian.
The action on U_K/Z is reconstructed from 15.3.48(3) at K, which remains
an explicit earlier input; no faithfulness or best-offender assertion is
inherited by restricting the action on U_H/Z.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.48 and
15.3.49(b), (d), and the local application before (j), printed pp.1142–1144.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement
variable {G : Type*} [Group G]

private theorem residual_eq [Finite G] (A : Subgroup G) :
    Stellmacher.twoResidualAmbient A = (pResidual 2 A).map A.subtype := by
  unfold Stellmacher.twoResidualAmbient
  congr 1
  unfold Stellmacher.twoResidualSubgroup pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    let := hN
    exact ⟨hN, IsPGroup.iff_card.mpr ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩⟩
  · rintro ⟨hN, hp⟩
    let := hN
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    exact ⟨hN, n, by simpa [Subgroup.index_eq_card] using hn⟩

/-- The earlier product factorization identifies the two source residuals, without assuming their equality. -/
theorem localL1_eq_Y0 [Finite G]
    (M Y V Z : Subgroup G) (T : Sylow 2 G)
    (hYM : Y ≤ M) (hM : M ≤ normalizer (V : Set G))
    (hTM : (T : Subgroup G) ≤ M) (hZV : Z ≤ V)
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x) :
    CosetSetup.localL1 Y Z = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G)) := by
  have hL := CosetSetup.localL1_le_centralizer M Y V Z T hYM hM hTM hfactor
  have hp : IsPPerfect 2 (CosetSetup.localL1 Y Z) := by
    rw [CosetSetup.localL1, residual_eq]
    exact isPPerfect_embedded_pResidual 2 _
  apply le_antisymm
  · have hr := embedded_pResidual_mono 2 hL
    rw [(pResidual_eq_top_iff 2 _).mpr hp, ← MonoidHom.range_eq_map, range_subtype,
      ← residual_eq] at hr
    exact hr
  · simp only [CosetSetup.localL1, residual_eq]
    exact embedded_pResidual_mono 2 (inf_le_inf_left Y (centralizer_le hZV))

private theorem core_le_sylow (H : Subgroup G) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) :
    H.pCoreIn 2 ≤ (T : Subgroup G) := by
  let S := T.comapOfInjective H.subtype H.subtype_injective (by simpa using hTH)
  have he : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_comap_eq_self (by simpa using hTH)
  exact (pCoreIn_le_sylow H S).trans_eq he

/-- Every intermediate overgroup of Y₀T outside M inherits the nontrivial local two-core. -/
theorem intermediate_mem_outsideFamily
    (M H K Y0 : Subgroup G) (T : Sylow 2 G)
    (hQ : localTwoCore H ≠ ⊥) (hKH : K ≤ H)
    (hYK : Y0 ⊔ (T : Subgroup G) ≤ K) (hKM : ¬ K ≤ M) :
    K ∈ outsideFamily Y0 (T : Subgroup G) M := by
  have hQK : H.pCoreIn 2 ≤ K :=
    (core_le_sylow H T (le_sup_right.trans (hYK.trans hKH))).trans (le_sup_right.trans hYK)
  have hc : H.pCoreIn 2 ≤ K.pCoreIn 2 := by
    simpa only [inf_eq_right.mpr hQK] using inf_pCoreIn_le_of_le 2 hKH
  refine ⟨⟨?_, hYK⟩, hKM⟩
  intro hb
  exact hQ (le_bot_iff.mp (hc.trans_eq hb))

private theorem normalized_le_residual_sup_sylow [Finite G]
    (C : Subgroup G) (T : Sylow 2 G) (hTC : (T : Subgroup G) ≤ normalizer (C : Set G)) :
    C ≤ Stellmacher.twoResidualAmbient C ⊔ (T : Subgroup G) := by
  let D := C ⊔ (T : Subgroup G)
  let S := T.comapOfInjective D.subtype D.subtype_injective (by rw [range_subtype]; exact le_sup_right)
  have hn : (C.subgroupOf D).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hTC)
  let := hn
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal (C.subgroupOf D)
  have hr : ((R : Subgroup (C.subgroupOf D)).map (C.subgroupOf D).subtype).map D.subtype ≤
      (T : Subgroup G) := by
    rw [hR, subgroupOf_map_subtype]
    exact (map_mono inf_le_left).trans_eq (map_comap_eq_self (by rw [range_subtype]; exact le_sup_right))
  have hs := congrArg (fun A : Subgroup (C.subgroupOf D) =>
    (A.map (C.subgroupOf D).subtype).map D.subtype) (pResidual_sup_sylow_eq_top R)
  have hres : ((pResidual 2 (C.subgroupOf D)).map (C.subgroupOf D).subtype).map D.subtype =
      Stellmacher.twoResidualAmbient C := by
    rw [map_map, residual_eq]
    have hm := map_pResidual_of_surjective 2 (subgroupOfEquivOfLe (show C ≤ D from le_sup_left)).toMonoidHom
      (subgroupOfEquivOfLe (show C ≤ D from le_sup_left)).surjective
    rw [← hm, map_map]
    rfl
  rw [Subgroup.map_sup, Subgroup.map_sup, hres, ← MonoidHom.range_eq_map,
    range_subtype, map_subgroupOf_eq_of_le (show C ≤ D from le_sup_left)] at hs
  exact hs.ge.trans (sup_le_sup_left hr _)

open scoped Pointwise in
/-- The source centralizer condition and residual supplement determine the standard edge intersection. -/
theorem base_edge_eq_localL1 [Finite G]
    (Y H Z : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hHZ : H ≤ centralizer (Z : Set G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hLH : CosetSetup.localL1 Y Z ≤ H) :
    H ⊓ (Y ⊔ (T : Subgroup G)) = CosetSetup.localL1 Y Z ⊔ (T : Subgroup G) := by
  have hTC : (T : Subgroup G) ≤ normalizer ((Y ⊓ centralizer (Z : Set G)) : Set G) :=
    (le_inf hTY ((hTH.trans hHZ).trans (centralizer (Z : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hc := normalized_le_residual_sup_sylow (Y ⊓ centralizer (Z : Set G)) T hTC
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (Y : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left Y (T : Subgroup G) hTY]
      exact hx.2
    obtain ⟨y, hy, t, ht, rfl⟩ := hx'
    have hyZ : y ∈ centralizer (Z : Set G) := by
      have := (centralizer (Z : Set G)).mul_mem (hHZ hx.1)
        ((centralizer (Z : Set G)).inv_mem (hHZ (hTH ht)))
      simpa only [mul_inv_cancel_right] using this
    exact (CosetSetup.localL1 Y Z ⊔ (T : Subgroup G)).mul_mem
      (hc ⟨hy, hyZ⟩) ((le_sup_right : (T : Subgroup G) ≤ _) ht)
  · apply sup_le (le_inf hLH ?_) (le_inf hTH le_sup_right)
    have hr : CosetSetup.localL1 Y Z ≤ Y ⊓ centralizer (Z : Set G) := by
      rw [CosetSetup.localL1, residual_eq]
      exact map_subtype_le _
    exact (hr.trans inf_le_left).trans le_sup_left

/-- Every intermediate overgroup of Y₀T retains the extraspecial side condition of 15.3.48. -/
theorem centralizer_le_intermediate [Finite G]
    (Y V Y0 K : Subgroup G) (T : Sylow 2 G)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hY0 : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G)))
    (hYK : Y0 ⊔ (T : Subgroup G) ≤ K) : Y ⊓ centralizer (V : Set G) ≤ K := by
  have hTC : (T : Subgroup G) ≤ normalizer ((Y ⊓ centralizer (V : Set G)) : Set G) :=
    (le_inf hTY (hTV.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hc := normalized_le_residual_sup_sylow (Y ⊓ centralizer (V : Set G)) T hTC
  rw [← hY0] at hc
  exact hc.trans hYK

/-- Reconstruct the action on the local span quotient from its centralizer kernel. -/
noncomputable def intermediateSectionAction
    (V ZS Z K : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS K)]
    [(Z.subgroupOf K).Normal]
    (hZ : Z ≤ ZS) (hZS : ZS ≤ V) (hVK : V ≤ K)
    (hKZ : K ≤ centralizer (Z : Set G))
    (hkernel : CosetSetup.quotientCentralizer K (localSpan ZS K) Z = pCore 2 K) :
    SectionAction K (localSpan ZS K) Z := by
  let := CosetSetup.layer_normal K Z hKZ
  exact sectionActionOfCentralizer K (localSpan ZS K) Z
    (hZ.trans (le_conjugateSpanBy ZS K))
    (conjugateSpanBy_le_self (hZS.trans hVK))
    (le_normalizer_conjugateSpanBy ZS K)
    (hKZ.trans (Subgroup.centralizer_le_normalizer _)) hkernel

/-- Local-family membership, theta, the extra centralizer containment, and both elementary spans at K. -/
theorem intermediate_local_data [Finite G]
    (M Y Y0 H K V ZS Z : Subgroup G) (T : Sylow 2 G)
    [IsElementaryAbelian 2 (localSpan V H)]
    (hQ : localTwoCore H ≠ ⊥) (hKH : K ≤ H)
    (hYK : Y0 ⊔ (T : Subgroup G) ≤ K) (hKM : ¬ K ≤ M)
    (hθ : theta (M ⊓ H) = Y0)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hY0 : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G)))
    (hHZ : H ≤ centralizer (Z : Set G)) (hZS : ZS ≤ V) :
    K ∈ outsideFamily Y0 (T : Subgroup G) M ∧
      theta (M ⊓ K) = Y0 ∧ Y ⊓ centralizer (V : Set G) ≤ K ∧
      K ≤ centralizer (Z : Set G) ∧
      IsElementaryAbelian 2 (localSpan ZS K) ∧
      IsElementaryAbelian 2 (localSpan V K) := by
  exact ⟨intermediate_mem_outsideFamily M H K Y0 T hQ hKH hYK hKM,
    theta_intermediate M H K Y0 hKH (le_sup_left.trans hYK) hθ,
    centralizer_le_intermediate Y V Y0 K T hTY hTV hY0 hYK,
    hKH.trans hHZ, localSpan_elementary_of_le V ZS H K hZS hKH,
    localSpan_elementary_of_le V V H K le_rfl hKH⟩

/-- Construct the faithful action on U_K/Z using elementary inheritance and the kernel theorem at K. -/
noncomputable def sectionActionAtIntermediate
    (V ZS Z H K : Subgroup G) [IsElementaryAbelian 2 (localSpan V H)]
    (hZ : Z ≤ ZS) (hZS : ZS ≤ V) (hVK : V ≤ K) (hKH : K ≤ H)
    (hHZ : H ≤ centralizer (Z : Set G))
    (hkernel : letI := CosetSetup.layer_normal K Z (hKH.trans hHZ)
      CosetSetup.quotientCentralizer K (localSpan ZS K) Z = pCore 2 K) :
    letI := localSpan_elementary_of_le V ZS H K hZS hKH
    SectionAction K (localSpan ZS K) Z := by
  letI := localSpan_elementary_of_le V ZS H K hZS hKH
  letI := CosetSetup.layer_normal K Z (hKH.trans hHZ)
  exact intermediateSectionAction V ZS Z K hZ hZS hVK (hKH.trans hHZ) hkernel

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement
