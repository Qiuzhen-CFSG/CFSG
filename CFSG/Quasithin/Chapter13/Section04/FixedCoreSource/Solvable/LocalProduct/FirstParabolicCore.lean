module
public import Theory.GroupTheory.PResidual.SectionSylow
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.LargerShortBlock

/-!
# The first parabolic core in both short-block kernel cases

Set R=O₂(L₁T), with the literal L₁=O^{3′}(C_L(z)). Its containment in T,
normalization by L₁ and T, and containment of O₂(C_G(z)) follow from
core restriction. In the larger-kernel case, the earlier 13.3.9 theorem
identifies L₁ with O²(C_H(V_H)); SectionSylow then constructs the Sylow
witness in C_H(L₁/O₂(L₁)), on the original T.

The final theorem applies both checked short-block arguments to this
fixed R. It proves the ordinary row, both local quotients, moved-plane
rank, H=L₁IT and uniqueness of IT without a supplied residual-section
Sylow, normalization or core-containment hypothesis.

Notation 13.2.1 identifies R₁ with O₂(L₁T) in the ordinary row. FirstParabolicAction
identifies the literal action-core preimage on L₁T. Its identification
with N_LT(V₁), V≤J(R₁), and the non-block branch remain source obligations. The explicit earlier 13.3.9,
13.2.2(5–6) and 13.4.2–3 inputs retain final discharge with
qt-d-1341-fixed-core-source and its producers; the local source assembly,
C₃ geometry and fusion remain owned by qt-d-1341-solvable-source.
Source: Aschbacher–Smith 13.2.1, 13.4.4(2), 13.4.8, pp.877,897,904–905.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The ordinary first-parabolic core, with the original residual and Sylow subgroup. -/
def firstParabolicCore (T : Sylow 2 G) (L : Subgroup G) (z : G) : Subgroup G :=
  (firstCentralizerResidual L z ⊔ (T : Subgroup G)).pCoreIn 2

omit [Finite G] in
/-- All core-containment and normalization inputs for the fixed first parabolic. -/
theorem firstParabolicCore_local_data {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) :
    firstParabolicCore T L z ≤ T ∧
      (T : Subgroup G) ≤ normalizer (firstParabolicCore T L z : Set G) ∧
      firstCentralizerResidual L z ≤ normalizer (firstParabolicCore T L z : Set G) ∧
      (centralizer ({z} : Set G)).pCoreIn 2 ≤ firstParabolicCore T L z := by
  let A := firstCentralizerResidual L z
  let P := A ⊔ (T : Subgroup G)
  let H := centralizer ({z} : Set G)
  have hTP : (T : Subgroup G) ≤ P := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hPH : P ≤ H := sup_le ((firstCentralizerResidual_le L z).trans inf_le_right) hTH
  have hRT : P.pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP]
      using pCoreIn_le_sylow P (T.subtype hTP)
  have hn : P ≤ normalizer (P.pCoreIn 2 : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  refine ⟨hRT,hTP.trans hn,(show A ≤ P from le_sup_left).trans hn,?_⟩
  have hQH : H.pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
      using pCoreIn_le_sylow H (T.subtype hTH)
  exact (le_inf (hQH.trans hTP) le_rfl).trans (inf_pCoreIn_le_of_le 2 hPH)

/-- The residual identity constructs the Sylow witness required by the larger-kernel branch. -/
theorem firstParabolicCore_residual_sylow
    (h₀ : Hypothesis1331 T L) {z : G}
    (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hres : let H := centralizer ({z} : Set G)
      let K := centralizer ((centralizerOmegaOrbit T z).subgroupOf H : Set H)
      ((pResidual 2 K).map K.subtype).map H.subtype = firstCentralizerResidual L z) :
    ∃ S : Sylow 2 (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z).subgroupOf
        (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))))),
      ((S : Subgroup _).map (residualSectionCentralizer 2
        (centralizer ((centralizerOmegaOrbit T z).subgroupOf
          (centralizer ({z} : Set G)) : Set (centralizer ({z} : Set G))))).subtype).map
            (centralizer ({z} : Set G)).subtype = firstParabolicCore T L z := by
  let H := centralizer ({z} : Set G)
  let U := (centralizerOmegaOrbit T z).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz hz1).normal
  let K := centralizer (U : Set H)
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  obtain ⟨S,hS⟩ := exists_sylow_residualSection_map_eq_join_core K (T.subtype hTH)
  refine ⟨S,?_⟩
  have hm := congrArg (map H.subtype) hS
  rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,Subgroup.map_sup,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,hres] at hm
  exact hm

/-- Both short-block kernel cases for the fixed first-parabolic core. -/
theorem centralizer_pair_quotient_of_short_block_firstParabolicCore
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstParabolicCore T L z.val))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstParabolicCore T L z.val)) H
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z.val ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ∧
      (H : Set G) = (firstCentralizerResidual L z.val : Set G) * (I : Set G) * (T : Set G) ∧
      I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ H →
        (Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ↔
          Y = I ⊔ (T : Subgroup G)) := by
  let R := firstParabolicCore T L z.val
  obtain ⟨hRT,hnR,hAN,hQR⟩ := firstParabolicCore_local_data (L := L) hz
  by_cases hkernel : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) =
      pCore 2 (centralizer ({z.val} : Set G))
  · have h1339' : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
        centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
        Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
        Y = ⊥ ∨ Nat.card (Y ⧸ pCore 2 Y) = 3 := by
      intro Y hYH hn hYM hp
      exact (h1339 Y hYH hn hYM hp).imp_right (fun hh => hh.2)
    obtain ⟨hq,hI,hr,hprod,hinter,hset⟩ := centralizer_pair_quotient_of_short_block
      h₀ h structural D m hb z hz hzL R hRT hnR hQR hVJ hsolv hkernel hout hindex
      hAN h1339' h1342
    have hcore : IsPGroup 2 (centralCore L) := by
      rw [centralCore_eq_twoCore_of_short_core_marking D m hb]
      exact pCore_isPGroup
    have hu := centralizer_thompson_unique_of_source_product D m hcore z hzL hz R hRT
      hI hprod hinter hout
    exact ⟨ordinary_of_short_core_marking D m hb,hq,hI,hr,hprod,hinter,hset,hu⟩
  · have hres := (centralizer_short_block_residual_normal_of_source1339
      h₀ h structural D m hb z hz hzL hkernel h1339).1
    obtain ⟨S,hS⟩ := firstParabolicCore_residual_sylow h₀ hz
      (fun he => hzL (he ▸ one_mem _)) hres
    exact centralizer_pair_quotient_of_larger_short_block h₀ h structural D m hb z hz hzL
      hkernel R hRT S hS hVJ hout hfusion h1339 hsolv hindex h1342

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
