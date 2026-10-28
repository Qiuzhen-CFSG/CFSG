module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Sieve
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.ImageAction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.Assembly

/-!
# The selected orthogonal configuration is impossible

The original lift supplies D, its full normalizer Sylow and the corrected
local C-component B = (K₀UD)∞. The image-action construction identifies the
literal image of B in N_G(D)/O₂(N_G(D)) with a deleted-five extension.
The complete carrier sieve then gives a contradiction. In particular no
embedding-classification or image-action premise remains.

The final consumer constructs the lift from the selected involution,
marked orthogonal component square, exchanged action and centralizer
comparison. These are explicit earlier geometric inputs. Constructing them
from the original Counterexample and invariant flag, including U = O₂(H),
remains necessary to prove the whole orthogonal branch of 14.4.14.

Source: Aschbacher--Smith, Lemma 14.4.9, printed pp.1009--1010.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open LargerDimension.Orthogonal LargerDimension.Orthogonal.ComponentSieve
variable {G : Type*} [Group G] [Finite G]

/-- The original normalizer quotient excludes a binary-five core action on the
actual image of any Sylow-normalized local component. -/
theorem no_normalizer_binary_five
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (D B : Subgroup G) (hD : IsPGroup 2 D) (hne : D ≠ ⊥)
    (P : Sylow 2 (normalizer (D : Set G)))
    (hl : B.subgroupOf (normalizer (D : Set G)) ∈ localCComponents P)
    (hn : (P : Subgroup (normalizer (D : Set G))) ≤
      normalizer (B.subgroupOf (normalizer (D : Set G)) : Set (normalizer (D : Set G))))
    (m : let N := normalizer (D : Set G)
      let Bbar := (B.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
      BinaryPermutation.FiveConjugation Bbar (pCore 2 Bbar)) : False := by
  let N := normalizer (D : Set G)
  let q := QuotientGroup.mk' (pCore 2 N)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 N) := (pCore_isPGroup (p := 2) (G := N)).isNilpotent
    infer_instance
  have hN : IsSQTK KnownSimple.IsKnownSimple N :=
    hG.twoLocal_sqtk ⟨D,hne,hD,rfl⟩
  exact no_core_free_binary_five
    (ChapterE.Structure.sqtk_two_quotient hN (pCore 2 N) pCore_isPGroup)
    (pCore_quotient_pCore_eq_bot 2)
    (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 N))) _
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
    ((map_mono hn).trans ((B.subgroupOf N).le_normalizer_map q)) m

/-- Apply the complete carrier sieve to the corrected orthogonal residual.
The selected lift supplies local placement and the original full Sylow.
The literal image-core action is constructed, with no classification input. -/
theorem source_selected_lift_contradiction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (U : Subgroup G) [IsExtraspecial 2 U] (T : Sylow 2 G) (z x : G)
    (hz : orderOf z = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hiT : conjugateElement z x ∈ T) (hout : conjugateElement z x ∉ U)
    (hKU : diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
      normalizer (U : Set G))
    (m : MovedCoreModel U
      (diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x))
      (conjugateElement z x) hKU)
    (d : QuotientModel.SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
        ⟨conjugateElement z x,hTz hiT⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x)).subgroupOf
        (centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))))
    (r : LiftResult U T z x hKU m) : False := by
  let i := conjugateElement z x
  let D := centralizerLift U z i
  let N := normalizer (D : Set G)
  let S := localSylow (T : Subgroup G) D
  let A := diagonalResidual (centralizer ({z} : Set G)) i ⊔ U
  let J := A ⊔ D
  let B := (solvableResidual J).map J.subtype
  have hl : B ∈ Chapter1.LIn N S :=
    source_residual_mem_localFamily U T z x hz hZ hUcore hTz hiT hout hKU m d r
  obtain ⟨P,hP⟩ := r.global_sylow
  have hl' : B.subgroupOf N ∈ localCComponents P := by
    rw [hP]
    exact local_restrict hl.2.1 hl.1
  have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
  have hi : orderOf i = 2 := by
    simpa only [i,conjugateElement,MulEquiv.orderOf_eq] using hz
  have hiU : i ∈ normalizer (U : Set G) := by
    have hh := (centralizer ({z} : Set G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image
        (centralizer ({z} : Set G)) (pCore 2 (centralizer ({z} : Set G))))
    change centralizer ({z} : Set G) ≤
      normalizer ((centralizer ({z} : Set G)).pCoreIn 2 : Set G) at hh
    rw [hUcore] at hh
    exact hh (hTz hiT)
  let : IsElementaryAbelian 2 D := r.actions.chief.elementary_D
  have hD : IsPGroup 2 D := IsElementaryAbelian.isPGroup 2 D
  have hSA : S ≤ normalizer (A : Set G) :=
    source_normalizes_actor U S z i hi hUcore hzU (hTz hiT) hout
      (inf_le_left.trans hTz) inf_le_right d
  have he : B = (solvableResidual A).map A.subtype :=
    corrected_residual_eq U z i hzU hiU hD
  have hn : S ≤ normalizer (B : Set G) := by
    rw [he]
    exact hSA.trans (normalizer_le_normalizer_characteristic_image A (solvableResidual A))
  have hn' : (P : Subgroup N) ≤ normalizer (B.subgroupOf N : Set N) := by
    rw [hP, ← subgroupOf_normalizer_eq hl.1]
    exact subgroupOf_mono N hn
  have hne : D ≠ ⊥ := by
    intro hb
    have hc : Nat.card D = 64 := r.actions.chief.card_D
    rw [hb] at hc
    simp at hc
  obtain ⟨binary⟩ := source_residual_binary_image U T z x hzU hiU hKU m r
  exact no_normalizer_binary_five hG D B hD hne P hl' hn' binary

/-- The selected case-(3) geometry constructs the lift and contradicts the
complete carrier sieve. No embedding or image-action premise remains. -/
theorem source_selected_configuration_contradiction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (U : Subgroup G) [IsExtraspecial 2 U] (T : Sylow 2 G) (z x : G)
    (hz : orderOf z = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hUcard : Nat.card U = 512)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hiT : conjugateElement z x ∈ T)
    (hout : conjugateElement z x ∉ U)
    (hKU : diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
      normalizer (U : Set G))
    (m : MovedCoreModel U
      (diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x))
      (conjugateElement z x) hKU)
    (exchanged : ExchangedModel.CaseThreeAction
      (centralizer ({conjugateElement z x} : Set G)) (conjugateCore U x))
    (components : QuotientModel.SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
        ⟨conjugateElement z x,hTz hiT⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x)).subgroupOf
        (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))))
    (hcompare : ((commutatorPreimage (centralizer ({z} : Set G))
        (zpowers (conjugateElement z x)) (zpowers z)).subgroupOf
        (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) =
      centralizer ({QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))
        ⟨conjugateElement z x,hTz hiT⟩} :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) :
    False := by
  obtain ⟨r⟩ := lift_of_selected_configuration U T z x hz hZ hUcore hUcard hTz
    hiT hout hKU m exchanged components hcompare
  exact source_selected_lift_contradiction hG U T z x hz hZ hUcore hTz hiT hout
    hKU m components r

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
