module
public import CFSG.Quasithin.Chapter14.Section02.ProperResidualControl
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SylowBlocks

/-!
# The original completion component is a χ₀-block under Sylow control

Let L be the canonical normal C-component in the proper completion and
R=O₂(YS). When the completion has characteristic two, the self-centralizing
core property descends to L and then to LR. The genuine C.1.29 component
criterion applies to LR: original uniqueness above YT supplies its
characteristic-normalizer control, and the original outside H supplies L⊄M.
Thus, if R is a Sylow two-subgroup of LR, L is the actual χ₀-block.
The remaining source step is precisely the Sylow assertion for R.

Source: Aschbacher--Smith 14.2.15, printed pp.985--986, using C.1.29.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_proper_component_chiZero_of_sylow_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2) (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : (K ⊔ sourceResidual M Mc ⊔ S).pCoreIn 2 ≠ ⊥)
    (hs : Chapter1.IsSylowIn 2 S (K ⊔ sourceResidual M Mc ⊔ S)) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    let R := (sourceResidual M Mc ⊔ S).pCoreIn 2
    X ∈ Chapter1.He G → IsQuasisimple (L ⧸ pCore 2 L) →
      Chapter1.IsSylowIn 2 R (L ⊔ R) → ChapterC.IsChiZeroBlock L := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  let R := (sourceResidual M Mc ⊔ S).pCoreIn 2
  change X ∈ Chapter1.He G → IsQuasisimple (L ⧸ pCore 2 L) →
    Chapter1.IsSylowIn 2 R (L ⊔ R) → ChapterC.IsChiZeroBlock L
  intro hXe hq hsR
  obtain ⟨hL,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcore hs
  have hLX : L ≤ X := map_subtype_le _
  have hRX : R ≤ X := (pCoreIn_le 2 _).trans (sup_le
    (le_sup_right.trans le_sup_left) le_sup_right)
  have hXN : X ≤ normalizer (L : Set G) := by
    have hh := (solvableResidual X).le_normalizer_map X.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hRN : R ≤ normalizer (L : Set G) := hRX.trans hXN
  have hLhc : centralizer (pCore 2 L : Set L) ≤ pCore 2 L :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hLX)).mp
      (subnormal_core_selfCentralizing (Chapter1.mem_He_iff.mp hXe) _ hL.2.subnormal)
  let D := L ⊔ R
  let L₀ := L.subgroupOf D
  have hDX : D ≤ X := sup_le hLX hRX
  let : L₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hRN)
  have hL₀ : L₀.IsCComponent := hL.2.subgroupOf_of_le le_sup_left hDX
  let := hq
  let : IsQuasisimple (L₀ ⧸ pCore 2 L₀) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show L ≤ D from le_sup_left))
      (pCore_map_iso 2 _)).symm
  have hf : generalizedFitting D = pCore 2 D :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_sup_le 2 L R hLhc (isPGroup_pCoreIn 2 _) hRN)
  have hsqX := Chapter1.RadicalExclusions.sqtk_of_mem_H hG hcore
  have hsq : IsSQTK KnownSimple.IsKnownSimple D :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hDX)).mp (hsqX.subgroup _)
  obtain ⟨P,hP⟩ := hsR
  have hPR : (P : Subgroup D) = R.subgroupOf D := by
    apply map_injective D.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show R ≤ D from le_sup_right)]
  have hLP : L₀ ⊔ (P : Subgroup D) = ⊤ := by
    rw [hPR,←subgroupOf_sup (show L ≤ D from le_sup_left)
      (show R ≤ D from le_sup_right),subgroupOf_self]
  have hcontrol := (source_proper_residual_core_control hG T hempty hM hu hmany
    hcard e S hST hi).2.2.2
  have hctl : (P : Subgroup D).characteristicNormalizerClosure ≤ M.subgroupOf D := by
    rw [hPR]
    exact characteristicNormalizerClosure_subgroupOf_le le_sup_right hcontrol
  have hout : ¬ L₀ ≤ M.subgroupOf D := by
    intro hh
    apply hH.1.2
    rw [←hgen]
    refine sup_le ?_ hM.1.2
    intro k hk
    exact hh (show (⟨k,mem_sup_left (hKL hk)⟩ : D) ∈ L₀ from hKL hk)
  have hb := ChapterC.C27Source.normal_component_chiZero_of_sylow_control hsq hf
    L₀ hL₀ P (M.subgroupOf D) hLP hctl hout
  exact hb.2.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ D from le_sup_left))
end CFSG.Quasithin.Chapter14.Section02
