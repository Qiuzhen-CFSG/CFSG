module
public import CFSG.Quasithin.Chapter10.SourceA5ModuleQuadraticBound
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.CoveringClosure

/-!
# Covering uniqueness from a local module fixed by the odd actor

A nonzero L₀T-invariant submodule of the original V_M, fully moved by L₀,
lies in the two-core of the fixed perfect residual whenever the odd actor
fixes it. This supplies the nontrivial two-core in the covering argument.
The already proved nonnormal covering theorem gives uniqueness for the
literal residual joined with N_T(A). Consequently an escaping normalizer
has trivial two-core. No fixation of the full M-orbit is required.

Source: Aschbacher--Smith 4.4.5--7, printed p.620, as used by 4.4.14 and
10.2.3(2), printed pp.624--625 and745 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A local moved submodule fixed by the odd actor lies in the fixed residual's two-core. -/
theorem source_local_oddActor_cover
    (W : Subgroup G) (hWV : W ≤ D.fullModule)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    (A : Subgroup G) (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card A)) (hAW : A ≤ centralizer (W : Set G)) :
    let F := (solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (A : Set G)).subtype
    (localOrbit T L : Set G) = (F : Set G) * ((localOrbit T L).pCoreIn 2 : Set G) ∧
      W = ⁅W,F⁆ ∧ W ≤ F.pCoreIn 2 := by
  let X := localOrbit T L
  let C := X ⊓ centralizer (A : Set G)
  let F := (solvableResidual C).map C.subtype
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect X := isPerfect_iSup_conjugates L (T : Subgroup G)
  have hcover := perfect_centralizer_cover X A hAC hodd
  have hcore : X.pCoreIn 2 ≤ centralizer (W : Set G) := by
    apply (pCoreIn_mono_of_normalizes X.le_normalizer le_rfl).trans
    apply le_centralizer_iff.mpr
    intro w hw q hq
    obtain ⟨v,hv,rfl⟩ := D.fullModule_le_reduced (source_module_nonsolvable_uniqueness D) (hWV hw)
    obtain ⟨q',hq',rfl⟩ := hq
    exact congrArg Subtype.val
      (reducedPSubgroup_le_centralizer_pCore 2 D.maximalLocal hv q' hq')
  have he : W = ⁅W,F⁆ := hWX.trans
    (commutator_eq_of_product_centralizing_factor hcover (le_centralizer_iff.mp hcore))
  have hWC : W ≤ C := le_inf (hWV.trans D.fullModule_le_orbit) (le_centralizer_iff.mp hAW)
  have hWF : W ≤ normalizer (F : Set G) := hWC.trans
    (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (solvableResidual C)))
  have hin : W ≤ F := he ▸ le_normalizer_iff_commutator_le_right.mp hWF
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  have hp : IsPGroup 2 W := (IsElementaryAbelian.isPGroup 2 D.fullModule).to_le hWV
  exact ⟨hcover,he,le_pCoreIn_of_normalizes hp hin
    ((((map_subtype_le _).trans inf_le_left).trans le_sup_left).trans hNW)⟩

/-- Covering uniqueness uses only the displayed nonzero local moved module. -/
theorem source_local_oddPrimeActor_covering_uniqueness
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (W : Subgroup G) (hWV : W ≤ D.fullModule) (hne : W ≠ ⊥)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsPGroup p A)
    (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hAW : A ≤ centralizer (W : Set G))
    (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G)) :
    UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (A : Set G))) D.maximalLocal := by
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := hA.exists_card_eq
    rw [he]
    exact hp.pow
  let X := localOrbit T L
  let F := (solvableResidual (X ⊓ centralizer (A : Set G) : Subgroup G)).map
    (X ⊓ centralizer (A : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (A : Set G))
  obtain ⟨hcover,_,hWF⟩ := source_local_oddActor_cover D W hWV hWX hNW A hAC hodd hAW
  have hIM : I ≤ D.maximalLocal := sup_le
    (((map_subtype_le _).trans inf_le_left).trans X.le_normalizer)
    (inf_le_left.trans (le_normalizer_componentOrbit L T))
  have hIH : I ≤ localJoin T L := sup_le
    (((map_subtype_le _).trans inf_le_left).trans le_sup_left)
    (inf_le_left.trans le_sup_right)
  have hWI : W ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 F).to_le hWF)
    (hWF.trans ((pCoreIn_le 2 F).trans le_sup_left)) (hIH.trans hNW)
  have hIo : componentOrbit L I = X := by
    apply le_antisymm
    · exact iSup_conjugates_le_of_le_normalizer _ _ _ (le_componentOrbit L T) hIM
    · apply (source_oddPrimeActor_normalizer_orbit D hp A hA hAC hAT).symm.le.trans
      exact iSup_le fun t => le_iSup_of_le
        (⟨t,(show (T : Subgroup G) ⊓ normalizer (A : Set G) ≤ I from le_sup_right)
          t.property⟩ : I) le_rfl
  exact source_nonnormal_covering_uniqueness D hn hIM
    (hcover.subset.trans (Set.mul_subset_mul (show F ≤ I from le_sup_left) Set.Subset.rfl))
    (fun he => hne (bot_unique (hWI.trans_eq he))) hIo

/-- The nontrivial-two-core branch already gives the full normalizer bound from local fixation. -/
theorem source_local_oddPrimeActor_normalizer_of_twoCore
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (W : Subgroup G) (hWV : W ≤ D.fullModule) (hne : W ≠ ⊥)
    (hWX : W = ⁅W,localOrbit T L⁆)
    (hNW : localJoin T L ≤ normalizer (W : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsPGroup p A)
    (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hAW : A ≤ centralizer (W : Set G))
    (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hcore : pCore 2 (normalizer (A : Set G)) ≠ ⊥) :
    normalizer (A : Set G) ≤ D.maximalLocal := by
  have hu := source_local_oddPrimeActor_covering_uniqueness D hn W hWV hne hWX hNW
    hp A hA hAC hAW hAT
  obtain ⟨N,hN,hAN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (normalizer (A : Set G)) hcore
  have hIN : (solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (A : Set G)).subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (A : Set G)) ≤ normalizer (A : Set G) :=
    sup_le (((map_subtype_le _).trans inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _)) inf_le_right
  exact (hu.2.2 N hN (hIN.trans hAN)) ▸ hAN

end CFSG.Quasithin.Chapter10
