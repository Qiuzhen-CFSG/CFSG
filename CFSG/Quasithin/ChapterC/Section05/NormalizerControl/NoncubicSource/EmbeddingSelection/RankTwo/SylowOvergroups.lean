module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.CharacteristicTwo
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.SymplecticOrthogonal.RankTwo
public import Theory.GroupTheory.SolvableRadical
/-!
# The proper Sylow-overgroup bound in the C.5.13 embedding sieve

A quasisimple local C-component lies in the generalized Fitting subgroup
of the join with the actual full Sylow. If this join is proper, the known
Sylow-overgroup bound makes its generalized Fitting subgroup solvable, a
contradiction. The symplectic and small-derived carriers supply the bound
from their original parabolic geometry.
Source: Aschbacher–Smith A.3.12 and C.5.13, printed pp.47–48,162–163.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open ChapterB.ComponentRecognition.SylowOvergroups
variable {G : Type*} [Group G] [Finite G]
theorem eq_of_proper_sylow_fitting_bound
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] (hproper : ProperSylowFittingBound L) : B = L := by
  obtain ⟨S, _, hlocal⟩ := exists_local_sylow_restriction T hB hBL hL.subnormal
  let C := B.subgroupOf L
  let J := C ⊔ (S : Subgroup L)
  change (C.subgroupOf J).IsCComponent at hlocal
  have hJ : J = ⊤ := by
    by_contra hne
    let e : C.subgroupOf J ≃* B :=
      (subgroupOfEquivOfLe (show C ≤ J from le_sup_left)).trans
        (subgroupOfEquivOfLe hBL)
    let : Nontrivial (C.subgroupOf J) := (nontrivial_iff_ne_bot _).mpr hlocal.ne_bot
    have hq : IsQuasisimple (C.subgroupOf J) :=
      IsQuasisimple.of_surjective e.symm.toMonoidHom e.symm.surjective
    have hle := (component_le_generalizedFitting J (C.subgroupOf J)
      ⟨hlocal.subnormal,hq⟩).trans (hproper S J le_sup_right hne)
    let : Group.IsNilpotent (pCore 2 J) := pCore_isNilpotent
    let : IsMulCommutative ((center L).subgroupOf J) :=
      Subgroup.subgroupOf_isMulCommutative _ _
    let : Group.IsSolvable (pCore 2 J ⊔ (center L).subgroupOf J : Subgroup J) :=
      Group.isSolvable_sup_of_normal_left _ _
    exact hlocal.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hle) (inclusion_injective hle))
  rw [hJ] at hlocal
  have hC : C.IsCComponent := by
    have h := hlocal.map_subtype (show (⊤ : Subgroup L).IsSubnormal from .top)
    simpa only [map_subgroupOf_eq_of_le le_top] using h
  exact le_antisymm hBL (subgroupOf_eq_top.mp (hL.eq_top_of_isCComponent hC))
/-- The nonbinary symplectic row of the original rank-two list. -/
theorem eq_of_binary_symplectic_model
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSp L 2 (2 ^ n)) : B = L := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  exact eq_of_proper_sylow_fitting_bound T hB hL hBL
    (properSylowFittingBound_of_equiv e
      (properSylowFittingBound_psp_two F n (by omega) hF))

/-- The literal derived PSp₄(2) carrier, with no simple-group substitution. -/
theorem eq_of_binary_symplectic_derived_model
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B]
    (hmodel : Nonempty (L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) : B = L := by
  obtain ⟨e⟩ := hmodel
  exact eq_of_proper_sylow_fitting_bound T hB hL hBL
    (properSylowFittingBound_of_equiv e properSylowFittingBound_binary_symplectic_derived)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
