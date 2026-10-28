module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryLinear
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import Theory.SpecificGroups.PSL3Two.SolvableSylowOvergroups
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Binary central covers do not enlarge quasisimple local components

Restrict the original Sylow to the containing C-component and pass through
its actual central covering map. The image of the smaller component remains
quasisimple and local for the full image Sylow. The binary degree-three,
four and five Sylow-overgroup theorems force equality downstairs; perfection
then removes the central supplement upstairs.

The SL₂(7) and central-quotient applications are in the Chapter 12
LocalConfigurationRigidityHigherCentralCovers extension.
Source: Aschbacher–Smith A.3.12, printed pp.47–48, as used in 12.2.25, p.805.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

theorem eq_of_binary_linear_central_cover
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    [IsQuasisimple B] (f : L →* Q) (hf : Function.Surjective f)
    (hk : f.ker ≤ center L) {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (hmodel : ClassicalGroup.IsPSL Q n 2) : B = L := by
  obtain ⟨S,hS,hBS⟩ := exists_local_sylow_restriction T hB hBL hL.subnormal
  let D := B.subgroupOf L
  let eD := subgroupOfEquivOfLe hBL
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv eD.symm
  let : Group.IsSolvable f.ker := Group.isSolvable_of_comm (fun x y =>
    Subtype.ext (mem_center_iff.mp (hk y.property) x.val))
  let Sq := S.mapSurjective hf
  have hDq : D.map f ∈ localCComponents Sq := localCComponents_map_of_solvable_ker hBS f
  have hne : D.map f ≠ ⊥ := by
    intro he
    have hh := hDq.ne_bot
    simp only [he, bot_subgroupOf] at hh
    exact hh rfl
  let : Nontrivial (D.map f) := (nontrivial_iff_ne_bot _).mpr hne
  let : IsQuasisimple (D.map f) := IsQuasisimple.of_surjective
    (f.subgroupMap D) (f.subgroupMap_surjective D)
  have htop : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self] using hL.subgroupOf le_rfl
  have hQ : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective f hf] using cComponent_map_of_solvable_ker htop f hf
  have he : D.map f = ⊤ := by
    rcases hn with rfl | hn
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
      exact eq_of_solvable_sylow_overgroups Sq hDq hQ le_top
        (SolvableSylowOvergroups.of_equiv (topEquiv.trans e)
          (Matrix.PSL3Two.solvableSylowOvergroups_projective_of_card_two hF))
    · exact eq_of_binary_linear_four_or_five Sq hDq hQ le_top hn
        (hmodel.of_mulEquiv topEquiv)
  let := hL.perfect
  have ht : D = ⊤ := top_unique
    (perfect_le_of_map_le_of_central_kernel f hk (⊤ : Subgroup L) D (by rw [he]; exact le_top))
  exact le_antisymm hBL (subgroupOf_eq_top.mp ht)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
