module
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original

/-!
# Ordinary components and full-Sylow local components

The known-simple A.3.12 containment theorem applies after quotienting by
O₂(G). Solvable-kernel lifting returns the unique containing C-component.
An ordinary component either is that C-component or centralizes it, giving
a containment-or-centralization dichotomy for the original local subgroup.

Source: Aschbacher--Smith A.3.12 and 1.2.4, printed pp.47--48,505;
the moved-block application in 14.6.9, printed p.1026.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

theorem existsUnique_containing_cComponent_knownSimple (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S) :
    ∃! C : Subgroup G, C.IsCComponent ∧ B ≤ C := by
  let := pCore_isNilpotent (p := 2) (G := G)
  let : Group.IsSolvable (QuotientGroup.mk' (pCore 2 G)).ker := by
    rw [QuotientGroup.ker_mk']; infer_instance
  let : Group.IsPerfect (B.subgroupOf (B ⊔ S)) := hB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).surjective
  apply existsUnique_cComponent_lift_containing (pCore 2 G)
  apply Chapter1.Section02.containment_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    _ (ChapterE.Structure.sqtk_two_quotient hG (pCore 2 G) pCore_isPGroup)
    (pCore_quotient_pCore_eq_bot 2)
    (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G)))
  simpa only [Sylow.coe_mapSurjective] using
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB
      (QuotientGroup.mk' (pCore 2 G))

theorem local_ordinary_dichotomy (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (S : Sylow 2 G) {B A : Subgroup G} (hB : B ∈ localCComponents S)
    (hA : IsComponent G A) : B ≤ A ∨ B ≤ centralizer (A : Set G) := by
  obtain ⟨C,⟨hC,hBC⟩,_⟩ := existsUnique_containing_cComponent_knownSimple hG S hB
  rcases hA.subnormal_dichotomy C hC.subnormal with hac | hc
  · left
    exact hBC.trans_eq (hA.isCComponent.eq_of_le hC hac).symm
  · right
    have hh : ⁅A,B⁆ = ⊥ := bot_unique ((commutator_mono le_rfl hBC).trans hc.le)
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
