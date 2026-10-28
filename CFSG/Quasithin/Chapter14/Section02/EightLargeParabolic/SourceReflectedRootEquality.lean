module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReflectedRootConjugacy
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootFixedConjugator

/-!
# The corrected eight-reflection has the same original root

The actual root-lift theorem gives a seven-fixed full-core conjugator.
If it fixes the second vertex it centralizes the old root. Otherwise the
unchanged opposite reflection and odd seven-path fixers separate its twist
from the new root. Consequently the two actual roots coincide.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph
open Subgroup.CosetGeometry Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReflectedRootEquality
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => Universal.cosetFamily A
local notation "P" => RankTwo.stabilizer F (base F true)

/-- The actual original eight-root is unchanged whenever the opposite
reflection is retained and the original root lies in the prescribed full-core complement. -/
@[expose] def HasReflectedRootEquality (c:CompatibleCartans L (reducedSylow L S)) : Prop :=
  ∀ d d':SixPathSmallActorGeometry c,d'.reflection false=d.reflection false →
    let p := reflectionPath c d.reflection d.fixes d.moves d.normalizes 6 (by decide) true
    let r := reflectionPath c d'.reflection d'.fixes d'.moves d'.normalizes 6 (by decide) true
    ∀ K:Subgroup (A).Universal,K≤P →
      (pCore 2 P).IsComplement' (K.subgroupOf P) → cartan c≤K →
      pathRoot (X := (A).Universal) p.walk≤K →
      pathRoot (X := (A).Universal) r.walk=pathRoot (X := (A).Universal) p.walk

private theorem assemble (h:HypothesisF11 L S) (c:CompatibleCartans L (reducedSylow L S))
    (hconj:SourceReflectedRootConjugacy.HasReflectedRootConjugacy c)
    (hfixed:SourceRootFixedConjugator.HasRootFixedConjugators c) :
    HasReflectedRootEquality c := by
  intro d d' hother
  dsimp only
  intro K hKP hK hCK hRK
  let p := reflectionPath c d.reflection d.fixes d.moves d.normalizes 6 (by decide) true
  let r := reflectionPath c d'.reflection d'.fixes d'.moves d'.normalizes 6 (by decide) true
  obtain ⟨u,hu,he⟩ := hconj d d' K hKP hK hCK hRK
  by_cases hf : u • p.walk.reverse.getVert 2=p.walk.reverse.getVert 2
  · have hc := hfixed p.walk p.isPath p.length_eq p.previous u hu hf
    have hn : u∈normalizer (pathRoot (X := (A).Universal) p.walk:Set (A).Universal) :=
      Subgroup.centralizer_le_normalizer _ hc
    exact he.trans (mem_normalizer_iff_map_conj_eq.mp hn)
  · have hm : u∈originalMiddle A := by
      apply universal_endpoint_core_le_middle h true
      have hh := hu.1
      change u∈(MulAction.stabilizer (A).Universal (base F true)).pCoreIn 2 at hh
      rwa [Subgroup.CosetGeometry.stabilizer_base] at hh
    have hne := source_six_reflection_root_ne_twist_of_unchanged_other c d.reflection
      d.fixes d.moves d.squares d.normalizes h d'.reflection d'.fixes d'.moves d'.squares
      d'.normalizes d'.transitive d'.thick d'.odd true hother u hm hf
    exact (hne he.symm).elim
end Geometry

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR


local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)
set_option maxHeartbeats 800000 in
/-- The original source identifies the corrected eight-root itself, with
no complement-classification or root-alternatives premise. -/
theorem source_reflected_root_equality
    (c:CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) : HasReflectedRootEquality c := by
  exact assemble (L := Lₛ) (S := Sₛ)
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap c
    (SourceReflectedRootConjugacy.source_reflected_root_conjugacy hG T hempty hM hu hmany hcard e H hH eR c)
    (SourceRootFixedConjugator.source_root_fixed_conjugators hG T hempty hM hu hmany hcard e H hH eR c)
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceReflectedRootEquality
