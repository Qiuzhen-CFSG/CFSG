module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Thompson

public import Theory.GroupTheory.CentralizerRelativeIndex

/-!
# Ambient centralizer Sylows on the original plane-core center

The proved identity J(T)=Z(O₂(L)) puts a Sylow subgroup of each point
centralizer inside N_G(L). Its local centralizer therefore has odd relative
index in the full ambient centralizer and the same two-part. Burnside fusion
also identifies ambient conjugacy with conjugacy inside this normalizer.

The marked companion transports these conclusions to the same published
extension. These are inputs to F.4.37–40, not the full F.4.42 centralizer equality.
Source: Aschbacher–Smith F.4.35–40, printed pp.292–294.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- A full ambient centralizer Sylow lies in the original plane normalizer. -/
theorem Preparation.unitaryFive_plane_center_centralizer_sylow
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (x : G) (hx : x ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype) :
    ∃ P : Sylow 2 (centralizer ({x} : Set G)),
      (P : Subgroup (centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype ≤
        normalizer (L : Set G) := by
  have hJ := d.unitaryFive_thompson h hH hp U hc
  let Z := (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype
  let : IsElementaryAbelian 2 Z :=
    ((d.unitaryFive_plane_core_structure h hH hp U hc).2.1).map (L.pCoreIn 2).subtype
  have hxc : x ∈ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [hJ]
    exact Z.le_centralizer hx
  have he := exists_centralizer_sylow_le_maxJ_normalizer T x hxc
  rwa [d.unitaryFive_thompson_normalizer h hH hp U hc] at he

/-- The actual local centralizer has odd index in the ambient centralizer. -/
theorem Preparation.unitaryFive_plane_center_centralizer_odd_index
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (x : G) (hx : x ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype) :
    Odd ((normalizer (L : Set G) ⊓ centralizer ({x} : Set G)).relIndex
      (centralizer ({x} : Set G))) := by
  let M := normalizer (L : Set G)
  let C := centralizer ({x} : Set G)
  obtain ⟨P,hP⟩ := d.unitaryFive_plane_center_centralizer_sylow h hH hp U hc x hx
  have hle : (P : Subgroup C) ≤ (M ⊓ C).subgroupOf C := fun y hy =>
    ⟨hP (mem_map_of_mem C.subtype hy),y.property⟩
  exact Nat.not_even_iff_odd.mp (fun he =>
    P.not_dvd_index (he.two_dvd.trans (index_dvd_of_le hle)))


/-- The ambient centralizer of each element of the plane-core center has
exactly the same two-part as its centralizer inside the full plane normalizer. -/
theorem Preparation.unitaryFive_plane_center_centralizer_two_part
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (x : normalizer (L : Set G))
    (hx : x.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype) :
    (Nat.card (centralizer ({x.val} : Set G))).factorization 2 =
      (Nat.card (centralizer ({x} : Set (normalizer (L : Set G))))).factorization 2 := by
  exact CentralizerRelativeIndex.factorization_eq_of_not_dvd_relIndex _ x 2
    (d.unitaryFive_plane_center_centralizer_odd_index h hH hp U hc x hx).not_two_dvd_nat

/-- Ambient fusion on the original plane-core center is exactly fusion
inside its full normalizer, expressed on the literal subgroup elements. -/
theorem Preparation.unitaryFive_plane_center_local_fusion
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (x y : normalizer (L : Set G))
    (hx : x.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype)
    (hy : y.val ∈ (center (L.pCoreIn 2)).map (L.pCoreIn 2).subtype) :
    IsConj x.val y.val ↔ IsConj x y := by
  constructor
  · intro hxy
    obtain ⟨g,hg,he⟩ := d.unitaryFive_plane_center_fusion h hH hp U hc hx hy hxy
    exact isConj_iff.mpr ⟨⟨g,hg⟩,Subtype.ext he⟩
  · exact (normalizer (L : Set G)).subtype.map_isConj

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
