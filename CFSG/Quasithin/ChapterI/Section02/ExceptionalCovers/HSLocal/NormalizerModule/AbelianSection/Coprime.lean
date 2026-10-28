module
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.Incidence
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.MarkedInternalProduct

/-!
# The coprime decomposition of the abelian HS covering core

Lift a Sylow-seven subgroup through the literal localMap. A fixed-free model
core makes its cover centralizer exactly the relatively embedded Z(K).
The standard coprime-action theorems then give the join, disjointness, and
an actual direct-product equivalence.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, p.412 / PDF p.423.
The abelianness hypothesis is discharged by Incidence in the assembly module.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Sporadic.LeechRelated.HS.BlockNormalizer
variable {K : Type*} [Group K]

/-- Z(K) embedded in the actual normalizer preimage. -/
def centralFactor (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Subgroup (M e) := (center K).subgroupOf (M e)

theorem centralFactor_le_center
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    centralFactor e ≤ center (M e) := by
  intro z hz
  apply mem_center_iff.mpr
  intro m
  apply Subtype.ext
  exact mem_center_iff.mp hz m

theorem Q_inf_centralizer_eq_centralFactor [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (Y : Subgroup (M e))
    (hfree : pCore 2 baseNormalizer ⊓ centralizer (Y.map (localMap e) : Set baseNormalizer) = ⊥) :
    Q e ⊓ centralizer (Y : Set (M e)) = centralFactor e := by
  apply le_antisymm
  · rintro q ⟨hq, hc⟩
    have hm : localMap e q ∈ pCore 2 baseNormalizer ⊓
        centralizer (Y.map (localMap e) : Set baseNormalizer) := by
      refine ⟨?_, ?_⟩
      · change q ∈ (pCore 2 baseNormalizer).comap (localMap e)
        rwa [← Q_eq_model_core_preimage e hZ]
      · rintro y ⟨a, ha, rfl⟩
        simpa only [map_mul] using congrArg (localMap e) (hc a ha)
    rw [hfree, mem_bot] at hm
    change q ∈ (center K).subgroupOf (M e)
    rw [← localMap_ker]
    exact hm
  · exact le_inf (center_le_Q e hZ)
      ((centralFactor_le_center e).trans (center_le_centralizer _))

theorem Q_decomposition_of_model_seven [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) [IsMulCommutative (Q e)]
    (S : Sylow 7 baseNormalizer)
    (hfree : pCore 2 baseNormalizer ⊓ centralizer (S : Set baseNormalizer) = ⊥) :
    ∃ Y : Sylow 7 (M e),
      (Y : Subgroup (M e)).map (localMap e) = (S : Subgroup baseNormalizer) ∧
      Q e = ⁅Q e, (Y : Subgroup (M e))⁆ ⊔ centralFactor e ∧
      Disjoint ⁅Q e, (Y : Subgroup (M e))⁆ (centralFactor e) ∧
      Nonempty (Q e ≃* (↥⁅Q e, (Y : Subgroup (M e))⁆ × ↥(centralFactor e))) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨Y, hY⟩ := Sylow.mapSurjective_surjective (f := localMap e) (localMap_surjective e) 7 S
  have hmap : (Y : Subgroup (M e)).map (localMap e) = S :=
    congrArg (fun T : Sylow 7 baseNormalizer => (T : Subgroup baseNormalizer)) hY
  have hc : Q e ⊓ centralizer (Y : Set (M e)) = centralFactor e :=
    Q_inf_centralizer_eq_centralFactor e hZ Y (by rwa [hmap])
  have hnorm : (Y : Subgroup (M e)) ≤ normalizer (Q e : Set (M e)) := by
    rw [normalizer_eq_top]; exact le_top
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card (Q e)) :=
    IsPGroup.coprime_card_of_ne (G := M e) (G₂ := M e) 7 2 (by decide)
      (Y : Subgroup (M e)) (Q e) Y.isPGroup' (pCore_isPGroup (p := 2) (G := M e))
  have hs : Group.IsSolvable (Q e) := Group.isSolvable_of_comm fun x y => mul_comm x y
  have hsup : Q e = ⁅Q e, (Y : Subgroup (M e))⁆ ⊔
      (Q e ⊓ centralizer (Y : Set (M e))) :=
    eq_commutator_sup_centralizer_of_solvable_coprime (Q e) Y hnorm hs hcop
  rw [hc] at hsup
  have hd : Disjoint ⁅Q e, (Y : Subgroup (M e))⁆
      (Q e ⊓ centralizer (Y : Set (M e))) :=
    commutator_disjoint_centralizer_of_coprime (Q e) Y hnorm hcop
  rw [hc] at hd
  obtain ⟨f, _, _⟩ := exists_marked_internalProductEquiv (Q e) ⁅Q e, (Y : Subgroup (M e))⁆
    (centralFactor e) hsup.symm hd
    (le_centralizer_iff.mp ((centralFactor_le_center e).trans (center_le_centralizer _)))
  exact ⟨Y, hmap, hsup, hd, ⟨f⟩⟩

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
