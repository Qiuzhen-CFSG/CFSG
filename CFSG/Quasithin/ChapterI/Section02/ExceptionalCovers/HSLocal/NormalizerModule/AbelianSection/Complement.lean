module
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.Coprime

/-!
# The marked displacement factor of the HS covering core

A complement to the central kernel maps isomorphically onto the model core.
The equivalence is induced by the original localMap, with its formula
retained for Frattini and action transport.
Source: Aschbacher–Smith I.2.2(5), p.412 / PDF p.423.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Sporadic.LeechRelated.HS.BlockNormalizer
variable {K : Type*} [Group K] [Finite K]

theorem complement_map_localMap
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) :
    D.map (localMap e) = pCore 2 baseNormalizer := by
  have hz : (centralFactor e).map (localMap e) = ⊥ := by
    change ((center K).subgroupOf (M e)).map (localMap e) = ⊥
    rw [← localMap_ker, map_ker_self]
  rw [← Q_map_localMap e hZ, hsplit, Subgroup.map_sup, hz, sup_bot_eq]

/-- The restriction uses the original covering map, rather than an unmarked
isomorphism with another group of order 64. -/
def complementModelMap
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) : D →* pCore 2 baseNormalizer :=
  ((localMap e).comp D.subtype).codRestrict _ (fun d => by
    rw [← complement_map_localMap e hZ D hsplit]
    exact mem_map_of_mem _ d.property)

theorem complementModelMap_bijective
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) (hd : Disjoint D (centralFactor e)) :
    Function.Bijective (complementModelMap e hZ D hsplit) := by
  constructor
  · apply (complementModelMap e hZ D hsplit).ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro d hdker
    apply Subtype.ext
    apply disjoint_def.mp hd d.property
    change (d : M e) ∈ (center K).subgroupOf (M e)
    rw [← localMap_ker]
    exact congrArg Subtype.val hdker
  · intro a
    have ha : (a : baseNormalizer) ∈ D.map (localMap e) := by
      rw [complement_map_localMap e hZ D hsplit]
      exact a.property
    obtain ⟨d, hd, hda⟩ := ha
    exact ⟨⟨d, hd⟩, Subtype.ext hda⟩

noncomputable def complementModelEquiv
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) (hd : Disjoint D (centralFactor e)) :
    D ≃* pCore 2 baseNormalizer :=
  MulEquiv.ofBijective (complementModelMap e hZ D hsplit)
    (complementModelMap_bijective e hZ D hsplit hd)

theorem complementModelEquiv_apply
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (D : Subgroup (M e))
    (hsplit : Q e = D ⊔ centralFactor e) (hd : Disjoint D (centralFactor e)) (d : D) :
    (complementModelEquiv e hZ D hsplit hd d : baseNormalizer) = localMap e d := rfl

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
