module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionNineCubicStarGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Conditions
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.InitialAction

/-!
# The original seed orbit generates the full initial moved subgroup

In a cubic six-point MS pair, the initial moved action is Irr+. Any seed
inside the star module which the component moves has a normal closure with
the same component commutator as the full star module. This retains the
literal normal closure inside LR and its actual ambient embedding.

The `import all` is an intentional proof-level coupling to the existing
private Irr+ commutator lemma in InitialAction. Its private declaration is
used only in a proof; no private name enters either public statement, and
the existing owner remains unchanged.

This is an equality in the initial central layer. It does not identify that
layer's commutator with the whole intrinsic block core.

Source: Aschbacher--Smith C.1.31--32 and B.5.1; Meierfrankenfeld--Stellmacher
(1993), (3.2), printed pp.863--864.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Exceptional AlternatingSixReconstruction.Exceptional.Exhaustion
variable {G : Type*} [Group G] [Finite G] {L R : Subgroup G}

/-- Every moved seed in the actual star module has the full initial
component commutator after normal closure inside the original LR. -/
theorem smallMS_cubic_seed_normalClosure_moved_eq
    (hms : SmallMSPair KnownSimple.IsKnownSimple L R)
    (t : (L ⧸ centralPreimage (pCore 2 L)) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (A : Subgroup G) (hA : A ≤ (starV L R).map (L ⊔ R : Subgroup G).subtype)
    (hmove : ⁅A,L⁆ ≠ ⊥) :
    ⁅normalClosure (A.subgroupOf (L ⊔ R) : Set (L ⊔ R : Subgroup G)),
      L.subgroupOf (L ⊔ R)⁆ = ⁅starV L R,L.subgroupOf (L ⊔ R)⁆ := by
  let H := L ⊔ R
  let K := L.subgroupOf H
  let X := centralOmega L R
  let Z := normalClosure (A.subgroupOf H : Set H)
  let := hms.relative_normal
  have hAH : A ≤ H := hA.trans (map_subtype_le _)
  have hAX : A.subgroupOf H ≤ X := by
    intro a ha
    obtain ⟨x,hx,he⟩ := hA ha
    exact H.subtype_injective he ▸ hx
  have hZX : Z ≤ X := normalClosure_le_normal hAX
  have hne : ¬ K ≤ centralizer (Z : Set H) := by
    intro hc
    apply hmove
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro a ha l hl
    have hh := (le_centralizer_iff.mp hc)
      (show (⟨a,hAH ha⟩ : H) ∈ Z from le_normalClosure ha)
      (⟨l,mem_sup_left hl⟩ : H) hl
    exact congrArg H.subtype hh
  let e : CentralMarking L := t.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm
  exact moved_commutator_eq_of_irrPlus X Z K
    (QuotientGroup.mk' (layerKernel L R)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hZX hms.relative_twoPerfect hne
    (layer_moved_irrPlus hms e hz)

/-- The same initial moved equality after the literal embedding of LR in G. -/
theorem smallMS_cubic_seed_normalClosure_moved_eq_map
    (hms : SmallMSPair KnownSimple.IsKnownSimple L R)
    (t : (L ⧸ centralPreimage (pCore 2 L)) ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (A : Subgroup G) (hA : A ≤ (starV L R).map (L ⊔ R : Subgroup G).subtype)
    (hmove : ⁅A,L⁆ ≠ ⊥) :
    ⁅(normalClosure (A.subgroupOf (L ⊔ R) : Set (L ⊔ R : Subgroup G))).map
        (L ⊔ R : Subgroup G).subtype,L⁆ =
      ⁅(starV L R).map (L ⊔ R : Subgroup G).subtype,L⁆ := by
  have he := congrArg (Subgroup.map (L ⊔ R : Subgroup G).subtype)
    (smallMS_cubic_seed_normalClosure_moved_eq hms t hz A hA hmove)
  simpa only [map_commutator,map_subgroupOf_eq_of_le (show L ≤ L ⊔ R from le_sup_left)] using he

end CFSG.Quasithin.Chapter15.Section01
