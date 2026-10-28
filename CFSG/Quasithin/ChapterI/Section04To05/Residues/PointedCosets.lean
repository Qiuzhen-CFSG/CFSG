module

public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SourceGeometry

/-!
# Individual types in the original residues

The cosets of an intrinsic pair stabilizer correspond to the original
ambient cosets incident with the base vertex. The correspondence retains
the literal ambient representative, the action and pairwise incidence.
This is the individual-type form of I.5.3(3), used to attach the concrete
Fano and polar point/line coordinates without replacing any coset space.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.DSystem
open Subgroup
variable {G : Type*} [Group G] {D : Diagram} (S : DSystem D G)

def pointedCosetMap (i j : Fin 3) (hji : j ≠ i)
    (q : S.family i ⧸ localParabolic S.family i j) :
    {x : G ⧸ S.family j // S.Inc ((1 : G) : G ⧸ S.family i) x} := by
  refine ⟨CosetGeometry.intrinsicCosetMap S.family i ⟨j, hji⟩ q, ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨a.val, ?_, rfl⟩
  apply QuotientGroup.eq.mpr
  simpa only [inv_mul_cancel_right, mul_one] using (S.family i).inv_mem a.property

theorem pointedCosetMap_injective (i j : Fin 3) (hji : j ≠ i) :
    Function.Injective (S.pointedCosetMap i j hji) := by
  intro a b h
  exact CosetGeometry.intrinsicCosetMap_injective S.family i ⟨j, hji⟩
    (congrArg Subtype.val h)

theorem pointedCosetMap_surjective (i j : Fin 3) (hji : j ≠ i) :
    Function.Surjective (S.pointedCosetMap i j hji) := by
  intro x
  obtain ⟨g, hg, hq⟩ := (CosetGeometry.incident_base_iff S.family i ⟨j, x.val⟩).mp x.property
  exact ⟨((⟨g, hg⟩ : S.family i) : S.family i ⧸ localParabolic S.family i j),
    Subtype.ext hq⟩

def pointedCosetEquiv (i j : Fin 3) (hji : j ≠ i) :
    (S.family i ⧸ localParabolic S.family i j) ≃
      {x : G ⧸ S.family j // S.Inc ((1 : G) : G ⧸ S.family i) x} :=
  Equiv.ofBijective (S.pointedCosetMap i j hji)
    ⟨S.pointedCosetMap_injective i j hji, S.pointedCosetMap_surjective i j hji⟩

theorem pointedCosetEquiv_mk (i j : Fin 3) (hji : j ≠ i) (a : S.family i) :
    (S.pointedCosetEquiv i j hji (a : S.family i ⧸ localParabolic S.family i j)).val =
      (a.val : G ⧸ S.family j) := rfl

theorem pointedCosetEquiv_smul (i j : Fin 3) (hji : j ≠ i) (a : S.family i)
    (q : S.family i ⧸ localParabolic S.family i j) :
    (S.pointedCosetEquiv i j hji (a • q)).val =
      a.val • (S.pointedCosetEquiv i j hji q).val := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
  rfl

theorem pointedCosetEquiv_incident (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i)
    (q : S.family i ⧸ localParabolic S.family i j)
    (r : S.family i ⧸ localParabolic S.family i k) :
    (∃ a : S.family i, (a : S.family i ⧸ localParabolic S.family i j) = q ∧
      (a : S.family i ⧸ localParabolic S.family i k) = r) ↔
    S.Inc (S.pointedCosetEquiv i j hji q).val (S.pointedCosetEquiv i k hki r).val := by
  exact (CosetGeometry.residueIntrinsicEquiv_incident_iff S.family i S.middleProduct
    ⟨⟨j, hji⟩, q⟩ ⟨⟨k, hki⟩, r⟩).symm

theorem pointedCoset_card (i j : Fin 3) (hji : j ≠ i) :
    Nat.card {x : G ⧸ S.family j // S.Inc ((1 : G) : G ⧸ S.family i) x} =
      (localParabolic S.family i j).index :=
  (Nat.card_congr (S.pointedCosetEquiv i j hji)).symm

end Quasithin.I5.DSystem
