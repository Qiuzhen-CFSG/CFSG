module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.ParabolicCover
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.Head

/-!
# The full cubic-root actor family in ambient triality

Transport the automorphism orbit of the actual elementary subgroup
(t,0,0;u,v) through a normal model copy. Every actor has order 2^(5f),
and ambient conjugation preserves the family without any splitting assumption.
The seed belongs to the prescribed Sylow subgroup after model alignment.

This constructs actors only. Weak-closure geometry and local subgroup
confinement are separate obligations for E.1.14(2).
Source: Aschbacher--Smith E.1.5 and E.1.14(2), printed pp.210 and 214,
citing Asc82a, GF(2)-representations of finite groups, Lemma 4.7.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

variable {G : Type*} [Group G] {f : ℕ} {hf : 0 < f}

def headFamily (f : ℕ) (hf : 0 < f) : Set (Subgroup (BinaryCarrier f hf)) :=
  {A | ∃ β : MulAut (BinaryCarrier f hf),
    A = (headSubgroup (binaryParameters f hf) rfl).map β.toMonoidHom}

theorem headSubgroup_mem : headSubgroup (binaryParameters f hf) rfl ∈ headFamily f hf := by
  refine ⟨MulEquiv.refl _, ?_⟩
  exact (Subgroup.map_id _).symm

theorem headFamily_map (β : MulAut (BinaryCarrier f hf))
    {A : Subgroup (BinaryCarrier f hf)} (hA : A ∈ headFamily f hf) :
    A.map β.toMonoidHom ∈ headFamily f hf := by
  obtain ⟨α, rfl⟩ := hA
  exact ⟨α.trans β, Subgroup.map_map _ _ _⟩

theorem headFamily_elementary {A : Subgroup (BinaryCarrier f hf)}
    (hA : A ∈ headFamily f hf) : IsElementaryAbelian 2 A := by
  obtain ⟨β, rfl⟩ := hA
  let _ := headSubgroup_elementary (binaryParameters f hf) rfl
  exact IsElementaryAbelian.map _

theorem headFamily_card {A : Subgroup (BinaryCarrier f hf)}
    (hA : A ∈ headFamily f hf) : Nat.card A = 2 ^ (5 * f) := by
  obtain ⟨β, rfl⟩ := hA
  rw [Subgroup.card_map_of_injective β.injective]
  exact (card_headSubgroup (binaryParameters f hf) rfl).trans (by
    rw [binaryParameters_q, ← pow_mul, Nat.mul_comm f 5])

def ambientHeadFamily (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) :
    Set (Subgroup G) :=
  {A | ∃ B ∈ headFamily f hf, A = B.map (modelEmbedding L e)}

theorem ambientHeadFamily_le {L : Subgroup G} {e : L ≃* BinaryCarrier f hf}
    {A : Subgroup G} (hA : A ∈ ambientHeadFamily L e) : A ≤ L := by
  obtain ⟨B, _, rfl⟩ := hA
  exact (Subgroup.map_le_range _ _).trans_eq (modelEmbedding_range L e)

theorem ambientHeadFamily_card {L : Subgroup G} {e : L ≃* BinaryCarrier f hf}
    {A : Subgroup G} (hA : A ∈ ambientHeadFamily L e) :
    Nat.card A = 2 ^ (5 * f) := by
  obtain ⟨B, hB, rfl⟩ := hA
  rw [Subgroup.card_map_of_injective (modelEmbedding_injective L e)]
  exact headFamily_card hB

theorem ambientHeadFamily_elementary (L : Subgroup G) [L.Normal]
    (e : L ≃* BinaryCarrier f hf) : IsElementaryFamily (ambientHeadFamily L e) := by
  constructor
  · rintro A ⟨B, hB, rfl⟩
    let _ := headFamily_elementary hB
    exact IsElementaryAbelian.map _
  · rintro g A ⟨B, hB, rfl⟩
    let β : MulAut (BinaryCarrier f hf) :=
      (e.symm.trans (MulAut.conjNormal (H := L) g)).trans e
    refine ⟨B.map β.toMonoidHom, headFamily_map β hB, ?_⟩
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    change g * (e.symm x : G) * g⁻¹ =
      (e.symm (e ((MulAut.conjNormal (H := L) g) (e.symm x))) : G)
    rw [e.symm_apply_apply]
    rfl

theorem ambientHeadFamily_nonempty (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) :
    (ambientHeadFamily L e).Nonempty :=
  ⟨(headSubgroup (binaryParameters f hf) rfl).map (modelEmbedding L e),
    headSubgroup (binaryParameters f hf) rfl, headSubgroup_mem, rfl⟩

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
