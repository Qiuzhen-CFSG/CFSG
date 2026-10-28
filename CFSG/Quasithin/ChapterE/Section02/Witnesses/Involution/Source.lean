module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.Basic
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreQuotient
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Solvable.Witness
import all CFSG.Quasithin.ChapterE.Section02.Witnesses.Solvable.Witness
/-!
# Lifting the order-two star branch to the original group

The image of O₂(M) lies in the two-core of its literal image. The star
quotient H/J has trivial two-core, so an image of V of order two admits
the genuine dihedral construction. The original pair lifting proof then
restores V, its internal conjugator and prescribed Sylow intersection,
and proves that the relative normal core is two-closed. No solvability
hypothesis on H or desired-witness premise is required.

The private lifting proof in the solvable implementation is deliberately
reused internally: that proof itself has no solvability assumption.
Source: Aschbacher–Smith, E.2.7–9, printed pp.218,221–222.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.Involution
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
private theorem map_core_le {A : Type*} [Group A] (f : H →* A) (M : Subgroup H) :
    (M.pCoreIn 2).map f ≤ (M.map f).pCoreIn 2 := by
  have hcore : (pCore 2 M).map (f.subgroupMap M) ≤ pCore 2 (M.map f) :=
    le_sSup ⟨Normal.map inferInstance _ (f.subgroupMap_surjective M),pCore_isPGroup.map _⟩
  calc
    _ = ((pCore 2 M).map (f.subgroupMap M)).map (M.map f).subtype := by
      rw [pCoreIn,map_map,map_map]
      rfl
    _ ≤ _ := map_mono hcore

/-- The original E.2.9 dihedral witness when the actual image of V in H/J has order two. -/
theorem source_star_order_two (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) = 2) :
    Nonempty (Solvable.Witness T (ChapterB.minimalParabolicMax T hP) V) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  have hq := QuotientGroup.mk'_surjective J
  have hk : q.ker ≤ J := by rw [QuotientGroup.ker_mk']
  let S := T.mapSurjective hq
  let B := M.map q
  let W := V.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  let hPs := ChapterB.minimalParabolic_surjective_core T hP q hq hk
  have hJs : ChapterB.minimalParabolicCore S hPs = ⊥ := by
    rw [← ChapterB.minimalParabolicCore_map_core T hP q hq hk]
    exact QuotientGroup.map_mk'_self J
  have hQs : pCore 2 (H ⧸ J) = ⊥ :=
    bot_unique (hJs ▸ ChapterB.minimalParabolicTwoCore_le_core S hPs)
  have hWcore : W ≤ B.pCoreIn 2 := (map_mono hVcore).trans (map_core_le q M)
  have hout : ¬ W ≤ pCore 2 (H ⧸ J) := by
    intro h
    have he : W = ⊥ := bot_unique (hQs ▸ h)
    have hc := Subgroup.card_eq_one.mpr he
    change Nat.card W = 2 at hcard
    omega
  obtain ⟨p,hp,hp2,⟨w⟩⟩ := exists_dihedral_of_card_two B W hWcore hcard hout
  exact Solvable.lift_witness T hP V hVT hn hVcore hp hp2 w
end CFSG.Quasithin.ChapterE.Witnesses.Involution
