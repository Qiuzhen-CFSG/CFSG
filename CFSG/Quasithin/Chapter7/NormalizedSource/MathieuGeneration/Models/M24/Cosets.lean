module
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.Coverage
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.Native
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.Words

/-!
# Native M₂₄ Cartan cosets

The six exceptional Sylow double cosets occupy thirteen left Sylow cosets.
Short transition words certify that left multiplication by each marked Sylow
generator preserves this cover. Positive closure induction and an injective
encoding bound every subgroup contained in these double cosets by 13·1024.

Source: Aschbacher--Smith, Definition E.3.37 and Table 7.3.4,
printed pp.239 and 699. Used to exclude the native Mathieu Cartan witnesses.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24Cartan
open Subgroup Sporadic.Mathieu M24LocalGeometry
open SylowNormalizer PairOvergroups.Placement.TransitiveCoverage

private def coverBase : Fin 13 → Fin 510 := ![0,3,3,3,3,15,15,16,16,32,32,150,150]
private def coverWord : Fin 13 → List (Fin 4) := ![[],[],[0],[1],[3],[],[0],[],[1],[],[0],[],[0]]
private def coverTarget : Fin 4 → Fin 13 → Fin 13 := ![![0,2,1,4,3,6,5,7,8,10,9,12,11],![0,3,4,1,2,5,6,8,7,9,10,11,12],![0,1,2,3,4,5,6,7,8,10,9,11,12],![0,4,3,2,1,6,5,8,7,9,10,11,12]]
private def coverTransitionWord : Fin 4 → Fin 13 → List (Fin 4) := ![![[0],[],[0,2,1,2,0,0,1,0],[0,2,3,2,0,1,0],[0,1,0,2,3,0],[],[0,3,1,2,3,1,0,0,0],[0,3,0,3,0],[3,0,1,0,0,0],[],[3,0,0,1],[],[2,1,2,1,0,0]],![[1],[],[2,0,3,0,3],[],[0,2,1,0,1],[3,2,1,2,3],[0,0,0,1,0],[],[],[1],[0,2,1,2,0,0,1,0],[1],[0,2,3,0,2,3]],![[2],[2,3,1,2,3,1],[0,2,0,0,0],[1,0,0,1,0,0],[3,2,1,2,3,1],[3,2,3,1,2,1],[1,0,2,0,0,0,1],[2,1,2,1],[2],[1,0,3,1,2],[2,0,1,0,3,1,0],[2,1,0,0,1,0,0],[0,3,1,2,3,1,0]],![[3],[],[2,0,3,0,3],[0,2,1,0,1],[],[3,1,2,1,0],[3,2,0,3,0,3,0],[2,3,1,2],[2,3,1,2],[3],[0,2,1,2,1,0],[3,1],[0,0,0,3,0]]]

private noncomputable def coverRep (j : Fin 13) : M24 :=
  OrderEnumeration.evaluate (coverWord j) * representative (coverBase j)
private def coverPoint (j : Fin 13) (x : Fin 24) : Fin 24 :=
  evaluatePoint (coverWord j) (representativePerm (coverBase j) x)
private theorem coverRep_apply (j : Fin 13) (x : Fin 24) :
    (coverRep j).val x = coverPoint j x := by
  change (OrderEnumeration.evaluate (coverWord j)).val
    (representativePerm (coverBase j) x) = _
  rw [OrderEnumeration.evaluate_apply]
  rfl

private theorem cover_transition (a : Fin 4) (j : Fin 13) :
    generator a * coverRep j =
      coverRep (coverTarget a j) * OrderEnumeration.evaluate (coverTransitionWord a j) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change generatorPerm a ((coverRep j).val x) =
    (coverRep (coverTarget a j)).val ((OrderEnumeration.evaluate (coverTransitionWord a j)).val x)
  rw [generatorPerm_apply, coverRep_apply, coverRep_apply, OrderEnumeration.evaluate_apply]
  exact (by decide +kernel : ∀ a j x,
    generatorPoint a (coverPoint j x) =
      coverPoint (coverTarget a j) (evaluatePoint (coverTransitionWord a j) x)) a j x

private theorem cover_left (s : candidate) (j : Fin 13) :
    ∃ k : Fin 13, ∃ t : candidate, (s : M24) * coverRep j = coverRep k * t := by
  have hs : (s : M24) ∈ Submonoid.closure (Set.range generator) := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact s.property
  have hall : ∀ j : Fin 13, ∃ k : Fin 13, ∃ t : candidate,
      (s : M24) * coverRep j = coverRep k * t := by
    refine Submonoid.closure_induction_left
      (motive := fun y _ => ∀ j : Fin 13, ∃ k : Fin 13, ∃ t : candidate,
        y * coverRep j = coverRep k * t) ?_ ?_ hs
    · intro j
      exact ⟨j, 1, by simp⟩
    · intro a ha y _ ih j
      obtain ⟨a, rfl⟩ := ha
      obtain ⟨k, t, ht⟩ := ih j
      refine ⟨coverTarget a k,
        ⟨OrderEnumeration.evaluate (coverTransitionWord a k),
          OrderEnumeration.evaluate_mem _⟩ * t, ?_⟩
      change (generator a * y) * coverRep j =
        coverRep (coverTarget a k) * (OrderEnumeration.evaluate (coverTransitionWord a k) * t)
      rw [mul_assoc, ht, ← mul_assoc, cover_transition, mul_assoc]
  exact hall j

private theorem exceptional_cover (i : Fin 510)
    (hi : i = 0 ∨ i = 3 ∨ i = 15 ∨ i = 16 ∨ i = 32 ∨ i = 150) :
    ∃ j : Fin 13, coverRep j = representative i := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [coverRep_apply]
    rfl
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [coverRep_apply]
    rfl
  · refine ⟨5, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [coverRep_apply]
    rfl
  · refine ⟨7, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [coverRep_apply]
    rfl
  · refine ⟨9, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [coverRep_apply]
    rfl
  · refine ⟨11, ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [coverRep_apply]
    rfl

private theorem native_representative_mem (H : Subgroup M24) (hS : candidate ≤ H)
    (g : H) (i : Fin 510) (s t : candidate)
    (he : s.val.val * representativePerm i * t.val.val = g.val.val) :
    representativePerm i ∈ H.map M24.subtype := by
  have h := (H.map M24.subtype).mul_mem
    ((H.map M24.subtype).mul_mem
      ((H.map M24.subtype).inv_mem (Subgroup.mem_map_of_mem _ (hS s.property)))
      (Subgroup.mem_map_of_mem _ g.property))
    ((H.map M24.subtype).inv_mem (Subgroup.mem_map_of_mem _ (hS t.property)))
  change s.val.val⁻¹ * g.val.val * t.val.val⁻¹ ∈ H.map M24.subtype at h
  rw [← he] at h
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h

private theorem card_le_of_cover {G : Type*} [Group G] [Finite G]
    (L H : Subgroup G) {n : ℕ} (r : Fin n → G)
    (hall : ∀ g : H, ∃ k : Fin n, ∃ s : L, g.val = r k * s) :
    Nat.card H ≤ n * Nat.card L := by
  classical
  choose k s he using hall
  let f : H → Fin n × L := fun g => (k g, s g)
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    rw [he x, he y]
    exact congrArg (fun js : Fin n × L => r js.1 * js.2) h
  simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- The six possible exceptional double cosets occupy only thirteen Sylow cosets. -/
theorem exceptional_card_bound (H : Subgroup M24) (hS : candidate ≤ H)
    (hrep : ∀ i : Fin 510, representativePerm i ∈ H.map M24.subtype →
      i = 0 ∨ i = 3 ∨ i = 15 ∨ i = 16 ∨ i = 32 ∨ i = 150) :
    Nat.card H ≤ 13312 := by
  classical
  have hall (g : H) : ∃ k : Fin 13, ∃ s : candidate, g.val = coverRep k * s := by
    obtain ⟨i, s, t, he⟩ := covers g.val
    obtain ⟨j, hj⟩ := exceptional_cover i (hrep i (native_representative_mem H hS g i s t he))
    obtain ⟨k, u, hu⟩ := cover_left s j
    refine ⟨k, u * t, ?_⟩
    have hn : s.val * representative i * t.val = g.val := Subtype.ext he
    rw [← hn, ← hj, hu]
    exact mul_assoc _ _ _
  simpa only [candidate_card] using card_le_of_cover candidate H coverRep hall

/-- If only the identity double coset remains, the overgroup is the Sylow subgroup. -/
theorem identity_card_bound (H : Subgroup M24) (hS : candidate ≤ H)
    (hrep : ∀ i : Fin 510, representativePerm i ∈ H.map M24.subtype → i = 0) :
    Nat.card H ≤ 1024 := by
  have hle : H ≤ candidate := by
    intro g hg
    obtain ⟨i, s, t, he⟩ := covers g
    have hi := hrep i (native_representative_mem H hS ⟨g, hg⟩ i s t he)
    subst i
    have hn : s.val * representative 0 * t.val = g := Subtype.ext he
    have hzero : representative 0 = 1 := by apply Subtype.ext; decide +kernel
    rw [hzero, mul_one] at hn
    exact hn ▸ candidate.mul_mem s.property t.property
  simpa only [candidate_card] using Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24Cartan
