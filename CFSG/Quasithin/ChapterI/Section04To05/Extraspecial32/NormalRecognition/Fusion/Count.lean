module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Defs
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.LocalOrbit

/-!
# Assembly of the ambient fusion count from the local involution orbit

The common-centralizer bound places every noncentral core conjugate of z
in `FusionCount.countCandidates z`. The original failure of weak closure
supplies one such conjugate. If H is transitive on these candidates, all of
them are ambient conjugates, so the literal fusion set is precisely the
candidates together with z. Six candidates therefore give seven conjugates.

Relative quaternion normality supplies both local action premises through
the actual H/Q action on the two quaternion quotient planes. The final
theorem discharges these premises and proves the seven-conjugate count
from the original hypotheses and normality inside H alone.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 31–47, Lemmas 2.3(2)(b) and 2.7(1).
-/

namespace CFSG.Quasithin.Extraspecial32.Hypotheses

open Subgroup FusionCount

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Transitivity on the purely local candidates determines the complete
ambient fusion set, using the source's failure of weak closure. -/
public theorem fusion_set_eq_insert_countCandidates_of_transitive (h : Hypotheses z)
    (ht : ∀ x ∈ countCandidates z, ∀ y ∈ countCandidates z,
      ∃ a ∈ Centralizer z, a * x * a⁻¹ = y) :
    {x : G | x ∈ coreInG z ∧ IsConj z x} = insert z (countCandidates z) := by
  obtain ⟨g, hgQ, hgz⟩ := h.fused
  have hgf : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  have hgs := h.mem_countCandidates_of_isConj hgQ hgf hgz
  ext x
  constructor
  · rintro ⟨hx, hf⟩
    by_cases he : x = z
    · exact Set.mem_insert_iff.mpr (Or.inl he)
    · exact Set.mem_insert_of_mem z (h.mem_countCandidates_of_isConj hx hf he)
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨h.involution_mem_coreInG, IsConj.refl _⟩
    · obtain ⟨a, _, ha⟩ := ht _ hgs x hx
      exact ⟨hx.1, hgf.trans (isConj_iff.mpr ⟨a, ha⟩)⟩

/-- The remaining local orbit calculation supplies the desired ambient
count. Its two premises are discharged by the normal-quaternion action. -/
public theorem fusion_conjugates_card_of_countCandidates (h : Hypotheses z)
    (hc : (countCandidates z).ncard = 6)
    (ht : ∀ x ∈ countCandidates z, ∀ y ∈ countCandidates z,
      ∃ a ∈ Centralizer z, a * x * a⁻¹ = y) :
    Nat.card {x : G // x ∈ coreInG z ∧ IsConj z x} = 7 := by
  change ({x : G | x ∈ coreInG z ∧ IsConj z x} : Set G).ncard = 7
  rw [h.fusion_set_eq_insert_countCandidates_of_transitive ht,
    Set.ncard_insert_of_notMem (fun hz => hz.2.2.1 rfl), hc]

/-- In the normal-quaternion branch, exactly seven elements of the core are
ambient conjugates of z, as in Aschbacher's Lemma 2.7(1). -/
public theorem fusion_conjugates_card_of_quaternion_normal (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) :
    Nat.card {x : G // x ∈ coreInG z ∧ IsConj z x} = 7 :=
  h.fusion_conjugates_card_of_countCandidates
    (h.countCandidates_card_of_quaternion_normal hn)
    (h.countCandidates_transitive_of_quaternion_normal hn)

end CFSG.Quasithin.Extraspecial32.Hypotheses
