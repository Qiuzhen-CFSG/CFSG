module

public import Theory.GroupTheory.DoubleCoverCentralizer.Basic

/-!
# Sylow containment for two-central elements

An element in the center of a Sylow two-subgroup has that whole Sylow
subgroup in its centralizer. Thus the centralizer has odd index. Both the
mark and the containment transport along an actual group isomorphism.

These elementary consequences of the definition support the centralizer-table
argument in Aschbacher–Smith, 16.3.11(3), printed p.1181.
-/

public section
namespace Theory.GroupTheory.DoubleCoverCentralizer
open Subgroup
variable {H S : Type*} [Group H] [Group S]

/-- A two-central element centralizes an entire Sylow two-subgroup. -/
theorem TwoCentral.exists_sylow_le_centralizer {u : H} (hu : TwoCentral u) :
    ∃ P : Sylow 2 H, (P : Subgroup H) ≤ centralizer ({u} : Set H) := by
  obtain ⟨P, huP, hc⟩ := hu
  refine ⟨P, fun x hx => mem_centralizer_singleton_iff.mpr ?_⟩
  exact congrArg Subtype.val (mem_center_iff.mp hc ⟨x, hx⟩)

/-- An actual group isomorphism preserves the two-central mark. -/
theorem TwoCentral.map [Finite H] (e : H ≃* S) {u : H} (hu : TwoCentral u) :
    TwoCentral (e u) := by
  obtain ⟨P, huP, hc⟩ := hu
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ⟨u, huP, rfl⟩, ?_⟩
  apply mem_center_iff.mpr
  intro x
  obtain ⟨v, hv, he⟩ := x.property
  apply Subtype.ext
  change (x : S) * e u = e u * (x : S)
  change e v = (x : S) at he
  rw [← he, ← e.map_mul, ← e.map_mul]
  exact congrArg e (congrArg Subtype.val (mem_center_iff.mp hc ⟨v, hv⟩))

/-- A two-central element has centralizer index indivisible by two. -/
theorem TwoCentral.not_dvd_centralizer_index [Finite H] {u : H} (hu : TwoCentral u) :
    ¬ 2 ∣ (centralizer ({u} : Set H)).index := by
  obtain ⟨P, hP⟩ := hu.exists_sylow_le_centralizer
  exact fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hP))

end Theory.GroupTheory.DoubleCoverCentralizer
