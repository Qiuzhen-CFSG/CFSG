module
public import Theory.SpecificGroups.Alternating.SevenThreeSection
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Two-core containment for a binary-three subgroup in an A₇ extension

If L ≤ I, L/O₂(L) is SL₃(2), and I/O₂(I) is A₇, then O₂(L) ≤ O₂(I).
Restrict the actual quotient map of I to L. Its two-group kernel and the
order-168 quotient force the image two-core to vanish, retaining the literal
inclusions rather than replacing either group by its abstract quotient.

Source application: Aschbacher--Smith 10.2.9, cases (b) and (b1), pp.751--752.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups

namespace alternatingGroup.SevenThreeSection
variable {G : Type*} [Group G] [Finite G]

/-- The embedded two-core of L lies in that of I under the two actual quotient markings. -/
theorem twoCoreIn_le_of_quotient_equivs (L I : Subgroup G) (hLI : L ≤ I)
    (e : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (E : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    L.pCoreIn 2 ≤ I.pCoreIn 2 := by
  let A := L.subgroupOf I
  let a : A ≃* L := subgroupOfEquivOfLe hLI
  let eA : (A ⧸ pCore 2 A) ≃* SL(3,ZMod 2) :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  let f := E.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hk : IsPGroup 2 (f.subgroupMap A).ker := by
    let j : (f.subgroupMap A).ker →* pCore 2 I :=
      (A.subtype.comp (f.subgroupMap A).ker.subtype).codRestrict _ (fun x => by
        apply (QuotientGroup.eq_one_iff _).mp
        apply E.map_eq_one_iff.mp
        exact congrArg Subtype.val x.property)
    exact pCore_isPGroup.of_injective j (fun x z h => Subtype.ext (Subtype.ext
      (congrArg (fun k : pCore 2 I => (k : I)) h)))
  have hker := (image_twoCore_eq_bot_and_ker_eq f A hk eA).2
  intro x hx
  obtain ⟨l,hl,rfl⟩ := hx
  have ha : a.symm l ∈ pCore 2 A := by
    rw [←pCore_map_iso 2 a] at hl
    exact (mem_map_equiv).mp hl
  have hz : f (a.symm l : I) = 1 :=
    congrArg Subtype.val (show a.symm l ∈ (f.subgroupMap A).ker from hker.symm ▸ ha)
  exact mem_map_of_mem I.subtype ((QuotientGroup.eq_one_iff _).mp (E.map_eq_one_iff.mp hz))
end alternatingGroup.SevenThreeSection
