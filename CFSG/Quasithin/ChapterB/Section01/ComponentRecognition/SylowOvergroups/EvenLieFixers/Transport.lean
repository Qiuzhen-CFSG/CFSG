module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Reduction

/-!
# Transport of the intrinsic Sylow fixer bound

An actual group equivalence conjugates the automorphism action and maps a
Sylow subgroup onto a Sylow subgroup. Restricting this conjugation gives an
injection between their pointwise fixers. The final application uses the
literal central quotient of a component and its literal conjugation action.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74 of `refs/quasithin.pdf`.
The perfect-central-cover step is supplied by `Reduction`; no assertion that
the component's Sylow centralizer has trivial odd central factor is needed.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers
open Subgroup Theory.GroupTheory
variable {G L B : Type*} [Group G] [Group L] [Group B]

/-- Transport the entire fixer, without a restriction on automorphism order. -/
theorem fixer_of_equiv [Finite L] (e : L ≃* B) (hB : SylowFixerIsTwoGroup B) :
    SylowFixerIsTwoGroup L := by
  intro S
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let F := fixingSubgroup (MulAut L) (S : Set L)
  let D := fixingSubgroup (MulAut B) (Q : Set B)
  let j : F →* D := ((MulAut.congr e).toMonoidHom.comp F.subtype).codRestrict D (by
    intro a
    apply (mem_fixingSubgroup_iff _).mpr
    rintro y ⟨x, hx, rfl⟩
    change e (a.val (e.symm (e x))) = e x
    rw [e.symm_apply_apply]
    exact congrArg e ((mem_fixingSubgroup_iff _).mp a.property x hx))
  exact (hB Q).of_injective j (fun a b h =>
    Subtype.ext ((MulAut.congr e).injective (congrArg Subtype.val h)))

/-- A concrete quotient-model calculation rules out the centralizing branch
of B.1.13's local alternative. Recognition and the alternative remain source inputs. -/
theorem le_component_of_quotient_model [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G))
    (e : L ⧸ center L ≃* B) (hB : SylowFixerIsTwoGroup B)
    (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥) : K ≤ L := by
  let := hL.2
  exact le_component_of_local_dichotomy K L T hL hLK hkind hKN hd
    (fixer_twoGroup_of_centralQuotient e hB)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers
