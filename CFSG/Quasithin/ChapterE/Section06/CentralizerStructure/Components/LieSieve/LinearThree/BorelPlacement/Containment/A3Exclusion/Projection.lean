module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Containment.Construction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Transport

/-!
# The marked Borel projection with its exact central kernel

Restrict the central quotient map to the marked Sylow normalizer, then use
Sylow conjugacy in the actual PSL₃ model to identify its image with the
matrix Borel. The restriction is surjective and its kernel is precisely
the intersection with the component's center. The unipotent subgroup is
retained; the map does not quotient by the full two-core.

This construction permits a trivial covering center. It needs neither
Borel containment in M nor normalization of the component by the whole Q.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248, and its Borel paragraph on p.248.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment.A3Exclusion
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- Project the actual marked Borel onto its matrix model, retaining its exact kernel. -/
theorem exists_markedBorel_projection {n : ℕ} (hn : 0 < n)
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n)) (S : Sylow 2 L) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      ∃ f : markedBorel L S →* Matrix.PSL3.LinearThree.borel F,
        Function.Surjective f ∧
        f.ker = (center L).comap (inclusion (show markedBorel L S ≤ L from map_subtype_le _)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let N := normalizer (S : Set L)
  let P := S.mapSurjective (f := q) hq
  have hN : N.map q = normalizer (P : Set PSL(3,F)) := S.normalizer_map_surjective q hq
  let a := (MulEquiv.subgroupCongr hN).trans
    (Matrix.PSL3.CartanActions.BorelQuotient.sylowNormalizerEquiv F hn hF P)
  let b : N ≃* markedBorel L S := N.equivMapOfInjective L.subtype L.subtype_injective
  let r := q.subgroupMap N
  let f := a.toMonoidHom.comp (r.comp b.symm.toMonoidHom)
  refine ⟨F, inferInstance, inferInstance, hF, f,
    a.surjective.comp ((q.subgroupMap_surjective N).comp b.symm.surjective), ?_⟩
  ext x
  change f x = 1 ↔ _
  change a (r (b.symm x)) = 1 ↔ _
  rw [map_eq_one_iff a a.injective]
  change (⟨q (b.symm x), _⟩ : N.map q) = 1 ↔ _
  rw [Subtype.ext_iff]
  change e (QuotientGroup.mk' (center L) (b.symm x)) = 1 ↔ _
  rw [map_eq_one_iff e e.injective]
  have hb : (b.symm x : L) = inclusion (show markedBorel L S ≤ L from map_subtype_le _) x := by
    apply Subtype.ext
    exact congrArg (fun y : markedBorel L S => (y : G)) (b.apply_symm_apply x)
  exact (QuotientGroup.eq_one_iff (b.symm x : L)).trans (by rw [hb]; rfl)
end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment.A3Exclusion
