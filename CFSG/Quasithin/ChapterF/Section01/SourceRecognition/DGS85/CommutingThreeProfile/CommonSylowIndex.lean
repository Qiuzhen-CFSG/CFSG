module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SourceLayers
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Dihedral

/-!
# Core-intersection indices in the actual common Sylow

Project a common Sylow through the original/starred quotient marking. The
opposite core maps onto the entire quotient Sylow because the other core is
exactly the kernel. The kernel-index formula then computes the literal
core-intersection index, both in the reduced completion and after its original
inclusion. In the order-ten dihedral row this index is two.

The common-Sylow identity is the earlier source (12.1)(c), retained explicitly.
The dihedral specialization feeds `DihedralCoreProduct`, where conjugate
intersections generate the middle core. No TYPE or model recognition follows
from this index calculation.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, (12.1)(c) and the first displayed line on printed p.180.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original quotient map sends the opposite core onto the quotient Sylow. -/
theorem source_common_sylow_core_index
    {M : Type*} [Group M]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* M)
    {x : Vertex (reducedFamily L S)}
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let A := star L S i
    let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 A))
    ∃ P : Sylow 2 M,
      ((Q F x).subgroupOf A).map q = (P : Subgroup M) ∧
      (Q F x ⊓ Q F (base F i)).relIndex (Q F x) = Nat.card P ∧
      ((Q F x ⊓ Q F (base F i)).map (G₀ L S).subtype).relIndex
        ((Q F x).map (G₀ L S).subtype) = Nat.card P := by
  let F := reducedFamily L S
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective
    (inclusion (star_le_stabilizer (L := L) (S := S) i)) (inclusion_injective _)
  let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := ((originalQuotient h i).symm.trans e).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : q.ker = (Q F (base F i)).subgroupOf A := by
    have hk' : q.ker = pCore 2 A := by
      ext a
      change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) a)) = 1 ↔ a ∈ pCore 2 A
      rw [map_eq_one_iff _ e.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff a
    rw [hk', ← star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  have hXA : Q F x ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hYA : Q F (base F i) ≤ A := (le_sup_right.trans hR.ge).trans (map_subtype_le _)
  have hRA : (R : Subgroup A) = (Q F x).subgroupOf A ⊔ (Q F (base F i)).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hR, Subgroup.map_sup, map_subgroupOf_eq_of_le hXA, map_subgroupOf_eq_of_le hYA]
  let P : Sylow 2 M := R.mapSurjective (f := q) hq
  have him : ((Q F x).subgroupOf A).map q = (P : Subgroup M) := by
    change _ = (R : Subgroup A).map q
    rw [hRA, Subgroup.map_sup, ← hk, Subgroup.map_ker_self, sup_bot_eq]
  have hi : (Q F x ⊓ Q F (base F i)).relIndex (Q F x) = Nat.card P := by
    rw [inf_relIndex_left, ← relIndex_subgroupOf hXA, ← hk, relIndex_ker, him]
  refine ⟨P, him, hi, ?_⟩
  rw [relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective]
  exact hi

/-- An actual order-ten quotient makes the neighboring-core intersection index two. -/
theorem source_dihedral_core_index
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* DihedralGroup 5)
    {x : Vertex (reducedFamily L S)}
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    (Q (reducedFamily L S) x ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (Q (reducedFamily L S) x) = 2 := by
  obtain ⟨P, _, hi, _⟩ := source_common_sylow_core_index h i e R hR
  have hp : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity, DihedralGroup.nat_card]
    rw [Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization, Nat.prime_five.factorization]
    norm_num
  exact hi.trans hp
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
