module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.SourceOrbit
public import Theory.GroupTheory.CComponent.LocalOrbitSolvable
public import Theory.GroupTheory.NormalSylowQuotientAction.ComponentLift
public import Theory.GroupTheory.SmallIndexSolvable

/-!
# Solvable parabolic placement for exchanged components

An N_T(K)-invariant solvable subgroup of the marked K/O₂(K) lifts to a
solvable subgroup of K. The C-component orbit theorem proves that its join
with the full T is solvable, including when T exchanges components.
Original 14.6.18 places that join in M, giving containment in the literal
image of M intersect K under the original quotient map. Cubic Sylow
overgroups satisfy the same conclusion by their small relative index.

Source: Aschbacher--Smith 14.6.20, printed p.1037. The actual consumers
are ComponentDiagram and BinaryG2. Original 14.6.18 is owned by
qt-e-14625-source; final support assembly stays with
qt-e-suitable-component-supports.
-/

public section
open Subgroup Theory.GroupTheory Subgroup.NormalSylowQuotientAction
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
variable {G B : Type*} [Group G] [Finite G] [Group B]

/-- Original 14.6.18 places solvable component subgroups stabilized by N_T(K)
in M, even when T exchanges K with another component. -/
theorem source_component_solvable_le_image
    (T : Sylow 2 G) (M : Subgroup G)
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* B) (J : Subgroup B) [Group.IsSolvable J]
    (hinv : ∀ s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G),
      J.map (markedCoreAction 2 K eK ⟨s,s.property.2⟩).toMonoidHom = J) :
    J ≤ (M.subgroupOf K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let Jpre := J.comap q
  let Y := Jpre.map K.subtype ⊔ (T : Subgroup G)
  have hYover : Y ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right
      (sup_le ((map_subtype_le Jpre).trans hKH) hH.2) hH
  have hker : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent q.ker := hker ▸ pCore_isPGroup.isNilpotent
  let : Group.IsSolvable Jpre := isSolvable_comap_of_solvable_ker q J
  have hsJ : Group.IsSolvable (Jpre.map K.subtype) :=
    Group.isSolvable_of_surjective (K.subtype.subgroupMap_surjective Jpre)
  have hn : (T : Subgroup G) ⊓ normalizer (K : Set G) ≤ normalizer (Jpre.map K.subtype : Set G) :=
    quotient_lift_normalized_of_subgroup_marked_invariant 2 _ K inf_le_right eK J hinv
  have hs : Group.IsSolvable Y := hK.relative_local_adjoin_isSolvable
    hKH (map_subtype_le Jpre) hH.2 T.isPGroup' hn hsJ
  have hpre : Jpre ≤ M.subgroupOf K :=
    map_le_iff_le_comap.mp (le_sup_left.trans (hsolv Y hYover hs))
  have hm := map_mono (f := q) hpre
  rwa [map_comap_eq_self_of_surjective
    (eK.surjective.comp (QuotientGroup.mk'_surjective _))] at hm

/-- Cubic overgroups invariant under the component stabilizer satisfy the
same placement, with their solvability derived from the Sylow index. -/
theorem source_component_cubic_le_image
    (T : Sylow 2 G) (M : Subgroup G)
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* B)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (J : Subgroup B)
    (hi : ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).relIndex J = 3)
    (hinv : ∀ b : MulAut B,
      ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map b.toMonoidHom =
        (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) →
      J.map b.toMonoidHom = J) :
    J ≤ (M.subgroupOf K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) := by
  let : Finite B := Finite.of_surjective eK eK.surjective
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pq := P.mapSurjective hq
  let : Group.IsNilpotent (Pq : Subgroup B) := Pq.isPGroup'.isNilpotent
  let : Group.IsSolvable J := (Pq : Subgroup B).isSolvable_of_relIndex_le_four J (by
    change ((P : Subgroup K).map q).relIndex J ≤ 4
    rw [hi]; decide)
  exact source_component_solvable_le_image T M hsolv H hH K hKH hK eK J
    (fun s => hinv _ (markedCoreAction_preserves_component_sylow 2 T K eK P hP s))
end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
