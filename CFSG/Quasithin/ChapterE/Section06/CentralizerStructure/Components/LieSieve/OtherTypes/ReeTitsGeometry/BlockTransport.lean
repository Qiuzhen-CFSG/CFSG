module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Ree.TitsLocal.BlockLayers
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import Theory.GroupTheory.ComponentLocalPrimeFree
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Relative block obstructions after adjoining a two-group

Every chi-zero block has order divisible by three. Thus three-free local
groups remain block-free after adjoining a normalizing two-group. For the
other obstruction, the normal local group is a single coordinate section of
its join. A subnormal short subgroup lies in that section by two-perfection;
its action on the section's actual two-core has square-one commutators.
An intrinsic core-action rigidity theorem can therefore exclude it.

The subnormality here is relative to the join, and the block predicate is
transported along the genuine subgroup inclusion equivalence.

Source: Aschbacher–Smith, C.1.7 and C.1.12, printed pp.123–124, and the
invariant-parabolic step in E.6.8, printed pp.247–248.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
open ChapterC Chapter2.ComponentRefinement.LieType
variable {G X : Type*} [Group G] [Group X] [Finite G]

omit [Finite G] in
/-- Three-free groups contain no chi-zero block, including relative subnormal ones. -/
theorem noChiZeroBlocks_of_three_free {D : Subgroup G} (hD : ¬ 3 ∣ Nat.card D) :
    NoChiZeroBlocks D := by
  intro B hBD _ hb
  apply hD
  exact ((Ree.three_dvd_quotient_card hb).trans (pCore 2 B).card_quotient_dvd_card).trans
    (card_dvd_of_le hBD)

/-- No new factor of three appears when adjoining a normalizing two-group. -/
theorem join_three_free {P Q : Subgroup G} (hinv : Q ≤ normalizer (P : Set G))
    (hP : ¬ 3 ∣ Nat.card P) (hQ : IsPGroup 2 Q) :
    ¬ 3 ∣ Nat.card ↥(P ⊔ Q) := by
  apply not_dvd_card_sup_of_normalizes Nat.prime_three P Q hinv hP
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  rw [hn]
  exact fun hd => (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

/-- A normal local subgroup with a two-group supplement is a one-coordinate section. -/
noncomputable def coreSectionOfJoin {P Q : Subgroup G}
    (hinv : Q ≤ normalizer (P : Set G)) (hQ : IsPGroup 2 Q) (e : P ≃* X) :
    G2.RelativeBlocks.CoreSection ↥(P ⊔ Q) X := by
  let N := P.subgroupOf (P ⊔ Q)
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le P.le_normalizer hinv)
  let f : N ≃* X := (subgroupOfEquivOfLe le_sup_left).trans e
  refine {
    base := N
    normal := inferInstance
    quotient_two := ?_
    count := 1
    projection := fun _ => f.toMonoidHom
    surjective := fun _ => f.surjective
    core_image := fun _ => pCore_map_iso 2 f
    kernel_two := ?_ }
  · apply isPGroup_quotient_of_sup_eq_top N (Q.subgroupOf (P ⊔ Q)) hQ.comap_subtype
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  · change IsPGroup 2 (⨅ _ : Fin 1, f.toMonoidHom.ker : Subgroup N)
    rw [iInf_const]
    exact IsPGroup.ker_isPGroup_of_injective (p := 2) (ϕ := f.toMonoidHom) f.injective

/-- Relative subnormality is transported into the actual overgroup before applying core rigidity. -/
theorem noChiZeroBlocks_of_coreSection {D : Subgroup G}
    (d : G2.RelativeBlocks.CoreSection D X)
    (hrigid : ∀ B : Subgroup X, B.IsSubnormal → IsPPerfect 2 B →
      (∀ q ∈ pCore 2 X, ∀ b ∈ B, (⁅q, b⁆ : X) ^ 2 = 1) → B = ⊥) :
    NoChiZeroBlocks D := by
  intro B hBD hsub hb
  exact G2.RelativeBlocks.not_short_of_coreSection d hrigid (B.subgroupOf D) hsub
    (hb.chi.short.of_mulEquiv (subgroupOfEquivOfLe hBD).symm)

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.ReeTitsGeometry
