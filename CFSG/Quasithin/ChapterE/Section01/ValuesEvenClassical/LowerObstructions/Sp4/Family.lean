module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.Bounds
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Thompson
public import Theory.GroupTheory.SylowNormalRestriction


/-!
# An ambient weak-closure family for the derived symplectic lower bound

For q = 2^f with f > 1, take all elementary abelian subgroups of the normal
simple subgroup L having order q³. This family is invariant under every
ambient conjugation, including graph and field automorphisms. The two
concrete Sylow wings have this order and generate a Sylow subgroup of L.
Transporting them identifies the weak closure in the supplied T with T ∩ L.
Its normalizer is proper, since L is simple, nontrivial and perfect.

The comparison from Sp₄(q)' to Sp₄(q) uses the proved inclusion isomorphism
for q > 2. No assertion is made for the exceptional derived binary carrier.
These results construct the family and proper normalizer in E.1.14(1);
the E-member exclusion is a separate local calculation.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.5--6 and E.1.14(1), printed pp.210--211, 214.
-/

@[expose] public section

open Subgroup
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterE

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.Sp4Lower

variable {G : Type*} [Group G]

/-- All elementary subgroups of L of the maximum symplectic order q³. -/
def family (L : Subgroup G) (f : ℕ) : Set (Subgroup G) :=
  {A | A ≤ L ∧ IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ (3 * f)}

/-- Normality of L gives invariance under the full ambient conjugation action. -/
theorem family_elementary (L : Subgroup G) [L.Normal] (f : ℕ) :
    IsElementaryFamily (family L f) := by
  refine ⟨fun A hA => hA.2.1, ?_⟩
  intro g A hA
  let _ := hA.2.1
  refine ⟨?_, IsElementaryAbelian.map _, ?_⟩
  · rintro x ⟨a, ha, rfl⟩
    exact (inferInstance : L.Normal).conj_mem a (hA.1 ha) g
  · rw [card_map_of_injective (MulAut.conj g).injective]
    exact hA.2.2

variable [Finite G] {F : Type*} [Field F] [Finite F]

/-- Two actual members generate the intersection with the supplied ambient Sylow subgroup. -/
theorem exists_wings (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : L ≃* commutator (Sp F)) :
    ∃ A B : Subgroup G, A ∈ family L f ∧ B ∈ family L f ∧
      A ⊔ B = (T : Subgroup G) ⊓ L := by
  let _ : CharP F 2 := EvenProjective.charTwo_of_card hF
  let d : L ≃* Sp F := e.trans (EvenTwoRank.derivedEquiv hF (by omega))
  obtain ⟨P, hP⟩ := T.exists_sylow_map_eq_inf_of_normal L
  let R : Sylow 2 L := (unipotentSylow hF (by omega)).mapSurjective
    (f := d.symm.toMonoidHom) d.symm.surjective
  let c : unipotent (F := F) ≃* P :=
    (d.symm.subgroupMap unipotent).trans (R.equiv P)
  let j : unipotent (F := F) →* G :=
    L.subtype.comp ((P : Subgroup L).subtype.comp c.toMonoidHom)
  have hj : Function.Injective j :=
    L.subtype_injective.comp ((P : Subgroup L).subtype_injective.comp c.injective)
  have hwing (i : Bool) : (CentralRootGeometry.wing (F := F) i).map j ∈ family L f := by
    let _ := CentralRootGeometry.wing_elementary (F := F) i
    refine ⟨?_, IsElementaryAbelian.map j, ?_⟩
    · rintro x ⟨a, _, rfl⟩
      exact (c a).val.property
    · rw [card_map_of_injective hj, CentralRootGeometry.card_wing, hF, ← pow_mul,
        Nat.mul_comm f 3]
  refine ⟨_, _, hwing false, hwing true, ?_⟩
  rw [← Subgroup.map_sup, CentralRootGeometry.wings_generate]
  change (⊤ : Subgroup (unipotent (F := F))).map
    (L.subtype.comp ((P : Subgroup L).subtype.comp c.toMonoidHom)) = _
  rw [← map_map, ← map_map, map_top_of_surjective _ c.surjective, ← MonoidHom.range_eq_map,
    range_subtype, hP]

/-- The weak closure is the inner Sylow subgroup, even in an outer extension. -/
theorem weakClosure_eq (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : L ≃* commutator (Sp F)) :
    weakClosure (T : Subgroup G) (family L f) = (T : Subgroup G) ⊓ L := by
  apply le_antisymm
  · exact sSup_le fun A hA => le_inf hA.2 hA.1.1
  · obtain ⟨A, B, hA, hB, hAB⟩ := exists_wings L T hf hF e
    rw [← hAB]
    apply sup_le
    · exact le_sSup ⟨hA, (le_sup_left.trans hAB.le).trans inf_le_left⟩
    · exact le_sSup ⟨hB, (le_sup_right.trans hAB.le).trans inf_le_left⟩

/-- The normalizer of the inner Sylow subgroup is proper in the ambient group. -/
theorem normalizer_ne_top (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (T : Sylow 2 G) {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : L ≃* commutator (Sp F)) :
    normalizer ((T : Subgroup G) ⊓ L : Set G) ≠ ⊤ := by
  let _ : CharP F 2 := EvenProjective.charTwo_of_card hF
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hf
  let _ := perfect_of_card_gt_two (F := F) hq
  let d : L ≃* Sp F := e.trans (EvenTwoRank.derivedEquiv hF (by omega))
  let _ : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := d.symm.toMonoidHom) d.symm.surjective
  intro hn
  let _ : ((T : Subgroup G) ⊓ L).Normal := normalizer_eq_top_iff.mp hn
  have hs := (inferInstance : (((T : Subgroup G) ⊓ L).subgroupOf L).Normal).eq_bot_or_eq_top
  rcases hs with hs | hs
  · have hzero : (T : Subgroup G) ⊓ L = ⊥ := by
      have h := congrArg (fun H : Subgroup L => H.map L.subtype) hs
      simpa only [map_subgroupOf_eq_of_le inf_le_right, Subgroup.map_bot] using h
    obtain ⟨A, B, hA, _, hAB⟩ := exists_wings L T hf hF e
    have hAbot : A = ⊥ := bot_unique (hzero ▸ hAB ▸ le_sup_left)
    have hc : 1 < Nat.card A := by
      rw [hA.2.2]
      exact Nat.one_lt_pow (by omega) (by decide)
    simp [hAbot] at hc
  · have hT : (T : Subgroup G).subgroupOf L = ⊤ := by
      simpa only [inf_subgroupOf_right] using hs
    have hp : IsPGroup 2 L := by
      have h : IsPGroup 2 ((T : Subgroup G).subgroupOf L) :=
        T.isPGroup'.comap_of_injective L.subtype L.subtype_injective
      rw [hT] at h
      exact h.of_equiv Subgroup.topEquiv
    exact Group.IsPerfect.not_isNilpotent L hp.isNilpotent

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.Sp4Lower
