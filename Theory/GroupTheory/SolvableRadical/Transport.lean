module

public import Theory.GroupTheory.SolvableRadical
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Transport of the finite solvable radical

Surjections carry the radical into the radical. Characteristicness gives the
same containment for normal inclusions, and induction along a subnormal chain
gives it for subnormal inclusions. Pulling back a solvable normal subgroup of
the radical quotient gives a solvable extension, hence the quotient has trivial
radical.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, proof of
Proposition A.3.3(5), printed p. 42; standard solvable extension theory.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- Surjective homomorphisms carry the radical into the radical. -/
theorem map_solvableRadical_le_of_surjective (f : G →* H) (hf : Function.Surjective f) :
    (solvableRadical G).map f ≤ solvableRadical H := by
  exact le_solvableRadical _ (Normal.map inferInstance f hf)
    (Group.isSolvable_of_surjective (f.subgroupMap_surjective _))

/-- Isomorphisms preserve the radical. -/
theorem map_solvableRadical_equiv [Finite H] (e : G ≃* H) :
    (solvableRadical G).map e.toMonoidHom = solvableRadical H := by
  apply le_antisymm (map_solvableRadical_le_of_surjective _ e.surjective)
  have h := map_mono (f := e.toMonoidHom) (map_solvableRadical_le_of_surjective e.symm.toMonoidHom e.symm.surjective)
  simpa [map_map] using h

/-- The radical of a normal subgroup lies in the ambient radical. -/
theorem map_solvableRadical_subtype_le_of_normal (L : Subgroup G) [L.Normal] :
    (solvableRadical L).map L.subtype ≤ solvableRadical G := by
  exact le_solvableRadical _ inferInstance
    (Group.isSolvable_of_surjective (L.subtype.subgroupMap_surjective _))

/-- The radical of a subnormal subgroup lies in the ambient radical. -/
theorem map_solvableRadical_subtype_le_of_isSubnormal {L : Subgroup G} (hL : L.IsSubnormal) :
    (solvableRadical L).map L.subtype ≤ solvableRadical G := by
  induction hL with
  | top => exact map_solvableRadical_subtype_le_of_normal _
  | step L K hLK hK hn ih =>
    let := hn
    have h := map_mono (f := K.subtype) (map_solvableRadical_subtype_le_of_normal (L.subgroupOf K))
    have he := map_solvableRadical_equiv (subgroupOfEquivOfLe hLK)
    have he' := congrArg (Subgroup.map L.subtype) he
    have hmaps : (solvableRadical (L.subgroupOf K)).map (K.subtype.comp (L.subgroupOf K).subtype) =
        (solvableRadical L).map L.subtype := by
      rw [map_map] at he'
      convert he' using 1
      congr 1
    rw [map_map, hmaps] at h
    exact h.trans ih

/-- Factoring out the radical leaves a group with trivial radical. -/
theorem solvableRadical_quotient_solvableRadical : solvableRadical (G ⧸ solvableRadical G) = ⊥ := by
  let R := solvableRadical G
  let q := QuotientGroup.mk' R
  let : Finite (G ⧸ R) := Finite.of_surjective q (QuotientGroup.mk'_surjective R)
  let S := (solvableRadical (G ⧸ R)).comap q
  let f : R →* S := R.subtype.codRestrict S (by
    intro x
    change q x ∈ solvableRadical (G ⧸ R)
    have hx : q x = 1 := (QuotientGroup.eq_one_iff x.val).mpr x.property
    rw [hx]
    exact one_mem _)
  let g : S →* solvableRadical (G ⧸ R) :=
    (q.comp S.subtype).codRestrict _ (fun x => x.property)
  have hk : g.ker ≤ f.range := by
    intro x hx
    have hx' : q x.val = 1 := congrArg Subtype.val (show g x = 1 from hx)
    exact ⟨⟨x.val, (QuotientGroup.eq_one_iff x.val).mp hx'⟩, Subtype.ext rfl⟩
  have hs : Group.IsSolvable S := Group.isSolvable_of_ker_le_range f g hk
  have hle : S ≤ R := le_solvableRadical S inferInstance hs
  have h := map_mono (f := q) hle
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R)] at h
  exact le_bot_iff.mp (by simpa [q] using h)
end Subgroup
