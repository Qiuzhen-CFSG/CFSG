module
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Lifting a marked Sylow center through a coprime kernel

A prescribed prime subgroup can be extended inside the preimage of a
prescribed quotient Sylow subgroup. The index formula makes that extension
Sylow in the original group. If the kernel has order prime to p, the
restriction to the lifted Sylow is an isomorphism.

When the quotient center lies in the image of a subgroup A, first choose a
Sylow subgroup in its preimage inside A. Extending this subgroup as above
puts the whole lifted center in A; the kernel need not be central.

This is the coprime lifting step in Aschbacher--Smith, original 4.3.2,
printed p.618. The unitary root-placement calculation is a separate input.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Finite G] [Group H]
  {p : ℕ} [Fact p.Prime]

/-- Extend a prescribed prime subgroup inside the preimage of a prescribed quotient Sylow. -/
theorem exists_sylow_map_eq_containing (f : G →* H) (hf : Function.Surjective f)
    (P : Sylow p H) (X : Subgroup G) (hX : IsPGroup p X)
    (hXP : X.map f ≤ P) :
    ∃ Q : Sylow p G, (Q : Subgroup G).map f = P ∧ X ≤ Q := by
  let : Finite H := Finite.of_surjective f hf
  let K := (P : Subgroup H).comap f
  have hXK : X ≤ K := map_le_iff_le_comap.mp hXP
  obtain ⟨Q₀, hQ₀⟩ := (hX.comap_of_injective K.subtype K.subtype_injective).exists_le_sylow
  let Q' := (Q₀ : Subgroup K).map K.subtype
  have hQ' : IsPGroup p Q' := Q₀.isPGroup'.map K.subtype
  have hi : ¬ p ∣ Q'.index := by
    rw [index_map_subtype, (P : Subgroup H).index_comap_of_surjective hf]
    exact Nat.Prime.not_dvd_mul Fact.out Q₀.not_dvd_index P.not_dvd_index
  let Q := hQ'.toSylow hi
  have hmap : (Q : Subgroup G).map f ≤ P :=
    map_le_iff_le_comap.mpr (map_subtype_le _)
  refine ⟨Q, ((Q.mapSurjective hf).is_maximal' P.isPGroup' hmap).symm, ?_⟩
  exact (map_subgroupOf_eq_of_le hXK).symm.le.trans (map_mono hQ₀)

/-- A Sylow center contained in a quotient subgroup lifts into that same subgroup
when the kernel has order prime to p. -/
theorem exists_sylow_center_le_of_coprime (f : G →* H) (hf : Function.Surjective f)
    (hker : Nat.Coprime p (Nat.card f.ker)) (A : Subgroup G) (P : Sylow p H)
    (hZ : (center P).map (P : Subgroup H).subtype ≤ A.map f) :
    ∃ Q : Sylow p G, (Q : Subgroup G).map f = P ∧
      (center Q).map (Q : Subgroup G).subtype ≤ A := by
  let Z := (center P).map (P : Subgroup H).subtype
  have hZp : IsPGroup p Z := (P.isPGroup'.to_subgroup (center P)).map _
  let C := Z.comap f ⊓ A
  let q : C →* Z := (f.comp C.subtype).codRestrict Z (fun x => x.property.1)
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨x, hx, hfx⟩ := hZ z.property
    refine ⟨⟨x, ⟨?_, hx⟩⟩, Subtype.ext hfx⟩
    change f x ∈ Z
    rw [hfx]
    exact z.property
  let S : Sylow p C := Sylow.nonempty.some
  have hStop : ((S.mapSurjective hq : Sylow p Z) : Subgroup Z) = ⊤ := by
    exact top_unique ((hZp.to_subgroup ⊤).le_sylow_of_normal _)
  let X := (S : Subgroup C).map C.subtype
  have hXmap : X.map f = Z := by
    have hh := congrArg (Subgroup.map Z.subtype) hStop
    change ((S : Subgroup C).map q).map Z.subtype = (⊤ : Subgroup Z).map Z.subtype at hh
    rw [map_map, ← MonoidHom.range_eq_map, range_subtype] at hh
    change (S : Subgroup C).map (f.comp C.subtype) = Z at hh
    simpa only [X, map_map] using hh
  have hXA : X ≤ A := (map_subtype_le _).trans inf_le_right
  have hXP : X.map f ≤ P := hXmap ▸ map_subtype_le _
  obtain ⟨Q, hQP, hXQ⟩ := exists_sylow_map_eq_containing f hf P X
    (S.isPGroup'.map C.subtype) hXP
  let r : Q →* P := (f.comp (Q : Subgroup G).subtype).codRestrict P
    (fun x => by
      change f x ∈ (P : Subgroup H)
      rw [← hQP]
      exact mem_map_of_mem f x.property)
  have hr : Function.Bijective r := by
    constructor
    · intro x y he
      exact injective_comp_subtype_of_coprime_ker f hker _ Q.isPGroup'
        (congrArg Subtype.val he)
    · intro y
      have hy : (y : H) ∈ (Q : Subgroup G).map f := by
        rw [hQP]
        exact y.property
      obtain ⟨x, hx, he⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  let e : Q ≃* P := MulEquiv.ofBijective r hr
  refine ⟨Q, hQP, ?_⟩
  rintro x ⟨z, hz, rfl⟩
  have hfz : f (z : G) ∈ Z :=
    ⟨e z, (centerCongr e ⟨z,hz⟩).property, rfl⟩
  obtain ⟨w, hw, he⟩ := hXmap.symm ▸ hfz
  have hwz : (⟨w, hXQ hw⟩ : Q) = z :=
    injective_comp_subtype_of_coprime_ker f hker _ Q.isPGroup' he
  have hwz' : w = (z : G) := congrArg Subtype.val hwz
  change (z : G) ∈ A
  rw [← hwz']
  exact hXA hw

end Theory.GroupTheory
