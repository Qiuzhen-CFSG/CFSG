module

public import Theory.GroupTheory.MaximalSylowAutomorphisms
/-!
# Sylow-preserving automorphisms of an actual normalizer

Suppose a finite local group has a normal p-subgroup characteristic in each
Sylow p-subgroup. If its transported ambient normalizer is exactly the given
local overgroup, every automorphism preserving the original ambient Sylow
preserves that overgroup. The normalizer equality is retained as an actual
subgroup equality; neither maximality nor ambient simplicity is needed.

This is the normalizer form of `stable_coatom_of_sylow_characteristic_normal`,
used by the literal J₄ pair normalizers in Aschbacher–Smith 1.3.4, p.511.
-/

public section

open Subgroup
namespace Subgroup
/-- An actual normalizer is stable under every automorphism preserving the full Sylow. -/
theorem stable_of_sylow_characteristic_normalizer
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (N : Subgroup H) [N.Normal]
    (hp : IsPGroup p N)
    (hchar : ∀ P : Sylow p H, (N.subgroupOf P.toSubgroup).Characteristic)
    (S : Sylow p G) (M : Subgroup G)
    (hSM : S.toSubgroup ≤ M) (e : M ≃* H)
    (hNM : normalizer ((N.comap e.toMonoidHom).map M.subtype : Set G) = M)
    (b : MulAut G) (hb : ∀ x, b x ∈ S ↔ x ∈ S) :
    ∀ x, b x ∈ M ↔ x ∈ M := by
  let P := (S.subtype hSM).mapSurjective (f := e.toMonoidHom) e.surjective
  let f : S ≃* P := (subgroupOfEquivOfLe hSM).symm.trans
    (e.subgroupMap (S.toSubgroup.subgroupOf M))
  let K := N.comap e.toMonoidHom
  let B := K.map M.subtype
  have hBS : B ≤ S.toSubgroup := by
    rintro _ ⟨x, hx, rfl⟩
    have hxP : e x ∈ P := hp.le_sylow_of_normal P hx
    obtain ⟨y, hy, he⟩ := hxP
    exact e.injective he ▸ hy
  have hstable : ∀ x, b x ∈ B ↔ x ∈ B := by
    have forward (c : MulAut G) (hc : ∀ x, c x ∈ S ↔ x ∈ S)
        (x : G) (hx : x ∈ B) : c x ∈ B := by
      let xS : S := ⟨x, hBS hx⟩
      let u := MulAut.congr f (stableAut S.toSubgroup c hc)
      have hxN : f xS ∈ N.subgroupOf P.toSubgroup := by
        obtain ⟨y, hy, he⟩ := hx
        change e ⟨x, hSM xS.property⟩ ∈ N
        have he' : (⟨x, hSM xS.property⟩ : M) = y := Subtype.ext he.symm
        rwa [he']
      have huN := characteristic_iff_le_comap.mp (hchar P) u hxN
      refine ⟨⟨c x, hSM ((hc x).mpr xS.property)⟩, ?_, rfl⟩
      change e ⟨c x, hSM ((hc x).mpr xS.property)⟩ ∈ N
      change (u (f xS) : H) ∈ N at huN
      have huN' : (f (stableAut S.toSubgroup c hc xS) : H) ∈ N := by
        simpa only [u, MulAut.congr_apply, MulEquiv.trans_apply, f.symm_apply_apply] using huN
      have heq : (f (stableAut S.toSubgroup c hc xS) : H) =
          e ⟨c x, hSM ((hc x).mpr xS.property)⟩ := by
        apply congrArg e
        exact Subtype.ext (stableAut_coe S.toSubgroup c hc xS)
      rwa [heq] at huN'
    intro x
    constructor
    · intro hx
      have hh : ∀ x, b.symm x ∈ S ↔ x ∈ S := fun x => by
        simpa only [b.apply_symm_apply] using (hb (b.symm x)).symm
      simpa using forward b.symm hh (b x) hx
    · exact forward b hb x
  have hmap : M.map b.toMonoidHom = M := by
    rw [← hNM, map_equiv_normalizer_eq, (show B.map b.toMonoidHom = B from by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        exact (hstable x).mpr hx
      · intro x hx
        exact ⟨b.symm x, (hstable (b.symm x)).mp (by simpa using hx), b.apply_symm_apply x⟩)]
  intro x
  constructor
  · intro hx
    have hx' : b x ∈ M.map b.toMonoidHom := hmap.symm ▸ hx
    obtain ⟨y, hy, he⟩ := hx'
    exact b.injective he ▸ hy
  · intro hx
    rw [← hmap]
    exact mem_map_of_mem b.toMonoidHom hx

/-- The normalizer of a subgroup characteristic in the preserved subgroup is stable. -/
theorem stable_normalizer_of_characteristic_subgroupOf
    {G : Type*} [Group G] (S A : Subgroup G) (hAS : A ≤ S)
    [(A.subgroupOf S).Characteristic]
    (b : MulAut G) (hb : ∀ x, b x ∈ S ↔ x ∈ S) :
    ∀ x, b x ∈ normalizer (A : Set G) ↔ x ∈ normalizer (A : Set G) := by
  let c := stableAut S b hb
  have hf : (A.subgroupOf S).map c.toMonoidHom = A.subgroupOf S :=
    characteristic_iff_map_eq.mp inferInstance c
  have hm := congrArg (Subgroup.map S.subtype) hf
  rw [map_map] at hm
  have hcomp : S.subtype.comp c.toMonoidHom = b.toMonoidHom.comp S.subtype := by
    ext x
    exact stableAut_coe S b hb x
  rw [hcomp, ← map_map, map_subgroupOf_eq_of_le hAS] at hm
  have hmap : (normalizer (A : Set G)).map b.toMonoidHom = normalizer (A : Set G) := by
    rw [map_equiv_normalizer_eq, hm]
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := hmap.symm ▸ hx
    exact b.injective he ▸ hy
  · intro hx
    rw [← hmap]
    exact mem_map_of_mem b.toMonoidHom hx

end Subgroup
