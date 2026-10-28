module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve.LocalGeometry

/-!
# Solvable invariant subgroups inside the actual star component

The kernel of the star map restricted to L is a proper normal subgroup
of a C-component, hence solvable. Thus a solvable subgroup B of L* has
a solvable preimage inside L. If (Y₊S)* normalizes B, relative normality
of L shows that Y₊S normalizes this preimage. The earlier solvable control
then puts B in the actual intersection (M ∩ L)*.

No solvability of the whole star kernel is required. In particular, an
S*-invariant Borel alone is not sufficient to apply this theorem: its
Y₊*-invariance must also be established by the model argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.26(3) and the proof of 15.3.28, printed pp.1130–1131.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
variable {G : Type*} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

private theorem component_kernel_solvable
    (f : c.L →* d.Star I) (hf : f.range = d.starImage I c.L) :
    Group.IsSolvable f.ker := by
  have hk : f.ker ≠ ⊤ := by
    intro ht
    apply component_star_ne_bot d c
    rw [← hf]
    apply eq_bot_iff.mpr
    rintro _ ⟨l, rfl⟩
    exact (show l ∈ f.ker from ht ▸ mem_top l)
  let e := subgroupOfEquivOfLe c.le_thompson
  let K := f.ker.comap e.toMonoidHom
  have hK : K ≠ ⊤ := by
    intro he
    apply hk
    apply comap_injective (f := e.toMonoidHom) e.surjective
    simpa only [comap_top] using he
  let : Group.IsSolvable K := c.component.isSolvable_of_subnormal_lt_top
    (inferInstance : K.Normal).isSubnormal hK
  have hs : Group.IsSolvable (K.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective K)
  rwa [map_comap_eq_self_of_surjective e.surjective] at hs

/-- Solvable invariant control descends inside the component without changing
the star denominator or assuming that its whole kernel is solvable. -/
theorem Input.solvable_star_subgroup_le_intersection (a : Input d I c)
    (B : Subgroup (d.Star I)) (hBL : B ≤ d.starImage I c.L)
    (hs : Group.IsSolvable B)
    (hn : d.starImage I (d.Yplus ⊔ d.S) ≤ normalizer (B : Set (d.Star I))) :
    B ≤ d.starImage I (d.M ⊓ c.L) := by
  let f : c.L →* d.Star I := (d.starMap I).comp (inclusion (component_le c))
  have hf : f.range = d.starImage I c.L := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  let N := B.comap f
  have hkN : f.ker ≤ N := by
    intro x hx
    change f x ∈ B
    rw [show f x = 1 from hx]
    exact B.one_mem
  let j : f.ker →* N := inclusion hkN
  let g : N →* B := (f.comp N.subtype).codRestrict B (fun x => x.property)
  let : Group.IsSolvable f.ker := component_kernel_solvable f hf
  let := hs
  let : Group.IsSolvable N := Group.isSolvable_of_ker_le_range j g (by
    intro x hx
    have hxker : (x : c.L) ∈ f.ker := congrArg Subtype.val hx
    exact ⟨⟨x, hxker⟩, rfl⟩)
  let X := N.map c.L.subtype
  have hXL : X ≤ c.L := map_subtype_le N
  have hXI : X ≤ I := hXL.trans (component_le c)
  have hYSI : d.Yplus ⊔ d.S ≤ I := a.minimal.1.1.2
  have hIX : d.Yplus ⊔ d.S ≤ normalizer (X : Set G) := by
    apply le_normalizer_iff.mpr
    rintro i hi _ ⟨l, hl, rfl⟩
    have hIL := (normal_subgroupOf_iff_le_normalizer (component_le c)).mp a.normal
    have hiI := hYSI hi
    refine mem_map.mpr ⟨⟨i * l * i⁻¹, (hIL hiI l).mp l.property⟩, ?_, rfl⟩
    have hiStar : (d.starMap I) ⟨i, hiI⟩ ∈ d.starImage I (d.Yplus ⊔ d.S) :=
      mem_map.mpr ⟨⟨i, hiI⟩, hi, rfl⟩
    have hconj := (hn hiStar (f l)).mp hl
    change (d.starMap I) ⟨i, hiI⟩ * (d.starMap I) ⟨l, (component_le c) l.property⟩ *
      ((d.starMap I) ⟨i, hiI⟩)⁻¹ ∈ B at hconj
    change (d.starMap I) ((⟨i, hiI⟩ : I) * ⟨l, (component_le c) l.property⟩ *
      (⟨i, hiI⟩ : I)⁻¹) ∈ B
    simpa only [map_mul, map_inv] using hconj
  have hXM : X ≤ d.MI I := a.solvableControl X hXI
    (Group.isSolvable_of_surjective (c.L.subtype.subgroupMap_surjective N)) hIX
  intro b hb
  obtain ⟨l, rfl⟩ := (show b ∈ f.range from hf ▸ hBL hb)
  have hlX : (l : G) ∈ X := mem_map.mpr ⟨l, hb, rfl⟩
  exact mem_map.mpr ⟨⟨l, (component_le c) l.property⟩, ⟨(hXM hlX).1, l.property⟩, rfl⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.LieSieve
