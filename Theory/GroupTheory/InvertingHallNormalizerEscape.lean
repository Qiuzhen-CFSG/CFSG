module
public import Theory.GroupTheory.InvertingSupplement
public import Mathlib.Algebra.Group.Subgroup.Basic
/-!
# Escape from products of Borels with inverted odd supplements

Conjugate the projections of an odd-primary subgroup into the two full
supplements. Their simultaneous inversion then normalizes the prescribed
subgroup, including a diagonal subgroup, and escapes the product Borel.
This is the elementary group-theoretic step in Aschbacher–Smith 4.4.13(1),
printed pp.623–624.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] in
theorem mem_normalizer_of_inverts_subgroup (A : Subgroup G) (w : G)
    (hw : ∀ a ∈ A, w*a*w⁻¹ = a⁻¹) : w ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    rw [hw a ha]
    exact A.inv_mem ha
  · intro ha
    have he := hw (w*a*w⁻¹) ha
    have hh := congrArg (fun x : G => w⁻¹*x*w) he
    have hb : w*a*w⁻¹ = a⁻¹ := by
      calc
        _ = w⁻¹*(w*(w*a*w⁻¹)*w⁻¹)*w := by group
        _ = w⁻¹*(w*a*w⁻¹)⁻¹*w := hh
        _ = a⁻¹ := by group
    rw [hb] at ha
    exact (A.inv_mem_iff).mp ha

theorem exists_conj_le_torus_in_borel {p : ℕ} [Fact p.Prime]
    (B T A : Subgroup G) (hindex : ¬ p ∣ (T.subgroupOf B).index)
    (hA : IsPGroup p A) (hAB : A ≤ B) :
    ∃ g : B, A.map (MulAut.conj (g:G)).toMonoidHom ≤ T := by
  obtain ⟨g,hg⟩ := exists_conj_le_of_prime_not_dvd_index
    (T.subgroupOf B) (A.subgroupOf B) hindex hA.comap_subtype
  refine ⟨g,?_⟩
  rintro _ ⟨a,ha,rfl⟩
  exact hg ⟨⟨a,hAB ha⟩,ha,rfl⟩

/-- Inversion of a full supplement gives escape for any prescribed odd
primary subgroup of the Borel. -/
theorem HasInvertingSupplement.normalizer_not_le {B : Subgroup G}
    (hB : HasInvertingSupplement B) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsPGroup p A) (hAB : A ≤ B) :
    ¬ normalizer (A : Set G) ≤ B := by
  obtain ⟨T,_,hi,w,hw,hinv⟩ := hB.odd_index_data
  obtain ⟨g,hg⟩ := exists_conj_le_torus_in_borel B T A (hi p hp) hA hAB
  have hn := mem_normalizer_of_inverts_subgroup
    (A.map (MulAut.conj (g:G)).toMonoidHom) w (fun a ha => hinv a (hg ha))
  intro hN
  have hN' : normalizer (A.map (MulAut.conj (g:G)).toMonoidHom : Set G) ≤ B := by
    rw [← map_equiv_normalizer_eq]
    rintro _ ⟨x,hx,rfl⟩
    exact B.mul_mem (B.mul_mem g.property (hN hx)) (B.inv_mem g.property)
  exact hw (hN' hn)

/-- Simultaneous inversion of the two full tori preserves every subgroup,
including diagonal subgroups whose projections meet both factors. -/
theorem normalizer_not_le_prod_of_inverting_tori
    (B T : Subgroup G) (C U : Subgroup H) {p : ℕ} [Fact p.Prime]
    (hindex : ¬ p ∣ (T.subgroupOf B).index)
    (hindex' : ¬ p ∣ (U.subgroupOf C).index)
    (w : G) (v : H) (hout : w ∉ B)
    (hw : ∀ t ∈ T, w*t*w⁻¹ = t⁻¹)
    (hv : ∀ u ∈ U, v*u*v⁻¹ = u⁻¹)
    (A : Subgroup (G × H)) (hA : IsPGroup p A) (hAB : A ≤ B.prod C) :
    ¬ normalizer (A : Set (G × H)) ≤ B.prod C := by
  let f := MonoidHom.fst G H
  let k := MonoidHom.snd G H
  have hAf : A.map f ≤ B := by
    rintro _ ⟨a,ha,rfl⟩
    exact (hAB ha).1
  have hAk : A.map k ≤ C := by
    rintro _ ⟨a,ha,rfl⟩
    exact (hAB ha).2
  obtain ⟨g,hg⟩ := exists_conj_le_torus_in_borel B T (A.map f) hindex (hA.map f) hAf
  obtain ⟨h,hh⟩ := exists_conj_le_torus_in_borel C U (A.map k) hindex' (hA.map k) hAk
  let z : G × H := (g,h)
  let D := A.map (MulAut.conj z).toMonoidHom
  have hDT : D ≤ T.prod U := by
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨hg (mem_map_of_mem _ (mem_map_of_mem f ha)),
      hh (mem_map_of_mem _ (mem_map_of_mem k ha))⟩
  have hnorm : (w,v) ∈ normalizer (D : Set (G × H)) := by
    apply mem_normalizer_of_inverts_subgroup
    intro a ha
    exact Prod.ext (hw a.1 (hDT ha).1) (hv a.2 (hDT ha).2)
  intro hN
  have hDC : normalizer (D : Set (G × H)) ≤ B.prod C := by
    rw [← map_equiv_normalizer_eq]
    rintro _ ⟨x,hx,rfl⟩
    exact (B.prod C).mul_mem ((B.prod C).mul_mem ⟨g.property,h.property⟩ (hN hx))
      ((B.prod C).inv_mem ⟨g.property,h.property⟩)
  exact hout (hDC hnorm).1

/-- The product version retains arbitrary subgroups of the full product. -/
theorem HasInvertingSupplement.normalizer_not_le_prod {B : Subgroup G} {C : Subgroup H}
    (hB : HasInvertingSupplement B) (hC : HasInvertingSupplement C)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup (G × H)) (hA : IsPGroup p A) (hAB : A ≤ B.prod C) :
    ¬ normalizer (A : Set (G × H)) ≤ B.prod C := by
  obtain ⟨T,_,hi,w,hw,hinv⟩ := hB.odd_index_data
  obtain ⟨U,_,hi',v,_,hinv'⟩ := hC.odd_index_data
  exact normalizer_not_le_prod_of_inverting_tori B T C U (hi p hp) (hi' p hp)
    w v hw hinv hinv' A hA hAB

end Theory.GroupTheory
