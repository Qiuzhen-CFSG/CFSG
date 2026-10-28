module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms.Checks
/-!
Intrinsic enumeration and generation for the native Borel.  The three cosets of
the Sylow subgroup enumerate `B`; the certified pair `(x,v)` generates it, so
`hom_ext` turns equality on the pair into equality of homomorphisms.  This is
the abstract interface consumed by the automorphism coverage proof.
-/

@[expose] public section
open Theory.GroupTheory
open Subgroup
open scoped Pointwise
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms
open GeneratorPair Seed PairNormalizer
open PairNormalizer.SylowData PairNormalizer.QuotientData
open GeneratorPair.SecondOrbitCertificate Overlap

/-- Three cosets of the native Sylow group enumerate the full overlap. -/
def bElement (i : Fin 384) : B :=
  ⟨sElement ⟨i.val % 128, Nat.mod_lt _ (by decide)⟩ * oddGenerator 1 ^ (i.val / 128),
    B.mul_mem ((show s ≤ B from le_sup_left) (sElement_mem _))
      ((show zpowers (oddGenerator 1) ≤ B from le_sup_right) (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))⟩

 theorem exists_bElement (b : B) : ∃ i, bElement i = b := by
  have hb : (b : Carrier) ∈ (s : Set Carrier) *
      (Subgroup.zpowers (oddGenerator 1) : Set Carrier) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (Subgroup.zpowers_le.mpr v_normalizes_s)]
    exact b.property
  obtain ⟨u, hu, v, hv, huv⟩ := hb
  obtain ⟨i, rfl⟩ := exists_sElement hu
  have hv' : v ∈ zpowers (oddGenerator 1) := hv
  rw [(isOfFinOrder_of_finite (oddGenerator 1)).mem_zpowers_iff_mem_range_orderOf,
    v_order] at hv'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv'
  have hj3 := Finset.mem_range.mp hj
  refine ⟨⟨i.val + 128 * j, by omega⟩, ?_⟩
  apply Subtype.ext
  change sElement _ * oddGenerator 1 ^ ((i.val + 128 * j) / 128) = _
  have hm : (i.val + 128 * j) % 128 = i.val := by omega
  have hd : (i.val + 128 * j) / 128 = j := by omega
  simp only [hd]
  rw [show (⟨(i.val + 128 * j) % 128, _⟩ : Fin 128) = i from Fin.ext hm]
  exact huv

/-- An explicit pair in the unchanged overlap. -/
def x : B := ⟨sElement 71, (show s ≤ B from le_sup_left) (sElement_mem _)⟩
def v : B := ⟨oddGenerator 1, (show zpowers (oddGenerator 1) ≤ B from le_sup_right) (mem_zpowers _)⟩


theorem bElement_table (i : Fin 384) : inclusion (bElement i : Carrier) = bTable i := by
  simp only [bElement, bTable, map_mul, map_pow, sElement_inclusion,
    oddGenerator_inclusion]

set_option maxRecDepth 100000 in
theorem x_table : inclusion (x : Carrier) = xTable := by
  change inclusion (sElement 71) = sTable 71
  exact sElement_inclusion _
theorem v_table : inclusion (v : Carrier) = oddTable 1 := by
  change inclusion (oddGenerator 1) = oddTable 1
  exact oddGenerator_inclusion _

theorem word_table (w : List (Fin 2)) :
    inclusion ((evalWord ![x, v] w : B) : Carrier) = evalWord ![xTable, oddTable 1] w := by
  induction w with
  | nil => exact map_one inclusion
  | cons i w ih =>
    change inclusion ((![x, v] i : B) : Carrier) *
      inclusion ((evalWord ![x, v] w : B) : Carrier) = _
    rw [ih]
    congr 1
    fin_cases i
    · exact x_table
    · exact v_table

theorem pair_generates : Subgroup.closure (Set.range ![x, v]) = ⊤ := by
  let C := Subgroup.closure (Set.range ![x, v])
  have hw (w : List (Fin 2)) : evalWord ![x, v] w ∈ C := by
    induction w with
    | nil => exact C.one_mem
    | cons i w ih => exact C.mul_mem (subset_closure ⟨i,rfl⟩) ih
  apply Subgroup.map_injective B.subtype_injective
  rw [← MonoidHom.range_eq_map, B.range_subtype]
  apply le_antisymm (map_subtype_le _)
  change s ⊔ zpowers (oddGenerator 1) ≤ C.map B.subtype
  apply sup_le
  · apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    refine mem_map.mpr ⟨evalWord ![x,v] (generatorWord i), hw _, ?_⟩
    apply inclusion_injective
    have hh := (word_table _).trans ((generator_check i).trans (sGenerator_inclusion i).symm)
    exact hh
  · apply zpowers_le.mpr
    exact mem_map.mpr ⟨v, subset_closure ⟨1,rfl⟩, rfl⟩

theorem hom_ext {M : Type*} [Monoid M] (f g : B →* M)
    (hx : f x = g x) (hv : f v = g v) : f = g := by
  apply MonoidHom.eq_of_eqOn_dense pair_generates
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact hx
  · exact hv

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.BorelAutomorphisms
