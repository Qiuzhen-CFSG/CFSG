module
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootTitsSystem
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Root data on a quotient of an infinite completion

All local decompositions are kept on the original endpoint subgroups. A single
surjective homomorphism, injective on each endpoint, transports these to the
quotient. The root signs and Cartan intersection are measured in that quotient,
as in the second case of DGS (3.7). Endpoint overlap is a separate geometric
input; it does not follow from endpoint injectivity.

The construction yields `RootPairData` and hence a genuine marked Tits system.
It assumes neither finiteness of the original group nor global injectivity.
Source: DGS, *Groups and Graphs* (1985), Part II, (3.6)–(3.7), pp.77–80.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X Y : Type*} [Group X] [Group Y]

/-- Source local structure before taking the group quotient. Root signs are
stated after the same quotient map; the opposite sign need not hold upstairs. -/
structure RootQuotientData (q : X →* Y) where
  B : Subgroup X
  N : Subgroup X
  endpoint : Bool → Subgroup X
  lift : Bool → N
  root : Bool → Subgroup X
  fixed : Bool → Subgroup X
  borel_le : ∀ i, B ≤ endpoint i
  lift_mem : ∀ i, (lift i : X) ∈ endpoint i
  lift_not_mem : ∀ i, (lift i : X) ∉ B
  generated : endpoint false ⊔ endpoint true = ⊤
  cells : ∀ i x, x ∈ endpoint i → x ∈ B ∨
    ∃ a c, a ∈ B ∧ c ∈ B ∧ x = a * (lift i : X) * c
  thick : ∀ i, ∃ x ∈ endpoint i, x ∉ B ∧ x * (lift i : X)⁻¹ ∉ B
  square : ∀ i, (lift i : X) * (lift i : X) ∈ B
  normal : ((B ⊓ N).subgroupOf N).Normal
  normalizer_generated : N ≤ Subgroup.closure
    ((B ⊓ N : Subgroup X) ∪ Set.range fun i => (lift i : X))
  factor : ∀ i b, b ∈ B → ∃ b₀ ∈ fixed i, ∃ r ∈ root i, b = b₀ * r
  conjugate_fixed : ∀ i b₀, b₀ ∈ fixed i → (lift i : X) * b₀ * (lift i : X)⁻¹ ∈ B
  root_sign : ∀ i n, n ∈ N →
    (∀ r ∈ root i, q (n⁻¹ * r * n) ∈ B.map q) ∨
    (∀ r ∈ root i, q (((lift i : X) * n)⁻¹ * r * ((lift i : X) * n)) ∈ B.map q)

namespace RootQuotientData
variable {q : X →* Y} (d : RootQuotientData q)

/-- The marked normalizer lift is the image of the original chosen reflection. -/
def imageLift (i : Bool) : d.N.map q :=
  ⟨q (d.lift i), ⟨d.lift i, (d.lift i).property, rfl⟩⟩

/-- Injectivity on an endpoint preserves nonmembership in its Borel. -/
theorem image_not_mem_borel
    (hinj : ∀ i, Set.InjOn q (d.endpoint i)) (i : Bool) {x : X}
    (hx : x ∈ d.endpoint i) (hxB : x ∉ d.B) : q x ∉ d.B.map q := by
  rintro ⟨b, hb, he⟩
  exact hxB ((hinj i (d.borel_le i hb) hx he) ▸ hb)

/-- Relative normality of the original Cartan intersection descends, provided
the quotient has exactly its image as Borel-normalizer intersection. -/
theorem image_intersection_normal
    (hBN : d.B.map q ⊓ d.N.map q = (d.B ⊓ d.N).map q) :
    ((d.B.map q ⊓ d.N.map q).subgroupOf (d.N.map q)).Normal := by
  constructor
  intro z hz n
  change (z : Y) ∈ d.B.map q ⊓ d.N.map q at hz
  rw [hBN] at hz
  obtain ⟨b, hb, hbz⟩ := hz
  obtain ⟨a, ha, han⟩ := n.property
  change (n : Y) * z * (n : Y)⁻¹ ∈ d.B.map q ⊓ d.N.map q
  rw [hBN]
  have hconj := d.normal.conj_mem (⟨b, hb.2⟩ : d.N) hb (⟨a, ha⟩ : d.N)
  refine ⟨a * b * a⁻¹, hconj, ?_⟩
  simp only [map_mul, map_inv, hbz, han]

/-- The original normalizer generation descends with its literal two lifts. -/
theorem image_normalizer_generated
    (hBN : d.B.map q ⊓ d.N.map q = (d.B ⊓ d.N).map q) :
    d.N.map q ≤ Subgroup.closure
      ((d.B.map q ⊓ d.N.map q : Subgroup Y) ∪ Set.range fun i => (d.imageLift i : Y)) := by
  apply le_trans (Subgroup.map_mono d.normalizer_generated)
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro y ⟨x, hx, rfl⟩
  rcases hx with hx | ⟨i, rfl⟩
  · left
    rw [hBN]
    exact ⟨x, hx, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

/-- Transport the local structure and the two root signs through the same map.
The two overlap equations and endpoint injectivity are independent premises. -/
def imageData (hsurj : Function.Surjective q)
    (hinj : ∀ i, Set.InjOn q (d.endpoint i))
    (hoverlap : (d.endpoint false).map q ⊓ (d.endpoint true).map q = d.B.map q)
    (hBN : d.B.map q ⊓ d.N.map q = (d.B ⊓ d.N).map q) :
    RootPairData (X := Y) where
  B := d.B.map q
  N := d.N.map q
  endpoint i := (d.endpoint i).map q
  lift := d.imageLift
  root i := (d.root i).map q
  fixed i := (d.fixed i).map q
  borel_le i := Subgroup.map_mono (d.borel_le i)
  lift_mem i := ⟨d.lift i, d.lift_mem i, rfl⟩
  lift_not_mem i := d.image_not_mem_borel hinj i (d.lift_mem i) (d.lift_not_mem i)
  overlap := hoverlap
  generated := by rw [← Subgroup.map_sup, d.generated]; exact Subgroup.map_top_of_surjective _ hsurj
  cells := by
    rintro i y ⟨x, hx, rfl⟩
    rcases d.cells i x hx with hxB | ⟨a, c, ha, hc, rfl⟩
    · exact Or.inl ⟨x, hxB, rfl⟩
    · exact Or.inr ⟨q a, q c, ⟨a, ha, rfl⟩, ⟨c, hc, rfl⟩, by simp only [map_mul]; rfl⟩
  thick := by
    intro i
    obtain ⟨x, hx, hxB, hxtB⟩ := d.thick i
    refine ⟨q x, ⟨x, hx, rfl⟩, d.image_not_mem_borel hinj i hx hxB, ?_⟩
    have hxt := d.image_not_mem_borel hinj i
      ((d.endpoint i).mul_mem hx ((d.endpoint i).inv_mem (d.lift_mem i))) hxtB
    simpa only [map_mul, map_inv, imageLift] using hxt
  square i := ⟨(d.lift i : X) * (d.lift i : X), d.square i, map_mul q _ _⟩
  normal := d.image_intersection_normal hBN
  normalizer_generated := d.image_normalizer_generated hBN
  factor := by
    rintro i y ⟨b, hb, rfl⟩
    obtain ⟨b₀, hb₀, r, hr, rfl⟩ := d.factor i b hb
    exact ⟨q b₀, ⟨b₀, hb₀, rfl⟩, q r, ⟨r, hr, rfl⟩, map_mul q _ _⟩
  conjugate_fixed := by
    rintro i y ⟨b, hb, rfl⟩
    exact ⟨(d.lift i : X) * b * (d.lift i : X)⁻¹, d.conjugate_fixed i b hb,
      by simp only [map_mul, map_inv]; rfl⟩
  root_sign := by
    rintro i y ⟨n, hn, rfl⟩
    rcases d.root_sign i n hn with hpos | hneg
    · left
      rintro z ⟨r, hr, rfl⟩
      simpa only [map_mul, map_inv] using hpos r hr
    · right
      rintro z ⟨r, hr, rfl⟩
      simpa only [map_mul, map_inv, imageLift] using hneg r hr

end RootQuotientData
end Theory.GroupTheory.WeakBNPair.RegularTree
