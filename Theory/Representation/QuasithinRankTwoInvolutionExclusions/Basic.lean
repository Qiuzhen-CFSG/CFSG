module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod


/-!
# Transport and orbit lemmas for moved planes

The moved space of an element is the image of its displacement operator. An
intertwining linear equivalence, together with a group isomorphism, transports
this space, its dimension, and transitivity of its setwise stabilizer on nonzero
vectors. Group isomorphism alone is not enough for these conclusions.

A commuting element of order dividing three preserves the moved space. On a
binary plane, if it fixes no nonzero vector, its orbit has all three nonzero
vectors. This supplies a common final step for concrete centralizer calculations.
The dimension obstruction also excludes a two-dimensional model in dimension
at least four.

These are independent linear algebra tools for the exclusions in
Aschbacher–Smith, *The Classification of Quasithin Groups*, proof of 6.2.19,
printed p.691 (PDF p.708). They do not assert the concrete model calculations
for the thirteen alternatives of G.11.2, printed p.364 (PDF p.375).
-/

@[expose] public section

namespace Representation.RankTwo

variable {k G H V W : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The image of the displacement operator. -/
def movedSpace (ρ : Representation k G V) (v : G) : Submodule k V :=
  LinearMap.range (ρ v - 1)

/-- Setwise stabilizers act transitively on the nonzero vectors of a subspace. -/
def StabilizerTransitive (ρ : Representation k G V) (P : Submodule k V) : Prop :=
  ∀ u ∈ P, u ≠ 0 → ∀ w ∈ P, w ≠ 0 →
    ∃ g : G, (∀ z, z ∈ P ↔ ρ g z ∈ P) ∧ ρ g u = w

lemma mem_movedSpace (ρ : Representation k G V) (v : G) (w : V) :
    w ∈ movedSpace ρ v ↔ ∃ z, ρ v z - z = w := Iff.rfl

lemma map_mem_movedSpace_of_commute (ρ : Representation k G V) {g v : G}
    (h : Commute g v) {w : V} (hw : w ∈ movedSpace ρ v) :
    ρ g w ∈ movedSpace ρ v := by
  obtain ⟨z, rfl⟩ := hw
  refine ⟨ρ g z, ?_⟩
  change ρ v (ρ g z) - ρ g z = ρ g (ρ v z - z)
  rw [map_sub]
  congr 1
  exact congrArg (fun f : Module.End k V => f z) (ρ.map_mul v g |>.symm.trans
    ((congrArg ρ h.eq.symm).trans (ρ.map_mul g v)))

lemma mem_movedSpace_map_iff_of_commute (ρ : Representation k G V) {g v : G}
    (h : Commute g v) (w : V) :
    w ∈ movedSpace ρ v ↔ ρ g w ∈ movedSpace ρ v := by
  constructor
  · exact map_mem_movedSpace_of_commute ρ h
  · intro hw
    have := map_mem_movedSpace_of_commute ρ h.inv_left hw
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using this

/-- Intertwining a group isomorphism carries precisely the moved subspace. -/
lemma movedSpace_transport (ρ : Representation k G V) (σ : Representation k H W)
    (e : G ≃* H) (f : V ≃ₗ[k] W)
    (hf : ∀ g z, f (ρ g z) = σ (e g) (f z)) (v : G) (w : V) :
    f w ∈ movedSpace σ (e v) ↔ w ∈ movedSpace ρ v := by
  constructor
  · rintro ⟨z, hz⟩
    change σ (e v) z - z = f w at hz
    refine ⟨f.symm z, f.injective ?_⟩
    change f (ρ v (f.symm z) - f.symm z) = f w
    simpa only [map_sub, hf, f.apply_symm_apply] using hz
  · rintro ⟨z, rfl⟩
    refine ⟨f z, ?_⟩
    change σ (e v) (f z) - f z = f (ρ v z - z)
    rw [map_sub, hf]

/-- Restriction of an intertwining equivalence to the moved spaces. -/
def movedSpaceEquiv (ρ : Representation k G V) (σ : Representation k H W)
    (e : G ≃* H) (f : V ≃ₗ[k] W)
    (hf : ∀ g z, f (ρ g z) = σ (e g) (f z)) (v : G) :
    movedSpace ρ v ≃ₗ[k] movedSpace σ (e v) where
  toFun z := ⟨f z, (movedSpace_transport ρ σ e f hf v z).mpr z.property⟩
  invFun z := ⟨f.symm z, (movedSpace_transport ρ σ e f hf v (f.symm z)).mp
    (by simpa only [f.apply_symm_apply] using z.property)⟩
  left_inv z := by ext; exact f.symm_apply_apply z
  right_inv z := by ext; exact f.apply_symm_apply z
  map_add' x y := by ext; exact f.map_add x y
  map_smul' c x := by ext; exact f.map_smul c x

lemma finrank_movedSpace_transport (ρ : Representation k G V) (σ : Representation k H W)
    (e : G ≃* H) (f : V ≃ₗ[k] W)
    (hf : ∀ g z, f (ρ g z) = σ (e g) (f z)) (v : G) :
    Module.finrank k (movedSpace ρ v) = Module.finrank k (movedSpace σ (e v)) :=
  (movedSpaceEquiv ρ σ e f hf v).finrank_eq

lemma stabilizerTransitive_transport (ρ : Representation k G V) (σ : Representation k H W)
    (e : G ≃* H) (f : V ≃ₗ[k] W)
    (hf : ∀ g z, f (ρ g z) = σ (e g) (f z)) (v : G)
    (ht : StabilizerTransitive σ (movedSpace σ (e v))) :
    StabilizerTransitive ρ (movedSpace ρ v) := by
  intro u hu hu0 w hw hw0
  obtain ⟨g, hg, hgu⟩ := ht (f u) ((movedSpace_transport ρ σ e f hf v u).mpr hu)
    (fun h => hu0 (f.injective (h.trans (f.map_zero).symm)))
    (f w) ((movedSpace_transport ρ σ e f hf v w).mpr hw)
    (fun h => hw0 (f.injective (h.trans (f.map_zero).symm)))
  refine ⟨e.symm g, ?_, f.injective ?_⟩
  · intro z
    rw [← movedSpace_transport ρ σ e f hf v z,
      ← movedSpace_transport ρ σ e f hf v (ρ (e.symm g) z), hf, e.apply_symm_apply]
    exact hg (f z)
  · simpa only [hf, e.apply_symm_apply] using hgu

/-- The two-dimensional model cannot represent a space of dimension at least four. -/
lemma not_equiv_two_dimensional [FiniteDimensional k V]
    (hd : 4 ≤ Module.finrank k V) : IsEmpty (V ≃ₗ[k] (Fin 2 → k)) := by
  refine ⟨fun f => ?_⟩
  have he := f.finrank_eq
  simp only [Module.finrank_pi, Fintype.card_fin] at he
  omega

private lemma four_element_orbit {α : Type*} [Fintype α] [Zero α]
    (hcard : Fintype.card α = 4) (t : α → α) (ht0 : t 0 = 0)
    (ht3 : ∀ z, t (t (t z)) = z) (hfix : ∀ z, t z = z → z = 0)
    {u w : α} (hu : u ≠ 0) (hw : w ≠ 0) :
    w = u ∨ w = t u ∨ w = t (t u) := by
  classical
  have hinj : Function.Injective t := by
    intro a b hab
    have := congrArg (fun z => t (t z)) hab
    simpa only [ht3] using this
  have htu0 : t u ≠ 0 := fun h => hu (hinj (h.trans ht0.symm))
  have htt0 : t (t u) ≠ 0 := fun h => htu0 (hinj (h.trans ht0.symm))
  have htu : t u ≠ u := fun h => hu (hfix u h)
  have htt : t (t u) ≠ t u := fun h => htu (hinj h)
  have htt' : t (t u) ≠ u := by
    intro h
    have h' := congrArg t h
    rw [ht3] at h'
    exact htu h'.symm
  have hfull : ({0, u, t u, t (t u)} : Finset α) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hcard, Ne.symm hu,
      Ne.symm htu0, Ne.symm htt0, Ne.symm htu, Ne.symm htt, Ne.symm htt']
  have hm : w ∈ ({0, u, t u, t (t u)} : Finset α) := by rw [hfull]; exact Finset.mem_univ w
  simpa only [Finset.mem_insert, Finset.mem_singleton, hw, false_or] using hm

section Binary
variable {B : Type*} [AddCommGroup B] [Module (ZMod 2) B]

/-- A commuting order-three actor with no nonzero fixed vector makes the
stabilizer of a binary moved plane transitive. Concrete models must supply
`c`, its commutation, and its fixed-space calculation. -/
lemma stabilizerTransitive_of_order_three (ρ : Representation (ZMod 2) G B)
    (v c : G) [FiniteDimensional (ZMod 2) (movedSpace ρ v)]
    (hrank : Module.finrank (ZMod 2) (movedSpace ρ v) = 2)
    (hcv : Commute c v) (hc3 : c ^ 3 = 1)
    (hfix : ∀ z ∈ movedSpace ρ v, ρ c z = z → z = 0) :
    StabilizerTransitive ρ (movedSpace ρ v) := by
  classical
  let P := movedSpace ρ v
  let : Finite P := Module.finite_of_finite (ZMod 2)
  let : Fintype P := Fintype.ofFinite P
  have hcard : Fintype.card P = 4 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hrank]
    decide
  let t : P → P := fun z => ⟨ρ c z, map_mem_movedSpace_of_commute ρ hcv z.property⟩
  have ht0 : t 0 = 0 := Subtype.ext (map_zero (ρ c))
  have ht3 : ∀ z, t (t (t z)) = z := by
    intro z
    apply Subtype.ext
    change ρ c (ρ c (ρ c z.val)) = z.val
    have hc : c * (c * c) = 1 := by simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hc3
    simp only [← Module.End.mul_apply, ← map_mul, hc, map_one,
      Module.End.one_apply]
  have htf : ∀ z, t z = z → z = 0 := by
    intro z hz
    exact Subtype.ext (hfix z z.property (congrArg Subtype.val hz))
  intro u hu hu0 w hw hw0
  have hu' : (⟨u, hu⟩ : P) ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hw' : (⟨w, hw⟩ : P) ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
  rcases four_element_orbit hcard t ht0 ht3 htf hu' hw' with h | h | h
  · refine ⟨1, ?_, ?_⟩
    · intro z; simp
    · simpa only [map_one, Module.End.one_apply] using (congrArg Subtype.val h).symm
  · exact ⟨c, mem_movedSpace_map_iff_of_commute ρ hcv, (congrArg Subtype.val h).symm⟩
  · refine ⟨c * c, mem_movedSpace_map_iff_of_commute ρ (hcv.mul_left hcv), ?_⟩
    simpa only [map_mul, Module.End.mul_apply] using (congrArg Subtype.val h).symm

end Binary
end Representation.RankTwo
