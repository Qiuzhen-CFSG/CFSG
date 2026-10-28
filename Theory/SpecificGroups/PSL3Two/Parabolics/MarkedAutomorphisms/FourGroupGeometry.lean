module

public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Coverage
public import Theory.Representation.PSL3Two.SmallModules

/-!
# Intrinsic centers of binary four-group actions

The intersection of the displacement images of the nonidentity elements is
intrinsic to an action. Equivariant coordinates transport this intersection,
and conjugating the acting subgroup transports it by the acting automorphism.
These facts allow independently chosen natural-plus-dual coordinates to be
compared without identifying their summands in advance.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56(3–5), 15.3.58(3), and the proof of 15.3.59, pp.1147–1150.
-/

@[expose] public section

namespace Matrix.PSL3Two.MarkedAutomorphisms.FourGroupGeometry
open Subgroup

variable {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]

/-- The intersection of the images of all nonidentity displacements.
The identity is excluded: its displacement image would collapse the intersection. -/
def commonDisplacement (ρ : A → B → B) (E : Subgroup A) : Set B :=
  {w | ∀ a ∈ E, a ≠ 1 → ∃ v, ρ a v * v⁻¹ = w}

/-- An equivalence of the acting subgroups suffices for transporting the center. -/
theorem commonDisplacement_subgroupEquiv (ρ : A → B → B) (σ : C → D → D)
    {E : Subgroup A} {F : Subgroup C} (e : E ≃* F) (f : B ≃* D)
    (he : ∀ a : E, ∀ v, f (ρ a v) = σ (e a) (f v)) (w : B) :
    f w ∈ commonDisplacement σ F ↔ w ∈ commonDisplacement ρ E := by
  constructor
  · intro hw a ha hne
    have hn : (e ⟨a, ha⟩ : C) ≠ 1 := by
      intro hh
      have hh' : e ⟨a, ha⟩ = 1 := Subtype.ext hh
      have : (⟨a, ha⟩ : E) = 1 := e.injective (hh'.trans (map_one e).symm)
      exact hne (congrArg Subtype.val this)
    obtain ⟨v, hv⟩ := hw _ (e ⟨a, ha⟩).property hn
    obtain ⟨u, rfl⟩ := f.surjective v
    refine ⟨u, f.injective ?_⟩
    simpa only [map_mul, map_inv, he ⟨a, ha⟩ u] using hv
  · intro hw c hc hne
    obtain ⟨a, ha⟩ := e.surjective ⟨c, hc⟩
    have hn : (a : A) ≠ 1 := by
      intro hh
      have : a = 1 := Subtype.ext hh
      have : c = 1 := congrArg Subtype.val (ha.symm.trans (by rw [this, map_one]))
      exact hne this
    obtain ⟨v, hv⟩ := hw a a.property hn
    refine ⟨f v, ?_⟩
    have hvc := congrArg Subtype.val ha
    change (e a : C) = c at hvc
    rw [← hvc, ← he, ← map_inv, ← map_mul, hv]

/-- Pulling an actor subgroup back through a faithful map loses no displacements. -/
theorem commonDisplacement_comap (ρ : A → B → B) (σ : C → D → D)
    (j : C →* A) (hj : Function.Injective j) (f : B ≃* D)
    (E : Subgroup A) (hE : E ≤ j.range)
    (he : ∀ c, ∀ v, f (ρ (j c) v) = σ c (f v)) (w : B) :
    f w ∈ commonDisplacement σ (E.comap j) ↔
      w ∈ commonDisplacement ρ E := by
  constructor
  · intro hw a ha hne
    obtain ⟨c, rfl⟩ := hE ha
    obtain ⟨v, hv⟩ := hw c ha (fun hh => hne (hh ▸ j.map_one))
    obtain ⟨u, rfl⟩ := f.surjective v
    refine ⟨u, f.injective ?_⟩
    simpa only [map_mul, map_inv, he c u] using hv
  · intro hw c hc hne
    obtain ⟨v, hv⟩ := hw (j c) hc (fun hh => hne (hj (hh.trans j.map_one.symm)))
    refine ⟨f v, ?_⟩
    rw [← he, ← map_inv, ← map_mul, hv]

/-- Simultaneously changing actor and vector coordinates preserves the intrinsic center. -/
theorem commonDisplacement_equiv (ρ : A → B → B) (σ : C → D → D)
    (e : A ≃* C) (f : B ≃* D) (E : Subgroup A)
    (he : ∀ a ∈ E, ∀ v, f (ρ a v) = σ (e a) (f v)) (w : B) :
    f w ∈ commonDisplacement σ (E.map e.toMonoidHom) ↔
      w ∈ commonDisplacement ρ E := by
  constructor
  · intro hw a ha hne
    obtain ⟨v, hv⟩ := hw (e a) ⟨a, ha, rfl⟩ (by simpa using hne)
    obtain ⟨u, rfl⟩ := f.surjective v
    refine ⟨u, f.injective ?_⟩
    simpa only [map_mul, map_inv, he a ha u] using hv
  · rintro hw _ ⟨a, ha, rfl⟩ hne
    obtain ⟨v, hv⟩ := hw a ha (by simpa using hne)
    refine ⟨f v, ?_⟩
    change σ (e a) (f v) * (f v)⁻¹ = f w
    rw [← he a ha v, ← map_inv, ← map_mul, hv]

/-- Conjugation transports the intersection even for a noncommutative vector group. -/
theorem commonDisplacement_conj (ρ : A →* MulAut B) (E : Subgroup A)
    (a : A) (w : B) :
    ρ a w ∈ commonDisplacement (fun g => ρ g)
        (E.map (MulAut.conj a).toMonoidHom) ↔
      w ∈ commonDisplacement (fun g => ρ g) E := by
  apply commonDisplacement_equiv (fun g => ρ g) (fun g => ρ g)
    (MulAut.conj a) (ρ a) E
  intro g _ v
  change ρ a (ρ g v) = ρ (a * g * a⁻¹) (ρ a v)
  simp only [map_mul, map_inv, MulAut.mul_apply]
  change ρ a (ρ g v) = ρ a (ρ g ((ρ a).symm (ρ a v)))
  rw [MulEquiv.symm_apply_apply]

/-- Normalizing an actor subgroup always preserves its intrinsic center. -/
theorem commonDisplacement_normalizer (ρ : A →* MulAut B) (E : Subgroup A)
    {a : A} (ha : a ∈ normalizer (E : Set A)) (w : B) :
    ρ a w ∈ commonDisplacement (fun g => ρ g) E ↔
      w ∈ commonDisplacement (fun g => ρ g) E := by
  have hm : E.map (MulAut.conj a).toMonoidHom = E := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.mp ha x).mp hx
    · intro hg
      refine ⟨(MulAut.conj a).symm g, ?_, (MulAut.conj a).apply_symm_apply g⟩
      apply (mem_normalizer_iff.mp ha _).mpr
      simpa only [← MulAut.conj_apply, MulEquiv.apply_symm_apply] using hg
  simpa only [hm] using commonDisplacement_conj ρ E a w

/-- The natural three-space together with its literal contragredient dual. -/
abbrev NaturalDual := BinaryLinearThree.Vector ×
  Module.Dual (ZMod 2) BinaryLinearThree.Vector

/-- The actual natural-plus-dual matrix action, written multiplicatively. -/
noncomputable def modelAction (g : SL) (v : Multiplicative NaturalDual) :
    Multiplicative NaturalDual :=
  Multiplicative.ofAdd
    (BinaryLinearThree.W g v.toAdd.1, BinaryLinearThree.W.dual g v.toAdd.2)

/-- The intrinsic displacement intersection on the concrete matrix representation. -/
noncomputable def modelCenter (E : Subgroup SL) : Set (Multiplicative NaturalDual) :=
  commonDisplacement modelAction E

/-- The standard marked line in the natural summand. -/
def pointCenter : Set (Multiplicative NaturalDual) :=
  {w | ∃ c : ZMod 2, w.toAdd = (c • ![1, 0, 0], 0)}

end Matrix.PSL3Two.MarkedAutomorphisms.FourGroupGeometry
