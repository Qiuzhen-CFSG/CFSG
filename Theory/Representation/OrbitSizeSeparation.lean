module
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Separation of nonzero representation orbits by their sizes

An equivariant linear isomorphism and a surjective actor map identify
the actual orbit sets, hence preserve separation by cardinality.
The intended application is the irreducible-row argument of
Aschbacher--Smith 12.2.16, printed pp.799--800.
-/

public noncomputable section
namespace Representation
/-- Distinct nonzero orbits of the actual representation have different sizes. -/
@[expose] def OrbitCardSeparates {A W : Type*} [Group A] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) A W) : Prop :=
  ∀ v w : W, v ≠ 0 → w ≠ 0 →
    (Set.range fun a : A => ρ a v).ncard = (Set.range fun a : A => ρ a w).ncard →
    ∃ a : A, ρ a v = w

/-- Surjective change of actor and equivariant coordinates preserve separation. -/
theorem OrbitCardSeparates.of_intertwining
    {A B W U : Type*} [Group A] [Group B] [AddCommGroup W] [AddCommGroup U]
    [Module (ZMod 2) W] [Module (ZMod 2) U]
    {ρ : Representation (ZMod 2) A W} {σ : Representation (ZMod 2) B U}
    (hσ : OrbitCardSeparates σ) (f : A →* B) (hf : Function.Surjective f)
    (e : W ≃ₗ[ZMod 2] U) (he : ∀ a v, e (ρ a v) = σ (f a) (e v)) :
    OrbitCardSeparates ρ := by
  have himage (v : W) : e '' (Set.range fun a : A => ρ a v) =
      Set.range fun b : B => σ b (e v) := by
    ext w
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨f a,(he a v).symm⟩
    · rintro ⟨b,rfl⟩
      obtain ⟨a,rfl⟩ := hf b
      exact ⟨ρ a v,⟨a,rfl⟩,he a v⟩
  intro v w hv hw hc
  have hc' : (Set.range fun b : B => σ b (e v)).ncard =
      (Set.range fun b : B => σ b (e w)).ncard := by
    rw [← himage v,← himage w,Set.ncard_image_of_injective _ e.injective,
      Set.ncard_image_of_injective _ e.injective,hc]
  obtain ⟨b,hb⟩ := hσ (e v) (e w) (by simpa using hv) (by simpa using hw) hc'
  obtain ⟨a,rfl⟩ := hf b
  exact ⟨a,e.injective ((he a v).trans hb)⟩


/-- On an even finite vector space, two nonzero orbits must have distinct sizes. -/
theorem OrbitCardSeparates.of_two_nonzero_orbits
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) A W) (heven : Even (Nat.card W))
    (r s : W) (hr : r ≠ 0) (hs : s ≠ 0)
    (hcover : ∀ v : W, v ≠ 0 →
      (∃ a : A, ρ a r = v) ∨ (∃ a : A, ρ a s = v)) : OrbitCardSeparates ρ := by
  let : MulAction A W :=
    { smul := fun a v => ρ a v
      one_smul := fun v => by change ρ 1 v = v; simp
      mul_smul := fun a b v => by
        change ρ (a*b) v = ρ a (ρ b v)
        rw [map_mul,Module.End.mul_apply] }
  have hz (v : W) (hv : v ≠ 0) : (0 : W) ∉ MulAction.orbit A v := by
    rintro ⟨a,ha⟩
    have hh := congrArg (ρ a⁻¹) ha
    change ρ a⁻¹ (ρ a v) = ρ a⁻¹ 0 at hh
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, map_zero] at hh
    exact hv hh
  have hor (v : W) (hv : v ≠ 0) :
      MulAction.orbit A v = MulAction.orbit A r ∨
      MulAction.orbit A v = MulAction.orbit A s := by
    rcases hcover v hv with h | h
    · exact Or.inl (MulAction.orbit_eq_iff.mpr h)
    · exact Or.inr (MulAction.orbit_eq_iff.mpr h)
  have hsep : MulAction.orbit A r ≠ MulAction.orbit A s →
      (MulAction.orbit A r).ncard ≠ (MulAction.orbit A s).ncard := by
    intro hne heq
    have hdis : Disjoint (MulAction.orbit A r) (MulAction.orbit A s) := by
      apply Set.disjoint_left.mpr
      intro v hvr hvs
      exact hne ((MulAction.orbit_eq_iff.mpr hvr).symm.trans
        (MulAction.orbit_eq_iff.mpr hvs))
    have hfull : insert 0 (MulAction.orbit A r ∪ MulAction.orbit A s) = Set.univ := by
      ext v
      simp only [Set.mem_insert_iff,Set.mem_union,Set.mem_univ,iff_true]
      by_cases hv : v = 0
      · exact Or.inl hv
      · exact Or.inr (hcover v hv)
    have hzero : (0 : W) ∉ MulAction.orbit A r ∪ MulAction.orbit A s :=
      fun hh => hh.elim (hz r hr) (hz s hs)
    have hcount := congrArg Set.ncard hfull
    rw [Set.ncard_insert_of_notMem hzero,Set.ncard_union_eq hdis,Set.ncard_univ,heq] at hcount
    obtain ⟨n,hn⟩ := heven
    omega
  intro v w hv hw hc
  change ∃ a : A, a • v = w
  apply MulAction.mem_orbit_iff.mp
  apply MulAction.orbit_eq_iff.mp
  have hc' : (MulAction.orbit A v).ncard = (MulAction.orbit A w).ncard := hc
  rcases hor v hv with hv | hv <;> rcases hor w hw with hw | hw
  · exact hw.trans hv.symm
  · by_cases he : MulAction.orbit A r = MulAction.orbit A s
    · exact hw.trans (he.symm.trans hv.symm)
    · exact (hsep he (by simpa [hv,hw] using hc')).elim
  · by_cases he : MulAction.orbit A r = MulAction.orbit A s
    · exact hw.trans (he.trans hv.symm)
    · exact (hsep he (by simpa [hv,hw] using hc'.symm)).elim
  · exact hw.trans hv.symm

end Representation
