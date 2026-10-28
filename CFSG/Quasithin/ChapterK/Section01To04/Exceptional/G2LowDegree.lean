module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary.FrobeniusParameters
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.OrbitBounds
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.BinarySix
public import Theory.Representation.G2DerivedPermutationFiltration
public import Theory.Representation.Quotient

/-!
# The marked natural G₂ output of the exceptional degree sieve

For a nonbinary defining field, the proved tensor classification and actual
Schur-field descent show that a faithful irreducible binary representation
is natural or has degree at least fourteen times the field exponent. The
natural alternative includes a group automorphism and a linear intertwiner.
Transport to a component preserves both maps, and perfectness converts the
full group to its actual derived subgroup only away from the binary field.

At the binary endpoint we instead use the independent recognition theorem
for the actual G₂(2)′. These are the representation-recognition part of
K.3.5, conditional on the degree estimate still required from the cubic
actor calculation of GM04 Theorem 8.1/Table 17. They do not assert that a
cubic-ratio bound has already supplied that estimate.

Source: Aschbacher--Smith, printed p.457; GLS3 2.8.6--2.8.10(g).
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterK.Exceptional
open Representation
open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
attribute [local instance] ZMod.algebra

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The actual tensor classification leaves a gap above the natural module;
quasiequivalence retains its two intertwining maps. -/
theorem g2_natural_or_large
    (ρ : Representation (ZMod 2) (Atlas.G2.Model F) V) [IsIrreducible ρ]
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective ρ) :
    Quasiequivalent ρ (naturalBinary F) ∨ 14 * r ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨_, t, l, ht, _, hperiod, hd, hne, hb, hn⟩ :=
    Nonbinary.exists_basic_parameters_and_natural ρ hr hF hf
  rcases orbit_dimension_alternatives (s := Representation.schurDegree 2 ρ) ht
      ((basic_product_alternatives l hb).resolve_left hne) with h | h
  · exact Or.inl (hn h.1 h.2)
  · exact Or.inr (by simpa only [← hperiod, ← hd] using h)

variable {G : Type*} [Group G] (ρ : Representation (ZMod 2) G V)
  (L : Subgroup G) [IsIrreducible (ρ.comp L.subtype)]

/-- A component below the nonnatural degree bound has actual marked maps to
the natural derived action. The field guard excludes the binary exception. -/
theorem g2_marked_natural_of_degree_lt
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (e : L ≃* Atlas.G2.Model F) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V < 14 * r) :
    ∃ e' : L ≃* commutator (Atlas.G2.Model F),
      ∃ f : V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space F,
        ∀ g : L, ∀ v, f (ρ g v) = derivedNaturalBinary F (e' g) (f v) := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective (ρ.comp L.subtype)).mpr inferInstance
  have hσ : Function.Injective σ := hf.comp (L.subtype_injective.comp e.symm.injective)
  obtain ⟨a, f, hact⟩ := (g2_natural_or_large σ hr hF hσ).resolve_right
    (not_le_of_gt hd)
  have hq : 2 < Nat.card F := by
    rw [hF]
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hr
    omega
  let : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect hq
  let d : commutator (Atlas.G2.Model F) ≃* Atlas.G2.Model F :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
  refine ⟨(e.trans a).trans d.symm, f, ?_⟩
  intro g v
  have h := hact (e g) v
  change f (ρ (e.symm (e g)) v) = naturalBinary F (a (e g)) (f v) at h
  rw [e.symm_apply_apply] at h
  have hv : ((d.symm (a (e g)) : commutator (Atlas.G2.Model F)) : Atlas.G2.Model F) =
      a (e g) := d.apply_symm_apply _
  change f (ρ g v) = naturalBinary F (d.symm (a (e g))).val (f v)
  rwa [hv]

attribute [local instance] BinarySix.scalars

/-- The binary endpoint retains the genuine derived-group marking. It never
identifies the full nonsimple G₂(2) with its derived subgroup. -/
theorem g2_binary_marked_natural_of_degree_six
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hd : Module.finrank (ZMod 2) V = 6) :
    ∃ e' : L ≃* commutator (Atlas.G2.Model (ZMod 2)),
      ∃ f : V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2),
        ∀ g : L, ∀ v, f (ρ g v) = derivedNaturalBinary (ZMod 2) (e' g) (f v) := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective (ρ.comp L.subtype)).mpr inferInstance
  obtain ⟨a, f, hact⟩ := BinarySix.quasiequivalent_of_finrank_eq_six σ hd
  refine ⟨e.trans a, f, ?_⟩
  intro g v
  have h := hact (e g) v
  change f (ρ (e.symm (e g)) v) = derivedNaturalBinary (ZMod 2) (a (e g)) (f v) at h
  rw [e.symm_apply_apply] at h
  exact h

end CFSG.Quasithin.ChapterK.Exceptional
