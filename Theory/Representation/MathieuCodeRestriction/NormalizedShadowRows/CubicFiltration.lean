module
public import Theory.Representation.BinaryOffender.FlagCodimension
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CubicChiefCount
import all Theory.Representation.ChiefCountCubic

/-!
# Exact cubic displacement on an induced seed filtration

An element whose linear action has cube one admits the averaging operator
`1 + g + g²`, even when the element itself has larger order. Fixed dimensions
and fixed codimensions are therefore additive on invariant sections. The
result telescopes on a complete flag and on its literal intersections with
an invariant seed. Central ambient sections contribute zero to the seed.

This is the exactness needed to compare cubic constituents on the original
module with its induced chief filtration in Aschbacher--Smith, 3.1.9(6),
printed p.578, used in8.2.2(1), p.715, refs/quasithin.pdf. The averaging proof
extends the existing `BinaryPermutation.PointedSix.cubic_fixed_finrank_add`
from group order to action order. The count-to-codimension theorem reuses
the proved binary cubic constituent calculation through its private import.
The original Chapter12 consumer is `M22CodeCubicFiltration`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace MathieuCode.NormalizedShadowRows.CubicFiltration
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem fixed_finrank_add (ρ : Representation (ZMod 2) G V)
    (W : Subrepresentation ρ) (g : G) (hg : (ρ g) ^ 3 = 1) :
    Module.finrank (ZMod 2) (fixedSpace W.toRepresentation (Subgroup.zpowers g)) +
      Module.finrank (ZMod 2) (fixedSpace W.quotientRepresentation (Subgroup.zpowers g)) =
      Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers g)) := by
  let A := Subgroup.zpowers g
  let f : fixedSpace ρ A →ₗ[ZMod 2] fixedSpace W.quotientRepresentation A :=
    (W.toSubmodule.mkQ.domRestrict (fixedSpace ρ A)).codRestrict _ (by
      intro v a
      exact congrArg W.toSubmodule.mkQ (v.property a))
  have hs : Function.Surjective f := by
    intro v
    obtain ⟨a,ha⟩ := W.toSubmodule.mkQ_surjective v.val
    have hp : ρ g (ρ g (ρ g a)) = a := by
      simpa only [pow_succ, pow_zero, one_mul, map_mul, Module.End.mul_apply,
        Module.End.one_apply] using
        (LinearMap.congr_fun hg a)
    have hq1 : W.toSubmodule.mkQ (ρ g a) = v.val := by
      change W.quotientRepresentation g (W.toSubmodule.mkQ a) = _
      rw [ha]
      exact (mem_fixedSpace_zpowers_iff _ _ _).mp v.property
    have hq2 : W.toSubmodule.mkQ (ρ g (ρ g a)) = v.val := by
      change W.quotientRepresentation g (W.toSubmodule.mkQ (ρ g a)) = _
      rw [hq1]
      exact (mem_fixedSpace_zpowers_iff _ _ _).mp v.property
    refine ⟨⟨a + ρ g a + ρ g (ρ g a), ?_⟩, ?_⟩
    · apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      rw [map_add, map_add, hp]
      abel
    · apply Subtype.ext
      change W.toSubmodule.mkQ (a + ρ g a + ρ g (ρ g a)) = v.val
      rw [map_add, map_add, ha, hq1, hq2, ← two_smul (ZMod 2),
        show (2 : ZMod 2) = 0 from rfl, zero_smul, zero_add]
  let e : f.ker ≃ₗ[ZMod 2] fixedSpace W.toRepresentation A :=
    { toFun := fun v => ⟨⟨v.val.val, (Submodule.Quotient.mk_eq_zero _).mp
          (congrArg Subtype.val v.property)⟩,
        fun a => Subtype.ext (v.val.property a)⟩
      invFun := fun v => ⟨⟨v.val.val, fun a => congrArg Subtype.val (v.property a)⟩,
        Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr v.val.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, e.finrank_eq] at h
  exact (Nat.add_comm _ _).trans h

/-- Exact additivity uses the cube of the linear action, not of its lift. -/
theorem quotient_codim_add (ρ : Representation (ZMod 2) G V)
    (U : Subrepresentation ρ) (g : G) (hg : (ρ g)^3 = 1) :
    fixedCodim U.quotientRepresentation (zpowers g) +
      fixedCodim U.toRepresentation (zpowers g) = fixedCodim ρ (zpowers g) := by
  have hf := fixed_finrank_add ρ U g hg
  have hq := U.toSubmodule.finrank_quotient_add_finrank
  have h₀ := fixedCodim_add_finrank ρ (zpowers g)
  have h₁ := fixedCodim_add_finrank U.toRepresentation (zpowers g)
  have h₂ := fixedCodim_add_finrank U.quotientRepresentation (zpowers g)
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- The cubic identity passes to an invariant subspace. -/
theorem subrepresentation_cube (ρ : Representation (ZMod 2) G V)
    (U : Subrepresentation ρ) (g : G) (hg : (ρ g)^3 = 1) :
    (U.toRepresentation g)^3 = 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact LinearMap.congr_fun hg v

/-- Adjacent literal sections add without an extension error. -/
theorem section_codim_add (ρ : Representation (ZMod 2) G V)
    (L N : Subrepresentation ρ) (hLN : L ≤ N) (g : G) (hg : (ρ g)^3 = 1) :
    fixedCodim (sectionRepresentation ρ L N) (zpowers g) +
      fixedCodim L.toRepresentation (zpowers g) =
      fixedCodim N.toRepresentation (zpowers g) := by
  have he : fixedCodim (sectionLower ρ L N).toRepresentation (zpowers g) =
      fixedCodim L.toRepresentation (zpowers g) := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant
      (sectionLower ρ L N).toRepresentation L.toRepresentation (MonoidHom.id G)
      (sectionLowerEquiv ρ hLN) (fun _ _ => rfl) (zpowers g)
  have hh := quotient_codim_add N.toRepresentation (sectionLower ρ L N) g
    (subrepresentation_cube ρ N g hg)
  change fixedCodim (sectionRepresentation ρ L N) (zpowers g) + _ = _ at hh
  rwa [he] at hh

/-- A complete flag has exact cubic displacement sum. -/
theorem sum_codim (ρ : Representation (ZMod 2) G V)
    {n : ℕ} (c : Fin (n+1) → Subrepresentation ρ) (hc : Monotone c)
    (h0 : c 0 = ⊥) (h1 : c (Fin.last n) = ⊤)
    (g : G) (hg : (ρ g)^3 = 1) :
    ∑ i : Fin n, fixedCodim (sectionRepresentation ρ (c i.castSucc) (c i.succ))
      (zpowers g) = fixedCodim ρ (zpowers g) := by
  let w (i : Fin (n+1)) := fixedCodim (c i).toRepresentation (zpowers g)
  have hi (i : Fin n) :
      fixedCodim (sectionRepresentation ρ (c i.castSucc) (c i.succ)) (zpowers g) +
        w i.castSucc = w i.succ :=
    section_codim_add ρ _ _ (hc (by exact Nat.le_succ i.val)) g hg
  have hz : w 0 = 0 := by
    change fixedCodim (c 0).toRepresentation _ = _
    rw [h0]
    have hh := fixedCodim_add_finrank (⊥ : Subrepresentation ρ).toRepresentation (zpowers g)
    have he : Module.finrank (ZMod 2) (⊥ : Subrepresentation ρ).toSubmodule = 0 :=
      finrank_bot (ZMod 2) V
    rw [he] at hh
    omega
  have hl : w (Fin.last n) = fixedCodim ρ (zpowers g) := by
    change fixedCodim (c (Fin.last n)).toRepresentation _ = _
    rw [h1]
    have ht := fixedCodim_add_finrank (⊤ : Subrepresentation ρ).toRepresentation (zpowers g)
    have hh := fixedCodim_add_finrank ρ (zpowers g)
    rw [(subrepresentationFixedEquiv ρ ⊤ (zpowers g)).finrank_eq] at ht
    change fixedCodim (⊤ : Subrepresentation ρ).toRepresentation (zpowers g) +
      Module.finrank (ZMod 2) (⊤ ⊓ fixedSpace ρ (zpowers g) : Submodule (ZMod 2) V) =
      Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) V) at ht
    rw [top_inf_eq, finrank_top] at ht
    omega
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun i _ => hi i)
  rw [Finset.sum_add_distrib] at hs
  have ht : (∑ i : Fin n, w i.succ) + w 0 =
      (∑ i : Fin n, w i.castSucc) + w (Fin.last n) := by
    rw [add_comm _ (w 0), ← Fin.sum_univ_succ, ← Fin.sum_univ_castSucc]
  omega

/-- Restrict a flag term to the seed, taking its literal inverse image. -/
@[expose] def seedTerm (ρ : Representation (ZMod 2) G V)
    (P N : Subrepresentation ρ) : Subrepresentation P.toRepresentation :=
  sectionLower ρ N P

omit [FiniteDimensional (ZMod 2) V] in
theorem seedTerm_mono (ρ : Representation (ZMod 2) G V)
    (P : Subrepresentation ρ) : Monotone (seedTerm ρ P) := by
  intro L N h v hv
  exact h hv

omit [FiniteDimensional (ZMod 2) V] in
@[simp] theorem seedTerm_bot (ρ : Representation (ZMod 2) G V)
    (P : Subrepresentation ρ) : seedTerm ρ P ⊥ = ⊥ := by
  ext v
  change (v : V) = 0 ↔ v = 0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

omit [FiniteDimensional (ZMod 2) V] in
@[simp] theorem seedTerm_top (ρ : Representation (ZMod 2) G V)
    (P : Subrepresentation ρ) : seedTerm ρ P ⊤ = ⊤ := by
  ext v
  rfl

/-- Exact cubic additivity on the seed's induced flag. -/
theorem sum_seed_codim (ρ : Representation (ZMod 2) G V) (P : Subrepresentation ρ)
    {n : ℕ} (c : Fin (n+1) → Subrepresentation ρ) (hc : Monotone c)
    (h0 : c 0 = ⊥) (h1 : c (Fin.last n) = ⊤)
    (g : G) (hg : (ρ g)^3 = 1) :
    ∑ i : Fin n, fixedCodim (sectionRepresentation P.toRepresentation
      (seedTerm ρ P (c i.castSucc)) (seedTerm ρ P (c i.succ))) (zpowers g) =
        fixedCodim P.toRepresentation (zpowers g) := by
  exact sum_codim P.toRepresentation (fun i => seedTerm ρ P (c i))
    ((seedTerm_mono ρ P).comp hc) (by rw [h0,seedTerm_bot])
    (by rw [h1,seedTerm_top]) g (subrepresentation_cube ρ P g hg)

/-- A central ambient section contributes zero on the induced seed section. -/
theorem seed_section_codim_zero (ρ : Representation (ZMod 2) G V)
    (P L N : Subrepresentation ρ) (g : G)
    (hz : ∀ v, sectionRepresentation ρ L N g v = v) :
    fixedCodim (sectionRepresentation P.toRepresentation
      (seedTerm ρ P L) (seedTerm ρ P N)) (zpowers g) = 0 := by
  apply (fixedCodim_eq_zero_iff _ _).mpr
  apply top_unique
  intro v _
  apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
  apply (sectionRepresentation_trivial_iff P.toRepresentation _ _ g).mpr
  intro w hw
  exact (sectionRepresentation_trivial_iff ρ L N g).mp hz w.val hw

/-- Count-to-displacement direction for the actual order-three action. -/
theorem fixedCodim_of_count {X W : Type*} [Group X] [Finite X]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) X W) (hX : Nat.card X = 3) {n : ℕ}
    (hc : BinaryLinearThree.ParabolicCyclic.ChiefCounts.HasCount ρ n) :
    fixedCodim ρ ⊤ = 2*n := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic X := isCyclic_of_prime_card hX
  obtain ⟨a,ha⟩ := IsCyclic.exists_generator (α := X)
  have hgen : zpowers a = ⊤ := top_unique (fun x _ => ha x)
  have ha3 : a^3 = 1 := by simpa only [hX] using pow_card_eq_one' (x := a)
  exact Representation.ChiefCountCubic.fixed_codim_count
    (MonoidHom.id X) Function.surjective_id
    (IsPGroup.of_card (n := 0) (by simp))
    (⊤ : Subgroup X) (by simpa using hX)
    (IsPGroup.of_card (n := 0) (by simp)) ⊤ (by simp) a ha3 hgen ρ hc

end MathieuCode.NormalizedShadowRows.CubicFiltration
