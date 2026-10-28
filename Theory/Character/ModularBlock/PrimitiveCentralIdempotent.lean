module
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Order.Preorder.Finite

/-!
# Primitive factors of finite central idempotents

In a finite ring A, every central idempotent e with nonzero image under a
ring homomorphism from the center of A has a centrally primitive factor
whose image remains nonzero. The generic predicate uses the usual factor
relation f * e = f. The ordered central-idempotent type supplies the finite
descent, and the concluding factor lemmas identify primitive idempotents
with nonzero intersection.

Choose a minimal factor surviving under the homomorphism. Every nonzero
central idempotent subfactor either survives, so minimality identifies it
with the chosen factor, or has zero image. In the latter case its complement
within the chosen factor is a surviving idempotent, and minimality forces
the original subfactor to vanish. This contradiction proves primitivity.

This is the generic algebra used before modular block correspondence in
the proof of Glauberman's Z* theorem. Ported from revision c3503435 of
public/lean-eval/glauberman_zStar, Submission/ZStar/CentralPrimitiveExistence.lean,
the generic predicate in BlockPrimitivity.lean, and the two generic lemmas
in CentralPrimitiveFactor.lean. Defining primitivity here keeps principal
block primitivity downstream and removes the historical upward import.
-/

public section
noncomputable section
namespace ModularBlock

/-- A nonzero central idempotent has no proper nonzero central-idempotent factor. -/
@[expose] def IsCentrallyPrimitive {A : Type*} [Ring A] (e : A) : Prop :=
  e ∈ Set.center A ∧ IsIdempotentElem e ∧ e ≠ 0 ∧
    ∀ f : A, f ∈ Set.center A → IsIdempotentElem f →
      f * e = f → f ≠ 0 → f = e

namespace CentralPrimitiveExistence

universe u v

/-- Central idempotents, ordered by the usual factor relation
`f ≤ e ⇔ f * e = f`. -/
structure CentralIdempotent (A : Type u) [Ring A] where
  val : A
  mem_center : val ∈ Set.center A
  isIdempotent : IsIdempotentElem val

namespace CentralIdempotent

variable {A : Type u} [Ring A]

instance : Coe (CentralIdempotent A) A := ⟨CentralIdempotent.val⟩

@[ext] theorem ext {e f : CentralIdempotent A} (h : e.val = f.val) : e = f := by
  cases e
  cases f
  simp_all

@[expose] def toCenter (e : CentralIdempotent A) : Subring.center A :=
  ⟨e.val, e.mem_center⟩

instance : LE (CentralIdempotent A) :=
  ⟨fun f e => f.val * e.val = f.val⟩

theorem le_iff {f e : CentralIdempotent A} :
    f ≤ e ↔ f.val * e.val = f.val := Iff.rfl

instance : PartialOrder (CentralIdempotent A) where
  le_refl e := e.isIdempotent
  le_trans e f g hef hfg := by
    change e.val * g.val = e.val
    calc
      e.val * g.val = (e.val * f.val) * g.val := by rw [hef]
      _ = e.val * (f.val * g.val) := mul_assoc _ _ _
      _ = e.val * f.val := by rw [hfg]
      _ = e.val := hef
  le_antisymm e f hef hfe := by
    apply ext
    calc
      e.val = e.val * f.val := hef.symm
      _ = f.val * e.val :=
        (Semigroup.mem_center_iff.mp e.mem_center f.val).symm
      _ = f.val := hfe

instance [Finite A] : Finite (CentralIdempotent A) :=
  Finite.of_injective CentralIdempotent.val (fun _ _ => ext)

end CentralIdempotent

/-- A central idempotent with nonzero image under a ring homomorphism has a
centrally primitive factor whose image is still nonzero. -/
theorem exists_isCentrallyPrimitive_factor_map_ne_zero
    {A : Type u} [Ring A] [Finite A]
    {B : Type v} [Ring B]
    (phi : Subring.center A →+* B)
    (e : A)
    (hecenter : e ∈ Set.center A)
    (heidem : IsIdempotentElem e)
    (hmap : phi ⟨e, hecenter⟩ ≠ 0) :
    ∃ f : CentralIdempotent A,
      IsCentrallyPrimitive f.val ∧
        f.val * e = f.val ∧ phi f.toCenter ≠ 0 := by
  let eCI : CentralIdempotent A := ⟨e, hecenter, heidem⟩
  let surviving : Set (CentralIdempotent A) :=
    {f | phi f.toCenter ≠ 0 ∧ f ≤ eCI}
  have heSurviving : eCI ∈ surviving := by
    exact ⟨hmap, le_rfl⟩
  obtain ⟨f, hfmin⟩ :=
    (Set.toFinite surviving).exists_minimal ⟨eCI, heSurviving⟩
  have hfmap : phi f.toCenter ≠ 0 := hfmin.1.1
  have hffe : f.val * e = f.val := hfmin.1.2
  have hfne : f.val ≠ 0 := by
    intro hfzero
    apply hfmap
    have hfCenterZero : f.toCenter = 0 := by
      apply Subtype.ext
      exact hfzero
    rw [hfCenterZero, map_zero]
  have hfprimitive : IsCentrallyPrimitive f.val := by
    refine ⟨f.mem_center, f.isIdempotent, hfne, ?_⟩
    intro g hgcenter hgid hgf hgne
    let gCI : CentralIdempotent A := ⟨g, hgcenter, hgid⟩
    have hgle : gCI ≤ f := hgf
    by_cases hgmap : phi gCI.toCenter ≠ 0
    · have hgSurviving : gCI ∈ surviving :=
        ⟨hgmap, le_trans hgle hfmin.1.2⟩
      have hfle : f ≤ gCI := hfmin.2 hgSurviving hgle
      exact congrArg CentralIdempotent.val (le_antisymm hgle hfle)
    · have hgmapZero : phi gCI.toCenter = 0 := not_ne_iff.mp hgmap
      have hfg : f.val * g = g := by
        exact (Semigroup.mem_center_iff.mp f.mem_center g).symm.trans hgf
      let cCI : CentralIdempotent A :=
        ⟨f.val - g,
          (by
            apply Semigroup.mem_center_iff.mpr
            intro a
            rw [mul_sub, sub_mul,
              Semigroup.mem_center_iff.mp f.mem_center a,
              Semigroup.mem_center_iff.mp hgcenter a]),
          IsIdempotentElem.sub hgid f.isIdempotent hgf hfg⟩
      have hcle : cCI ≤ f := by
        change (f.val - g) * f.val = f.val - g
        rw [sub_mul, f.isIdempotent.eq, hgf]
      have hcmap : phi cCI.toCenter ≠ 0 := by
        have hcmapEq : phi cCI.toCenter = phi f.toCenter := by
          calc
            phi cCI.toCenter = phi (f.toCenter - gCI.toCenter) := by
              congr 1
            _ = phi f.toCenter - phi gCI.toCenter := map_sub phi _ _
            _ = phi f.toCenter := by rw [hgmapZero, sub_zero]
        rw [hcmapEq]
        exact hfmap
      have hcSurviving : cCI ∈ surviving :=
        ⟨hcmap, le_trans hcle hfmin.1.2⟩
      have hfle : f ≤ cCI := hfmin.2 hcSurviving hcle
      have hcEq : cCI = f := le_antisymm hcle hfle
      have hsubEq : f.val - g = f.val := congrArg CentralIdempotent.val hcEq
      have hgzero : g = 0 := by simpa only [sub_eq_self] using hsubEq
      exact (hgne hgzero).elim
  exact ⟨f, hfprimitive, hffe, hfmap⟩

end CentralPrimitiveExistence

namespace CentralPrimitiveFactor

/-- A nonzero central idempotent left factor of a centrally primitive
idempotent equals that idempotent. -/
theorem eq_of_mul_eq_left_of_right_isCentrallyPrimitive
    {A : Type*} [Ring A]
    {eLocal eBrauer : A}
    (hLocalCenter : eLocal ∈ Set.center A)
    (hLocalIdempotent : IsIdempotentElem eLocal)
    (hfactor : eLocal * eBrauer = eLocal)
    (hLocalNe : eLocal ≠ 0)
    (hBrauerPrimitive : IsCentrallyPrimitive eBrauer) :
    eLocal = eBrauer :=
  hBrauerPrimitive.2.2.2 eLocal hLocalCenter hLocalIdempotent hfactor hLocalNe

/-- Two centrally primitive idempotents with nonzero intersection are equal.
This is the symmetric minimal algebraic bridge: no pre-existing factor
identity is needed. -/
theorem eq_of_mul_ne_zero_of_both_isCentrallyPrimitive
    {A : Type*} [Ring A]
    {e f : A}
    (he : IsCentrallyPrimitive e)
    (hf : IsCentrallyPrimitive f)
    (hefne : e * f ≠ 0) :
    e = f := by
  have hcomm : f * e = e * f :=
    Semigroup.mem_center_iff.mp he.1 f
  have hcenter : e * f ∈ Set.center A :=
    Set.mul_mem_center he.1 hf.1
  have hidem : IsIdempotentElem (e * f) :=
    IsIdempotentElem.mul_of_commute hcomm.symm he.2.1 hf.2.1
  have hfactorE : (e * f) * e = e * f := by
    calc
      (e * f) * e = e * (f * e) := mul_assoc _ _ _
      _ = e * (e * f) := by rw [hcomm]
      _ = (e * e) * f := (mul_assoc _ _ _).symm
      _ = e * f := by rw [he.2.1.eq]
  have hfactorF : (e * f) * f = e * f := by
    calc
      (e * f) * f = e * (f * f) := mul_assoc _ _ _
      _ = e * f := by rw [hf.2.1.eq]
  have hprodE : e * f = e :=
    he.2.2.2 (e * f) hcenter hidem hfactorE hefne
  have hprodF : e * f = f :=
    hf.2.2.2 (e * f) hcenter hidem hfactorF hefne
  exact hprodE.symm.trans hprodF

end CentralPrimitiveFactor
end ModularBlock


