import Submission.ZStar.BlockPrimitivity

/-!
# Primitive factors of finite central idempotents

This file supplies the finite-descent step needed before applying block
correspondence.  A nonzero image of a central idempotent under a ring map is
already detected on a centrally primitive factor.
-/

noncomputable section

namespace Submission.ZStar
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

def toCenter (e : CentralIdempotent A) : Subring.center A :=
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
      BlockPrimitivity.IsCentrallyPrimitive f.val ∧
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
  have hfprimitive : BlockPrimitivity.IsCentrallyPrimitive f.val := by
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
end Submission.ZStar
