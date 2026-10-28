module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Kernel
public import CFSG.Quasithin.ChapterF.Section06.Basic

/-!
# The complete F.6.11 interface and its noncollapsed branch

The universal source implication remains an explicit input. Its conclusion
retains solvability, the Sylow subgroup of the three-prime core, both alternatives,
the noncyclic quotient in the collapsed case, and the compatible local quotient
isomorphisms in the preserved case. Local two-cores are always embedded in
the original group before comparison.

The proved reduction excludes the collapsed alternative from unequal local
cores. The canonical isomorphism construction specifies its value on every
original element, retaining compatibility of all three amalgam terms. This
module does not claim to prove the universal F.6.11 theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Definition F.6.1, p.304, and F.6.11, pp.306–307.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {H : Type u} [Group H] [Finite H]

/-- The quotient in F.6.11 and F.6.18, before any identification with the action quotient. -/
abbrev threePrimeQuotient (H : Type u) [Group H] := H ⧸ pPrimeCore 3 H

/-- The actual image of a local subgroup in the source quotient. -/
abbrev threePrimeImage (U : Subgroup H) : Subgroup (threePrimeQuotient H) :=
  U.map (QuotientGroup.mk' (pPrimeCore 3 H))

/-- The canonical local quotient equivalence. The element formula specifies
compatibility with the inclusions from the common subgroup in the amalgam. -/
def CompatibleThreePrimeQuotient (U : Subgroup H) : Prop :=
  ∃ e : (U ⧸ (pCore 2 H).subgroupOf U) ≃* threePrimeImage U,
    ∀ x : U, (e (QuotientGroup.mk' ((pCore 2 H).subgroupOf U) x) : threePrimeQuotient H) =
      QuotientGroup.mk' (pPrimeCore 3 H) (x : H)

omit [Finite H] in
/-- Equality of the actual local kernels constructs the required compatible
isomorphism by the first isomorphism theorem. -/
theorem compatibleThreePrimeQuotient_of_kernel (U : Subgroup H)
    (hk : (pPrimeCore 3 H).subgroupOf U = (pCore 2 H).subgroupOf U) :
    CompatibleThreePrimeQuotient U := by
  let q := QuotientGroup.mk' (pPrimeCore 3 H)
  let f := q.subgroupMap U
  have hf : f.ker = (pCore 2 H).subgroupOf U := by
    rw [← hk]
    ext x
    change f x = 1 ↔ (x : H) ∈ pPrimeCore 3 H
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).mpr hx
  let a := QuotientGroup.quotientMulEquivOfEq hf.symm
  let b := QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective U)
  refine ⟨a.trans b, ?_⟩
  intro x
  change (b (a (QuotientGroup.mk' ((pCore 2 H).subgroupOf U) x)) : threePrimeQuotient H) = _
  rw [show a (QuotientGroup.mk' ((pCore 2 H).subgroupOf U) x) =
      QuotientGroup.mk' f.ker x from QuotientGroup.quotientMulEquivOfEq_mk hf.symm x]
  rfl

omit [Finite H] in
/-- The kernel bridge carries every local subgroup image to its actual image
in the representation quotient. -/
theorem threePrimeQuotientEquivCore_map (h : pPrimeCore 3 H = pCore 2 H)
    (U : Subgroup H) :
    (threePrimeImage U).map (threePrimeQuotientEquivCore h).toMonoidHom =
      U.map coreProjection := by
  rw [threePrimeImage, Subgroup.map_map]
  rfl

/-- All of F.6.11(2)(i), retaining the common Sylow image, the faithful
amalgam condition, and actual compatible equivalences for all three terms. -/
structure F611Preserved (G₁ G₂ : Subgroup H) : Prop where
  intersection : threePrimeImage G₁ ⊓ threePrimeImage G₂ = threePrimeImage (G₁ ⊓ G₂)
  triple : ChapterF.IsGoldschmidtTriple (threePrimeImage G₁) (threePrimeImage G₂)
  faithful_amalgam : pCore 2 (threePrimeQuotient H) = ⊥
  left_quotient : CompatibleThreePrimeQuotient G₁
  middle_quotient : CompatibleThreePrimeQuotient (G₁ ⊓ G₂)
  right_quotient : CompatibleThreePrimeQuotient G₂

/-- All of F.6.11(2)(ii), with both local cores embedded in the original group
and the noncyclic quotient formed inside its actual three-prime core. -/
structure F611Collapsed (G₁ G₂ : Subgroup H) : Prop where
  left_core : (pCore 2 G₁).map G₁.subtype = pCore 2 H
  right_core : (pCore 2 G₂).map G₂.subtype = pCore 2 H
  symmetric_three : Nonempty (threePrimeQuotient H ≃* Equiv.Perm (Fin 3))
  generated : G₁ ⊔ pPrimeCore 3 H = ⊤
  noncyclic : ¬ IsCyclic ((pPrimeCore 3 H) ⧸ (pCore 2 H).subgroupOf (pPrimeCore 3 H))

/-- The complete conclusion of F.6.11; this record is an interface for the
authorized universal source input, not a proof of that source theorem. -/
structure F611Conclusion (G₁ G₂ : Subgroup H) : Prop where
  core_sylow : ∃ S : Sylow 2 (pPrimeCore 3 H),
    (S : Subgroup (pPrimeCore 3 H)).map (pPrimeCore 3 H).subtype = pCore 2 H
  core_solvable : Group.IsSolvable (pPrimeCore 3 H)
  alternatives : F611Preserved G₁ G₂ ∨ F611Collapsed G₁ G₂

/-- The full universal implication of F.6.11, as permitted for this comparison.
It assumes only the genuine Goldschmidt triple, with no SQTK restriction. -/
def F611Universal : Prop :=
  ∀ {H : Type u} [Group H] [Finite H] (G₁ G₂ : Subgroup H),
    ChapterF.IsGoldschmidtTriple G₁ G₂ → F611Conclusion G₁ G₂

/-- Unequal embedded local two-cores exclude the collapsed alternative.
The source theorem remains an explicit universal input. -/
theorem apply_F611_of_different_cores (source : F611Universal.{u})
    (G₁ G₂ : Subgroup H) (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype) :
    (∃ S : Sylow 2 (pPrimeCore 3 H),
      (S : Subgroup (pPrimeCore 3 H)).map (pPrimeCore 3 H).subtype = pCore 2 H) ∧
      Group.IsSolvable (pPrimeCore 3 H) ∧ F611Preserved G₁ G₂ := by
  have h := source G₁ G₂ triple
  refine ⟨h.core_sylow, h.core_solvable, ?_⟩
  rcases h.alternatives with hp | hc
  · exact hp
  · exact (different (hc.left_core.trans hc.right_core.symm)).elim

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
