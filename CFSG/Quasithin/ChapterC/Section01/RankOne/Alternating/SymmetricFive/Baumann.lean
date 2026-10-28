module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Source
import Mathlib.Tactic

/-!
# Thompson and Baumann images in the genuine S₅ branch

Sylow conjugacy marks the actual Thompson image as a transposition four-group.
The natural quotient constructs equivariant lifts of its fixed vectors.
Their ambient relative centralizer lies in Ω₁(Z(J(T))), so Baum(T) fixes them.
The natural pointwise-fixer calculation bounds the Baumann image by the same
four-group; J(T)≤Baum(T) gives equality. No conclusion about either image is
assumed, and the original module may have an additional fixed part.

Source: Aschbacher–Smith, C.1.24 and E.2.3(3), printed pp.130–131 and 216–217.
-/

public section

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.SymmetricFive
open ChapterB BinaryPermutation BinaryPermutation.FiveCentralExtension
variable {H : Type*} [Group H] [Finite H]
variable (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (T : Sylow 2 H) (hUT : U ≤ T)
    (q : H →* Sym) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set H))
    (p : Additive U →ₗ[ZMod 2] core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hker g v) =
      coreRepresentation (Fin 5) g (p v))
    (hk : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hker g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup H) ≤ centralizer (U : Set H))

include hUT hp he hk hJ


theorem source_thompson_conjugate :
    ∃ a : Sym, (elementaryAbelianMaxJ (T : Subgroup H)).map q =
      (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hj : ¬ elementaryAbelianMaxJ (T : Subgroup H) ≤ q.ker := by rwa [hker]
  have hs := (ChapterB.lemma_B_2_10_relative U T hUT q hq hker hj).2.1
  have hc : ∀ A, fixedCodim ρ A = fixedCodim (coreRepresentation (Fin 5)) A :=
    source_fixedCodim U T hUT q hq hker p hp he hk hJ
  have hstable : IsStable (coreRepresentation (Fin 5))
      (relativeMaxOffenderImages T U q) := by
    have hh := hs.map_of_fixedCodim ρ (coreRepresentation (Fin 5))
      (MulEquiv.refl Sym) (by intro A; simpa using hc A)
    simpa using hh
  obtain ⟨g, hg⟩ := exists_generatedBy_marking hstable (T.mapSurjective hq)
  have hgen : (elementaryAbelianMaxJ (T : Subgroup H)).map q =
      generatedBy (relativeMaxOffenderImages T U q) ((T : Subgroup H).map q) := by
    exact source_family_generated T U q hq
  rw [Sylow.coe_mapSurjective, ← hgen] at hg
  refine ⟨g⁻¹, ?_⟩
  have hh := congrArg (fun A : Subgroup Sym => A.map (MulAut.conj g⁻¹).toMonoidHom) hg
  have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Sym := by ext x; simp [MulAut.conj_apply, mul_assoc]
  have hcancel (A : Subgroup Sym) :
      (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
    rw [Subgroup.map_map, hid, Subgroup.map_id]
  simpa only [hcancel] using hh

omit hUT hp he hk hJ [Finite H] in
private theorem thompson_le_baumann (R : Subgroup H) : elementaryAbelianMaxJ R ≤ baumann R := by
  apply le_inf (sSup_le fun _ hB => hB.1)
  apply le_centralizer_iff.mpr
  intro x hx
  exact mem_centralizer_iff.mpr
    ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2

theorem source_thompson_baumann :
    (elementaryAbelianMaxJ (T : Subgroup H)).map q = (baumann (T : Subgroup H)).map q ∧
      Nat.card ((baumann (T : Subgroup H)).map q) = 4 ∧
      ∃ a : Sym, (baumann (T : Subgroup H)).map q =
        (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  obtain ⟨a, ha⟩ := source_thompson_conjugate U T hUT q hq hker p hp he hk hJ
  obtain ⟨s, hs, hse, _⟩ := exists_section ρ p hp he hk
  let J := elementaryAbelianMaxJ (T : Subgroup H)
  let E := U ⊓ centralizer (J : Set H)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ U from inf_le_left)
  have hEa : E ≤ omegaOneCenterAmbient J :=
    elementary_centralizer_maxJ_le_omegaCenter (T : Subgroup H) E
      (inf_le_left.trans hUT) inf_le_right
  have hupper : (baumann (T : Subgroup H)).map q ≤ J.map q := by
    rw [show J.map q = (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom from ha]
    rintro x ⟨g, hg, rfl⟩
    apply fixed_space_fixer_le_conjugate_D a
    intro v hv
    let w := s v
    have hwfix : w ∈ fixedSpace ρ (J.map q) := by
      rw [show J.map q = (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom from ha]
      intro z
      change ρ z (s v) = s v
      rw [← hse]
      exact congrArg s (hv z)
    have hwE : (w.toMul : H) ∈ E :=
      ⟨w.toMul.property, (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker J w).mp hwfix⟩
    have hgfix : g ∈ centralizer (omegaOneCenterAmbient J : Set H) := hg.2
    have hcomm := mem_centralizer_iff.mp hgfix _ (hEa hwE)
    have hwg : ρ (q g) w = w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply, ← hcomm, mul_inv_cancel_right]
    have hh := congrArg p hwg
    change p (ρ (q g) (s v)) = p (s v) at hh
    rw [he, hs] at hh
    exact hh
  have heq : J.map q = (baumann (T : Subgroup H)).map q :=
    le_antisymm (map_mono (thompson_le_baumann _)) hupper
  refine ⟨heq, ?_, a, heq.symm.trans ha⟩
  rw [← heq, ha, Subgroup.card_map_of_injective (MulAut.conj a).injective, D_card]
end CFSG.Quasithin.ChapterC.SymmetricFive
