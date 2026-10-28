module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Stable
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Geometry
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Stellmacher.ElementaryAbelianMaxSylowImages
import Mathlib.Tactic

/-!
# The literal reduced-module S₅ Thompson image

The natural quotient comparison applies directly to the faithful conjugation
representation on the original normal elementary subgroup. B.2.7 supplies the
FF property and B.2.10 supplies the stable family. Kernel conjugacy localizes
its generators in the original Sylow, so the stable-family calculation identifies
the actual image of J(T).

Source: Aschbacher–Smith, C.1.24 and E.2.3(3), printed pp.130–131 and 216–217.
-/

public section

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.SymmetricFive
open ChapterB BinaryPermutation BinaryPermutation.FiveCentralExtension
variable {H Q : Type*} [Group H] [Finite H] [Group Q]
/-- Restricting the conjugate image family recovers exactly the local image family. -/
private theorem local_family_iff
    (R : Sylow 2 H) (V : Subgroup H) (q : H →* Q) (hq : Function.Surjective q)
    (E : Subgroup Q) :
    E ∈ relativeMaxOffenderImages R V q ∧ E ≤ (R : Subgroup H).map q ↔
      E ∈ maxOffenderImages R V q := by
  constructor
  · rintro ⟨⟨A, hA, h, rfl, hne⟩, hER⟩
    obtain ⟨x, rfl⟩ := hq h
    have hAg := (maxFamily_sylow_iff R A).mp hA |>.2
    have hD := (maxFamily_map_injective_iff (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective ⊤ A).mpr hAg
    rw [map_top_of_surjective _ (MulAut.conj x).surjective] at hD
    have hm : (A.map (MulAut.conj x).toMonoidHom).map q =
        (A.map q).map (MulAut.conj (q x)).toMonoidHom := by
      rw [map_map, map_map]
      congr 1
      ext a
      simp [MulAut.conj_apply]
    obtain ⟨B, hB, hBe⟩ := exists_maxFamily_sylow_same_image R q _ hD (hm ▸ hER)
    exact ⟨B, hB, hBe.trans hm, hne⟩
  · rintro ⟨A, hA, rfl, hne⟩
    refine ⟨⟨A, hA, 1, ?_, hne⟩, map_mono hA.1⟩
    have h1 : (MulAut.conj (1 : Q)).toMonoidHom = MonoidHom.id Q := by
      ext x; simp
    rw [h1, Subgroup.map_id]

/-- The restricted relative family generates precisely the actual Thompson image. -/
theorem source_family_generated [Finite Q]
    (R : Sylow 2 H) (V : Subgroup H) (q : H →* Q) (hq : Function.Surjective q) :
    (elementaryAbelianMaxJ (R : Subgroup H)).map q =
      generatedBy (relativeMaxOffenderImages R V q) ((R : Subgroup H).map q) := by
  rw [maxOffenderImages_generated R V q]
  apply le_antisymm
  · apply iSup_le
    intro E
    apply iSup_le
    rintro ⟨hE, _⟩
    exact le_iSup_of_le E (le_iSup_of_le
      ((local_family_iff R V q hq E).mpr hE) le_rfl)
  · apply iSup_le
    intro E
    apply iSup_le
    intro hE
    exact le_iSup_of_le E (le_iSup_of_le
      ⟨(local_family_iff R V q hq E).mp hE, le_top⟩ le_rfl)

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

theorem source_fixedCodim (A : Subgroup Sym) :
    fixedCodim (NormalElementaryQuotient.representation U q hq hker) A =
      fixedCodim (coreRepresentation (Fin 5)) A := by
  have hj : ¬ elementaryAbelianMaxJ (T : Subgroup H) ≤ q.ker := by rwa [hker]
  exact fixedCodim_eq_core_of_ff _ p hp he hk
    (ChapterB.lemma_B_2_7_local U q hq hker T hUT hj).1 A

theorem source_thompson_image (hD : ChapterB.Offenders.D 5 ≤ (T : Subgroup H).map q) :
    (elementaryAbelianMaxJ (T : Subgroup H)).map q = ChapterB.Offenders.D 5 := by
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
  rw [source_family_generated T U q hq]
  exact stable_generatedBy_eq_D hstable _ (T.isPGroup'.map q) hD
end CFSG.Quasithin.ChapterC.SymmetricFive
