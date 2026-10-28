module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.StableFamilies
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Paired.Marking
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.Source
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.Representation.BinaryOffender.GeneratedCore
import Mathlib.Tactic

/-!
# The paired S₅ Thompson image in the original quotient

The literal marked natural pair transports the source stable family, and the
actual Sylow exchanger activates both axes. The resulting Thompson image is
the product of conjugate transposition four-groups in the two factors. This
retains the original quotient map, Sylow intersection and centralizer kernel;
no global S₅ Sylow assertion is made.

Source: Aschbacher–Smith E.2.3(1),(3) and 3.1.7, pp.216–217 and575–576.
-/

public section
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open ChapterB ChapterB.SourceInduction
variable {H : Type*} [Group H]

private theorem generated_on_layer (Y : Subgroup H) (e : Y ≃* Sym × Sym)
    (P : Set (Subgroup H)) (hP : ∀ A ∈ P, A ≤ Y)
    (S : Subgroup H) (R : Subgroup (Sym × Sym))
    (hR : R.map (Y.subtype.comp e.symm.toMonoidHom) = S ⊓ Y) :
    generatedBy P S = (generatedBy
      {A | A.map (Y.subtype.comp e.symm.toMonoidHom) ∈ P} R).map
        (Y.subtype.comp e.symm.toMonoidHom) := by
  let j := Y.subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := Y.subtype_injective.comp e.symm.injective
  apply le_antisymm
  · apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA,hAS⟩
    let B := (A.subgroupOf Y).map e.toMonoidHom
    have hB : B.map j = A := by
      rw [map_map]
      have hc : j.comp e.toMonoidHom = Y.subtype := by ext x; simp [j]
      rw [hc,map_subgroupOf_eq_of_le (hP A hA)]
    rw [←hB]
    apply map_mono
    refine le_iSup_of_le B (le_iSup_of_le ⟨by change B.map j ∈ P; rwa [hB],?_⟩ le_rfl)
    apply (map_le_map_iff_of_injective hj).mp
    rw [hR,hB]
    exact le_inf hAS (hP A hA)
  · rw [map_le_iff_le_comap]
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA,hAR⟩
    apply map_le_iff_le_comap.mp
    refine le_iSup_of_le (A.map j) (le_iSup_of_le ⟨hA,?_⟩ le_rfl)
    exact (map_mono hAR).trans (hR.le.trans inf_le_left)

private theorem active_axes_in_layer (Y : Subgroup H) [Y.Normal] (e : Y ≃* Sym × Sym)
    (P : Set (Subgroup H))
    (hP : ∀ A ∈ P, ∀ g : H, A.map (MulAut.conj g).toMonoidHom ∈ P)
    (hstable : IsStable action {A | A.map (Y.subtype.comp e.symm.toMonoidHom) ∈ P})
    (g : H)
    (h₁ : (((⊤ : Subgroup Sym).prod ⊥).map (Y.subtype.comp e.symm.toMonoidHom)).map
      (MulAut.conj g).toMonoidHom = ((⊥ : Subgroup Sym).prod ⊤).map (Y.subtype.comp e.symm.toMonoidHom))
    (h₂ : (((⊥ : Subgroup Sym).prod ⊤).map (Y.subtype.comp e.symm.toMonoidHom)).map
      (MulAut.conj g).toMonoidHom = ((⊤ : Subgroup Sym).prod ⊥).map (Y.subtype.comp e.symm.toMonoidHom)) :
    (∃ A : Subgroup (Sym × Sym), A.map (Y.subtype.comp e.symm.toMonoidHom) ∈ P ∧ A.map (MonoidHom.fst Sym Sym) ≠ ⊥) ∧
    ∃ A : Subgroup (Sym × Sym), A.map (Y.subtype.comp e.symm.toMonoidHom) ∈ P ∧ A.map (MonoidHom.snd Sym Sym) ≠ ⊥ := by
  let j := Y.subtype.comp e.symm.toMonoidHom
  let τ : MulAut (Sym × Sym) := e.symm.trans ((MulAut.conjNormal g).trans e)
  have hj : Function.Injective j := Y.subtype_injective.comp e.symm.injective
  have he : j.comp τ.toMonoidHom = (MulAut.conj g).toMonoidHom.comp j := by
    ext x
    change ((e.symm (e ((MulAut.conjNormal g) (e.symm x))) : Y) : H) = _
    rw [e.symm_apply_apply]
    rfl
  apply active_axes_of_exchange hstable τ
  · intro A hA
    change (A.map τ.toMonoidHom).map j ∈ P
    rw [map_map,he,←map_map]
    exact hP _ hA g
  · apply Subgroup.map_injective hj
    rw [map_map,he,←map_map]
    exact h₁
  · apply Subgroup.map_injective hj
    rw [map_map,he,←map_map]
    exact h₂

variable {G : Type*} [Group G] [Finite G] [Finite H]

/-- The original Thompson image is the product of the two marked transposition
four-groups on the same source natural pair. -/
theorem source_thompson_images
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (Y : Subgroup H) [Y.Normal]
    (hY : offenderSubgroup (NormalElementaryQuotient.representation U q hq hker) ≤ Y)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp Y.subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hex : ∃ g : H,
      (((⊤ : Subgroup Sym).prod ⊥).map (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom)).map
        (MulAut.conj g).toMonoidHom = ((⊥ : Subgroup Sym).prod ⊤).map
          (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom) ∧
      (((⊥ : Subgroup Sym).prod ⊤).map (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom)).map
        (MulAut.conj g).toMonoidHom = ((⊤ : Subgroup Sym).prod ⊥).map
          (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom)) :
    ∃ a b : Sym, (elementaryAbelianMaxJ (T : Subgroup G)).map q =
      (((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
        ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
          (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let P := relativeMaxOffenderImages (T : Subgroup G) U q
  let e := c.action.groupEquiv
  let j := Y.subtype.comp e.symm.toMonoidHom
  have hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker := by rwa [hker]
  have hp : IsStable α P := (lemma_B_2_10_relative U T hUT q hq hker hj).2.1
  have hPY (A) (hA : A ∈ P) : A ≤ Y := ((hp.2.1 A hA).le_offenderSubgroup α).trans hY
  have hstable : IsStable action {A | A.map j ∈ P} :=
    stable_family_on_symmetric_product α Y d c P hp hPY
  obtain ⟨g,hg₁,hg₂⟩ := hex
  have haxes := active_axes_in_layer Y e P hp.2.2.1 hstable g hg₁ hg₂
  obtain ⟨R,hR⟩ := (T.mapSurjective hq).exists_sylow_map_eq_inf_of_normal Y
  let R' : Sylow 2 (Sym × Sym) := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR' : (R' : Subgroup (Sym × Sym)).map j = (T : Subgroup G).map q ⊓ Y := by
    change ((R : Subgroup Y).map e.toMonoidHom).map j = _
    rw [map_map]
    have he : j.comp e.toMonoidHom = Y.subtype := by ext x; simp [j]
    rw [he]
    exact hR
  obtain ⟨a,b,hab⟩ := exists_sylow_marking hstable haxes.1 haxes.2 R'
  refine ⟨a,b,?_⟩
  rw [source_family_generated T U q hq,
    generated_on_layer Y e P hPY ((T : Subgroup G).map q) (R' : Subgroup _) hR',hab]

end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
