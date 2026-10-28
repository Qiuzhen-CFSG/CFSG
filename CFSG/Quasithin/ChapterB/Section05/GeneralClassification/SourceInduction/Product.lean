module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import Theory.GroupTheory.PCoreProduct

/-!
# The actual factor and cover maps for cardinal descent

An internal product determines the projection with kernel the other original
subgroup. Thus each factor is normal, and deleting a nontrivial factor strictly
reduces group order. The second factor inherits a trivial two-core. Its SQTK
cover is the inverse image under the original quotient projection; arbitrary
SQTK quotient inheritance is not used.

These are the group-theoretic descent steps at B.5.8 and B.5.11 in
Aschbacher–Smith, combined 1 March 2004 manuscript, printed pp.106 and 109.
The representation hypotheses are supplied in the separate descent module.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D : Type*} [Group D]
namespace InternalProduct
variable {A B : Subgroup D} (h : InternalProduct A B)

/-- The first projection retains the original product coordinates. -/
def fst : D →* A := (MonoidHom.fst A B).comp h.equiv.symm.toMonoidHom

/-- The second projection retains the original product coordinates. -/
def snd : D →* B := (MonoidHom.snd A B).comp h.equiv.symm.toMonoidHom

include h

theorem exists_mul (g : D) : ∃ (a : A) (b : B), g = (a : D) * (b : D) := by
  obtain ⟨⟨a,b⟩, rfl⟩ := h.equiv.surjective g
  exact ⟨a,b,h.apply_eq a b⟩

theorem sup_eq_top : A ⊔ B = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨a,b,rfl⟩ := h.exists_mul g
  exact (A ⊔ B).mul_mem ((le_sup_left : A ≤ A ⊔ B) a.property) ((le_sup_right : B ≤ A ⊔ B) b.property)

theorem fst_apply (a : A) (b : B) : h.fst ((a : D) * (b : D)) = a := by
  rw [← h.apply_eq]
  exact congrArg Prod.fst (h.equiv.symm_apply_apply (a,b))

theorem ker_fst : h.fst.ker = B := by
  ext g
  obtain ⟨a,b,rfl⟩ := h.exists_mul g
  change h.fst ((a : D) * (b : D)) = 1 ↔ (a : D) * (b : D) ∈ B
  rw [h.fst_apply]
  constructor
  · rintro rfl
    simp
  · intro hab
    let c : B := ⟨(a : D) * (b : D), hab⟩
    have he : h.equiv (a,b) = h.equiv (1,c) := by
      simp only [h.apply_eq, OneMemClass.coe_one, one_mul, c]
    exact congrArg Prod.fst (h.equiv.injective he)

theorem second_normal : B.Normal := by
  rw [← h.ker_fst]
  infer_instance

theorem card_eq [Finite D] : Nat.card D = Nat.card A * Nat.card B := by
  rw [← Nat.card_congr h.equiv.toEquiv, Nat.card_prod]

/-- The strict decrease used for both recursive classifications. -/
theorem second_card_lt [Finite D] (hA : A ≠ ⊥) : Nat.card B < Nat.card D := by
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA
  rw [h.card_eq]
  simpa only [one_mul] using
    Nat.mul_lt_mul_of_pos_right (Finite.one_lt_card (α := A)) (Nat.card_pos (α := B))

theorem second_twoCore [Finite D] (hD : pCore 2 D = ⊥) : pCore 2 B = ⊥ := by
  let : B.Normal := h.second_normal
  have hle : (pCore 2 B).map B.subtype ≤ pCore 2 D :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map B.subtype⟩
  rw [hD] at hle
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro b hb
  apply Subtype.ext
  exact hle (Subgroup.mem_map_of_mem B.subtype hb)
end InternalProduct

namespace SQTKQuotient
universe u
variable {K : GroupClass.{u}} {D : Type u} [Group D]

def projection (h : SQTKQuotient K D) : h.Cover →* D :=
  h.equiv.toMonoidHom.comp (QuotientGroup.mk' h.kernel)

theorem projection_surjective (h : SQTKQuotient K D) : Function.Surjective h.projection :=
  h.equiv.surjective.comp (QuotientGroup.mk'_surjective h.kernel)

/-- Pull back the subgroup along the original SQTK quotient map. -/
noncomputable def subgroup (h : SQTKQuotient K D) (B : Subgroup D) : SQTKQuotient K B where
  Cover := B.comap h.projection
  kernel := (h.projection.subgroupComap B).ker
  sqtk := h.sqtk.subgroup _
  equiv := QuotientGroup.quotientKerEquivOfSurjective _
    (h.projection.subgroupComap_surjective_of_surjective B h.projection_surjective)
end SQTKQuotient


end CFSG.Quasithin.ChapterB.SourceInduction
