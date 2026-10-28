module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.Goldschmidt.MathieuNormalBase.Overlap
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.Goldschmidt.MathieuNormalBase.ModelProducts

/-!
# Exact normal-product data for the Mathieu extension

The original overlap homomorphism has the correct intersection with each
embedded inner endpoint. Its restriction to the residual overlap is the
original inner embedding, and its conjugation action on each normal endpoint
is prescribed by the marked residual isomorphism. These are exactly the
three hypotheses of normal-supplement gluing; none is an additional
recognition assumption. Source: Goldschmidt (1980), §3.8.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.MathieuNormalBase
open Subgroup Theory.GroupTheory RankTwoAmalgam Sporadic.Mathieu
open SourceAssembly.Goldschmidt ModelProducts
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

def ambientOverlapHom (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :
    ↥(F false ⊓ F true) →* MulAut M12 :=
  AutMathieuTwelve.autB.subtype.comp (overlapHom e)

theorem ambientOverlapHom_injective (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :
    Function.Injective (ambientOverlapHom e) :=
  AutMathieuTwelve.autB.subtype_injective.comp (overlapHom_injective h e)

def leftCoreEquiv (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :
    residualFamily F false ≃* innerP 0 :=
  e.left.trans ((MathieuTwelve.P 0).equivMapOfInjective MulAut.conj conj_injective)

def rightCoreEquiv (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :
    residualFamily F true ≃* innerP 1 :=
  e.right.trans ((MathieuTwelve.P 1).equivMapOfInjective MulAut.conj conj_injective)

theorem innerB_mem_iff (b : AutMathieuTwelve.autB) :
    (b : MulAut M12) ∈ innerB ↔ b ∈ MathieuExtensions.sourceInnerBorelEmbedding.range := by
  constructor
  · rintro ⟨x, hx, he⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    rw [MathieuExtensions.sourceInnerBorelEmbedding_apply]
    exact he
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, (MathieuExtensions.sourceInnerBorelEmbedding_apply x).symm⟩

theorem ambientOverlapHom_mem_innerP_iff (h : CubicTreeAction F)
    (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) (i : Fin 2)
    (t : ↥(F false ⊓ F true)) :
    ambientOverlapHom e t ∈ innerP i ↔ (t : G) ∈ pResidual 2 G := by
  have hb : ambientOverlapHom e t ∈ AutMathieuTwelve.autB := (overlapHom e t).property
  have hi : ambientOverlapHom e t ∈ innerP i ↔ ambientOverlapHom e t ∈ innerB := by
    rw [← innerP_inf_autB i]
    exact ⟨fun ha => ⟨ha, hb⟩, And.left⟩
  rw [hi]
  exact (innerB_mem_iff (overlapHom e t)).trans (overlapHom_mem_inner_iff h e t)

theorem ambientOverlapHom_base_left (e : Iso (baseAmalgam F) MathieuTwelve.amalgam)
    (s : ↥(residualFamily F false ⊓ residualFamily F true)) :
    ambientOverlapHom e (baseOverlapEmbedding F s) =
      (leftCoreEquiv e ((baseAmalgam F).left s) : MulAut M12) := by
  change (overlapHom e (baseOverlapEmbedding F s) : MulAut M12) =
    MulAut.conj (e.left ((baseAmalgam F).left s) : M12)
  rw [overlapHom_base, MathieuExtensions.sourceInnerBorelEmbedding_apply, e.left_commutes]
  rfl

theorem ambientOverlapHom_base_right (e : Iso (baseAmalgam F) MathieuTwelve.amalgam)
    (s : ↥(residualFamily F false ⊓ residualFamily F true)) :
    ambientOverlapHom e (baseOverlapEmbedding F s) =
      (rightCoreEquiv e ((baseAmalgam F).right s) : MulAut M12) := by
  change (overlapHom e (baseOverlapEmbedding F s) : MulAut M12) =
    MulAut.conj (e.right ((baseAmalgam F).right s) : M12)
  rw [overlapHom_base, MathieuExtensions.sourceInnerBorelEmbedding_apply, e.right_commutes]
  rfl

private theorem conj_automorphism (a : MulAut M12) (x : M12) :
    MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
  apply MulEquiv.ext
  intro y
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply,
    map_mul, map_inv, a.apply_symm_apply]

theorem leftCoreEquiv_conj (e : Iso (baseAmalgam F) MathieuTwelve.amalgam)
    (t : ↥(F false ⊓ F true)) (n : residualFamily F false) :
    (leftCoreEquiv e ((residualAmalgamAction F t).left n) : MulAut M12) =
      ambientOverlapHom e t * leftCoreEquiv e n * (ambientOverlapHom e t)⁻¹ := by
  change MulAut.conj (e.left ((residualAmalgamAction F t).left n) : M12) =
    ambientOverlapHom e t * MulAut.conj (e.left n : M12) * (ambientOverlapHom e t)⁻¹
  rw [← overlapHom_left e t n]
  exact conj_automorphism _ _

theorem rightCoreEquiv_conj (e : Iso (baseAmalgam F) MathieuTwelve.amalgam)
    (t : ↥(F false ⊓ F true)) (n : residualFamily F true) :
    (rightCoreEquiv e ((residualAmalgamAction F t).right n) : MulAut M12) =
      ambientOverlapHom e t * rightCoreEquiv e n * (ambientOverlapHom e t)⁻¹ := by
  change MulAut.conj (e.right ((residualAmalgamAction F t).right n) : M12) =
    ambientOverlapHom e t * MulAut.conj (e.right n : M12) * (ambientOverlapHom e t)⁻¹
  rw [← overlapHom_right e t n]
  exact conj_automorphism _ _

private theorem inner_range_map :
    MathieuExtensions.sourceInnerBorelEmbedding.range.map AutMathieuTwelve.autB.subtype =
      innerB := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (innerB_mem_iff b).mpr hb
  · intro hx
    let b : AutMathieuTwelve.autB := ⟨x, innerB_le_autB hx⟩
    exact ⟨b, (innerB_mem_iff b).mp hx, rfl⟩

theorem ambient_overlap_range_cases (e : Iso (baseAmalgam F) MathieuTwelve.amalgam) :
    (ambientOverlapHom e).range = innerB ∨
      (ambientOverlapHom e).range = AutMathieuTwelve.autB := by
  have hr : (ambientOverlapHom e).range =
      (overlapHom e).range.map AutMathieuTwelve.autB.subtype := MonoidHom.range_comp _ _
  rcases overlap_range_cases e with he | he
  · exact Or.inl (hr.trans (he ▸ inner_range_map))
  · right
    rw [hr, he, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end CFSG.Quasithin.ChapterF.GreenBook.Goldschmidt.MathieuNormalBase
