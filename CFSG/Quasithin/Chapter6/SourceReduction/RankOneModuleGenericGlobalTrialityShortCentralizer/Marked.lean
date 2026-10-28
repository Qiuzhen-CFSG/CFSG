module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityShortCentralizer.Containment

/-!
# The full marked ambient short-root centralizer

F.4.42 identifies the ambient short centralizer with its local intersection
in N_G(L). The unchanged whole-normalizer map therefore restricts to an
isomorphism onto the entire short centralizer in the same constructed
extension. Its pointwise equation and pinned-root equation retain the
original reversed amalgam comparison and the chosen marking.

Source: Aschbacher--Smith F.4.42, printed p.295; this is the short-side
centralizer correspondence needed by F.4.43 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.TrialityNonbinary TrialityCompletionFusion

private theorem centralizer_equiv {G E : Type*} [Group G] [Group E]
    (N : Subgroup G) (f : N →* E) (hf : Function.Injective f)
    (t : G) (ht : t ∈ N) (v : E) (hv : f ⟨t,ht⟩ = v)
    (hC : centralizer ({t} : Set G) ≤ N)
    (hD : centralizer ({v} : Set E) ≤ f.range) :
    ∃ k : centralizer ({t} : Set G) ≃* centralizer ({v} : Set E),
      (∀ x, (k x).val = f (inclusion hC x)) ∧
      k ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ =
        ⟨v,mem_centralizer_singleton_iff.mpr rfl⟩ := by
  let F : centralizer ({t} : Set G) →* centralizer ({v} : Set E) := {
    toFun x := ⟨f (inclusion hC x),mem_centralizer_singleton_iff.mpr (by
      rw [←hv,←map_mul,←map_mul]
      exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp x.property)))⟩
    map_one' := by apply Subtype.ext; exact map_one f
    map_mul' x y := by apply Subtype.ext; exact (f.comp (inclusion hC)).map_mul x y }
  have hFi : Function.Injective F := by
    intro x y he
    exact inclusion_injective hC (hf (congrArg Subtype.val he))
  have hFs : Function.Surjective F := by
    intro x
    obtain ⟨y,hy⟩ := hD x.property
    have hyC : y.val ∈ centralizer ({t} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      apply congrArg Subtype.val (hf (show f (y*⟨t,ht⟩) = f (⟨t,ht⟩*y) from ?_))
      simpa only [map_mul,hv,hy] using mem_centralizer_singleton_iff.mp x.property
    exact ⟨⟨y.val,hyC⟩,Subtype.ext hy⟩
  refine ⟨MulEquiv.ofBijective F ⟨hFi,hFs⟩,fun _ => rfl,?_⟩
  exact Subtype.ext hv

variable {G : Type*} [Group G] [Finite G]
theorem Preparation.triality_short_centralizer_full_marked
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (nativeAmalgam m hm).reverse)
    (a : TrialityNormalizerMarking L (residual H) (sourceS L H) m hm e) :
    let P := binaryParameters m hm
    let t := (e.right.symm (shortElement P rfl)).val
    ∃ ht : centralizer ({t} : Set G) ≤ normalizer (L : Set G),
      ∃ k : centralizer ({t} : Set G) ≃* centralizer
          ({a.extension.baseHom (shortElement P rfl).val} : Set a.extension.carrier),
        (∀ x, (k x).val = inclusion a.extension.right_le
          (a.comparison.left (inclusion ht x))) ∧
        k ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ =
          ⟨a.extension.baseHom (shortElement P rfl).val,
            mem_centralizer_singleton_iff.mpr rfl⟩ := by
  let P := binaryParameters m hm
  let t := (e.right.symm (shortElement P rfl)).val
  let f := (inclusion a.extension.right_le).comp a.comparison.left.toMonoidHom
  have hC := d.triality_short_centralizer_le_normalizer h hH hp m hm e
  obtain ⟨v,hv,_,he,hN⟩ := d.triality_short_marker_left h hH hp m hm e
  have hmark : f ⟨t,hN⟩ = a.extension.baseHom (shortElement P rfl).val := by
    apply Subtype.ext
    have ht : (⟨t,hN⟩ : normalizer (L : Set G)) =
        inclusion a.left_le (e.left.symm v) := Subtype.ext he
    change (a.comparison.left _).val = _
    rw [ht,a.left_marked,e.left.apply_symm_apply,hv]
    rfl
  have hm2 := (d.triality_local_structure h hH.1.1.2 hp m hm e).2.1
  have hD : centralizer ({a.extension.baseHom (shortElement P rfl).val} :
      Set a.extension.carrier) ≤ f.range := by
    intro x hx
    have hxR := TrialityShortExtension.short_centralizer_le_right hm2 a.extension 1 one_ne_zero hx
    refine ⟨a.comparison.left.symm ⟨x.val,hxR⟩,?_⟩
    exact congrArg (inclusion a.extension.right_le)
      (a.comparison.left.apply_symm_apply ⟨x.val,hxR⟩)
  exact ⟨hC,centralizer_equiv _ f
    ((inclusion_injective a.extension.right_le).comp a.comparison.left.injective)
    t hN _ hmark hC hD⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
