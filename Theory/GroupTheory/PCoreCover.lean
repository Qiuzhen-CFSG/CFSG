module
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Quotients of a subgroup covering the two-core quotient

If L = Y O₂(L), restriction of the quotient map is onto L/O₂(L).
Its kernel embeds in O₂(L); the trivial two-core of the target identifies
that kernel with O₂(Y). The resulting equivalence records its formula
on the original elements of Y.

The source consumer is the intersection residual in Aschbacher–Smith
4.2.12–13, printed pp.610–612.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A covering subgroup has the same two-core quotient, through its literal inclusion. -/
theorem exists_pCoreQuotientEquiv_of_cover {L Y : Subgroup G} (hYL : Y ≤ L)
    (hcover : (L : Set G) = (Y : Set G) * (L.pCoreIn 2 : Set G)) :
    ∃ e : (Y ⧸ pCore 2 Y) ≃* (L ⧸ pCore 2 L),
      ∀ y : Y, e (QuotientGroup.mk' (pCore 2 Y) y) =
        QuotientGroup.mk' (pCore 2 L) (inclusion hYL y) := by
  let f : Y →* L ⧸ pCore 2 L := (QuotientGroup.mk' (pCore 2 L)).comp (inclusion hYL)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    obtain ⟨y,hy,c,hc,he⟩ := hcover ▸ (show l.val ∈ (L : Set G) from l.property)
    refine ⟨⟨y,hy⟩,QuotientGroup.eq.mpr ?_⟩
    obtain ⟨c',hc',hec⟩ := hc
    have heq : (⟨y,hYL hy⟩ : L)⁻¹ * l = c' := by
      apply Subtype.ext
      change y⁻¹ * l.val = c'.val
      rw [←he,←hec]
      simp
    change (⟨y,hYL hy⟩ : L)⁻¹ * l ∈ pCore 2 L
    rwa [heq]
  let j : f.ker →* pCore 2 L :=
    { toFun := fun x => ⟨⟨x.val.val,hYL x.val.property⟩,
        (QuotientGroup.eq_one_iff _).mp x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 L => z.val.val) he))
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.of_injective j hj
  have hker : f.ker = pCore 2 Y := by
    have hh := f.comap_pCore_of_ker_isPGroup hf hk
    simpa only [pCore_quotient_pCore_eq_bot,MonoidHom.comap_bot] using hh
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf),fun _ => rfl⟩
end Theory.GroupTheory
