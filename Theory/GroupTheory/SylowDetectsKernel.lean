module

public import Mathlib.GroupTheory.Sylow

/-!
# Detecting a p-group kernel on a Sylow subgroup

Let f : N → A and q : A → B be group homomorphisms, with N finite and p
prime. If the kernel of q is a p-group, then q is injective on the image
of f whenever its kernel is trivial on the image of a Sylow p-subgroup
of N. No finiteness assumption on A or B is needed.

The kernel of the restriction of q to f(N) embeds in the kernel of q.
It is therefore a normal p-subgroup of f(N), so lies in the Sylow image
of the chosen Sylow subgroup. The local hypothesis makes that kernel
trivial, proving injectivity.

This is the abstract normal-kernel argument in the U and V automizer
calculations of Alperin–Brauer–Gorenstein, Chapter II §1 Proposition 2,
article p.12. It is independent of the classification hypotheses.
-/

namespace Sylow

/-- A p-group kernel is detected on the image of a Sylow p-subgroup. -/
public theorem injective_on_range_of_isPGroup_kernel
    {N A B : Type*} [Group N] [Finite N] [Group A] [Group B]
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p N) (f : N →* A) (q : A →* B) (hker : IsPGroup p q.ker)
    (hlocal : ∀ s : S, q (f s) = 1 → f s = 1) :
    Function.Injective (q.comp f.range.subtype) := by
  let R := f.range
  let r : R →* B := q.comp R.subtype
  have hk : IsPGroup p r.ker := by
    let i : r.ker →* q.ker :=
      { toFun x := ⟨x.val.val, x.property⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
    apply hker.of_injective i
    intro x y h
    have hval : x.val.val = y.val.val := congrArg (fun z : q.ker => z.val) h
    exact Subtype.ext (Subtype.ext hval)
  let P := S.mapSurjective f.rangeRestrict_surjective
  have hle : r.ker ≤ P := hk.le_sylow_of_normal P
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨s, hs, hfs⟩ := hle hx
  have hh : q (f s) = 1 := by
    have hval := congrArg Subtype.val hfs
    change q x.val = 1 at hx
    rwa [← hval] at hx
  have hsone := hlocal ⟨s, hs⟩ hh
  apply Subtype.ext
  exact (congrArg Subtype.val hfs).symm.trans hsone

end Sylow
