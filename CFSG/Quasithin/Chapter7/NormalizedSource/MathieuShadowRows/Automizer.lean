module
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M22.MarkedActions
public import Theory.Representation.BinaryNormalExtension
public import Theory.Representation.BinaryOffender.SylowTransport

/-!
# Extending the simple M22 marking to a normal overgroup

A faithful binary action containing a normal marked M22 has the same code or
cocode coordinates on its whole actor. Absolute irreducibility makes the
linear centralizer trivial, so the native extension to Aut(M22) implements
every ambient conjugation. Faithfulness then makes the resulting map into
the setwise pair stabilizer injective. Both the inner preimage and the two
possible full images are retained.

This is the action transport needed before applying H.14--H.15 to the full
automizer in the original 8.1.3 and 8.2.2 arguments, printed pp.713--715 of
Aschbacher--Smith, refs/quasithin.pdf. It does not assert either exclusion.
-/

public noncomputable section
open Subgroup Representation Sporadic.Mathieu MathieuCode
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source

/-- The same component coordinates intertwine every ambient actor, and the
preimage of the native inner group is exactly the original normal subgroup. -/
theorem normal_m22_marking
    {H W U : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    [Nontrivial U]
    (ρ : Representation (ZMod 2) H W) (hρ : Function.Injective ρ)
    (J : Subgroup H) [J.Normal] (e : J ≃* M22)
    (σ : Representation (ZMod 2) M22 U) [σ.IsIrreducible]
    [σ.IsAbsolutelyIrreducible]
    (τ : Representation (ZMod 2) MathieuCode.m22PairStabilizer U)
    (hτ : τ.comp m22ToPairStabilizer = σ)
    (E : W ≃ₗ[ZMod 2] U)
    (hE : ∀ j : J, ∀ w, E (ρ j w) = σ (e j) (E w)) :
    ∃ a : H →* MathieuCode.m22PairStabilizer, Function.Injective a ∧
      (∀ b w, E (ρ b w) = τ (a b) (E w)) ∧
      (∀ j : J, a j = m22ToPairStabilizer (e j)) ∧
      m22ToPairStabilizer.range.comap a = J ∧
      (a.range = m22ToPairStabilizer.range ∨ a.range = ⊤) := by
  let a := simpleAmbientPairHom J e inferInstance
  have ha (b : H) (w : W) : E (ρ b w) = τ (a b) (E w) := by
    apply BinaryNormalExtension.equivariant ρ J σ
      (τ.comp MathieuCode.m22PairStabilizerEquivAut.symm.toMonoidHom) _
      (BinaryNormalExtension.centralizer_eq_one_of_absolutelyIrreducible σ) e E hE
    apply MonoidHom.ext
    intro g
    have hg : MathieuCode.m22PairStabilizerEquivAut.symm (MulAut.conj g) =
        m22ToPairStabilizer g := by
      apply MathieuCode.m22PairStabilizerEquivAut.injective
      simp
    change τ (m22PairStabilizerEquivAut.symm (MulAut.conj g)) = σ g
    rw [hg]
    exact congrArg (fun r : Representation (ZMod 2) M22 U => r g) hτ
  have hi : Function.Injective a := by
    intro b c hbc
    apply hρ
    ext w
    apply E.injective
    rw [ha, ha, hbc]
  refine ⟨a, hi, ha, simpleAmbientPairHom_on_component e inferInstance, ?_,
    simpleAmbientPairHom_range_cases e inferInstance⟩
  rw [← simpleAmbientPairHom_component_image e (inferInstance : J.Normal)]
  ext x
  constructor
  · rintro ⟨y,hy,he⟩
    exact hi he ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

/-- A surjective covering action descends to a normal marked M22 inside the
whole actor. The original cover map is retained in the intertwining formula. -/
theorem covered_normal_m22_marking
    {H K W U : Type*} [Group H] [Group K]
    [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    [Nontrivial U]
    (ρ : Representation (ZMod 2) H W) (hρ : Function.Injective ρ)
    (σ : Representation (ZMod 2) M22 U) (hσ : Function.Injective σ)
    [σ.IsIrreducible] [σ.IsAbsolutelyIrreducible]
    (τ : Representation (ZMod 2) MathieuCode.m22PairStabilizer U)
    (hτ : τ.comp m22ToPairStabilizer = σ)
    (k : K →* H) [k.range.Normal] (J : Subgroup H) (hJ : k.range = J)
    (q : K →* M22) (hq : Function.Surjective q)
    (E : W ≃ₗ[ZMod 2] U)
    (hcomponent : ∀ l v, E (ρ (k l) v) = σ (q l) (E v)) :
    ∃ a : H →* MathieuCode.m22PairStabilizer, Function.Injective a ∧
      (∀ b v, E (ρ b v) = τ (a b) (E v)) ∧
      (∀ l, a (k l) = m22ToPairStabilizer (q l)) ∧
      m22ToPairStabilizer.range.comap a = J ∧
      (a.range = m22ToPairStabilizer.range ∨ a.range = ⊤) := by
  obtain ⟨f,hfi,hf,hfq⟩ := BinaryOffender.faithful_action_factor σ ρ
    hσ hρ q hq k E.symm (by
      intro l u
      apply E.injective
      rw [E.apply_symm_apply,hcomponent,E.apply_symm_apply])
  have hrange : f.range = k.range := by
    have hc : f.comp q = k := MonoidHom.ext hfq
    rw [←hc,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hq,←MonoidHom.range_eq_map]
  let : f.range.Normal := hrange ▸ inferInstance
  let e : f.range ≃* M22 := (f.ofInjective hfi).symm
  have he (j : f.range) (v : W) :
      E (ρ j v) = σ (e j) (E v) := by
    have hj : f (e j) = j := congrArg Subtype.val ((f.ofInjective hfi).apply_symm_apply j)
    rw [←hj]
    have hh := congrArg E (hf (e j) (E v))
    simpa only [E.apply_symm_apply,E.symm_apply_apply] using hh.symm
  obtain ⟨a,hai,ha,haj,hinner,himage⟩ := normal_m22_marking
    ρ hρ
      f.range e σ τ hτ E he
  refine ⟨a,hai,ha,?_,hinner.trans (hrange.trans hJ),himage⟩
  intro l
  have hh := haj ((f.ofInjective hfi) (q l))
  change a (f (q l)) = m22ToPairStabilizer (e ((f.ofInjective hfi) (q l))) at hh
  rw [hfq] at hh
  simpa only [e,MulEquiv.symm_apply_apply] using hh

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows
