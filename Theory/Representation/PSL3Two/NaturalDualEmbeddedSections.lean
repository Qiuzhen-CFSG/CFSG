module
public import Theory.Representation.BinaryConjugationSection.EmbeddedSection
public import Theory.Representation.PSL3Two.NaturalDualNonFF

/-!
# Natural and dual subgroups from one marked component support

The two coordinate injections in the natural--dual pair are equivariant
for every inner actor. Pulling their ranges back under the original section
map constructs the actual natural and dual subgroups with the same central
kernel. No new representation or independent support is chosen.
Source: Aschbacher--Smith 14.6.22 and 14.6.24(3), printed pp.1038--1041.
-/

public noncomputable section
open Subgroup Representation
namespace BinaryLinearThree.NaturalDual
variable {G E : Type*} [_root_.Group G] [AddCommGroup E] [Module (ZMod 2) E]
  {H U Z A : Subgroup G} {ρ : Representation (ZMod 2) H E}

/-- The two original three-spaces lift to literal section subgroups. Both
coordinates are restrictions of the same given coordinate quotient. -/
theorem exists_natural_dual_sections
    (c : BinaryConjugationSection H U Z ρ)
    (α : H →* MulAut Group) (e : Space →ₗ[ZMod 2] E) (hi : Function.Injective e)
    (he : ∀ a v, ρ a (e v) = e (autAction (α a) v))
    (hAH : A ≤ H) (hUA : U ≤ A) (f : A →* Group)
    (hf : ∀ a, MulAut.conj (f a) = α (inclusion hAH a)) :
    ∃ Wn Wd : Subgroup G, Wn ≤ U ∧ Wd ≤ U ∧
      Nonempty (BinaryConjugationSection A Wn Z (W.comp f)) ∧
      Nonempty (BinaryConjugationSection A Wd Z (W.dual.comp f)) ∧
      c.imageSpace Wn = (e.comp (LinearMap.inl _ Vector (Module.Dual (ZMod 2) Vector))).range ∧
      c.imageSpace Wd = (e.comp (LinearMap.inr _ Vector (Module.Dual (ZMod 2) Vector))).range := by
  let d := c.restrictActor hAH hUA
  let en := e.comp (LinearMap.inl (ZMod 2) Vector (Module.Dual (ZMod 2) Vector))
  let ed := e.comp (LinearMap.inr (ZMod 2) Vector (Module.Dual (ZMod 2) Vector))
  have hn : Function.Injective en := hi.comp (fun _ _ hh => congrArg Prod.fst hh)
  have hd : Function.Injective ed := hi.comp (fun _ _ hh => congrArg Prod.snd hh)
  have hen (a : A) (v : Vector) : (ρ.comp (inclusion hAH)) a (en v) = en ((W.comp f) a v) := by
    change ρ (inclusion hAH a) (e (v,0)) = e (W (f a) v,0)
    rw [he,←hf,autAction_inner]
    change e (W (f a) v,W.dual (f a) 0) = e (W (f a) v,0)
    rw [map_zero]
  have hed (a : A) (v : Module.Dual (ZMod 2) Vector) :
      (ρ.comp (inclusion hAH)) a (ed v) = ed ((W.dual.comp f) a v) := by
    change ρ (inclusion hAH a) (e (0,v)) = e (0,W.dual (f a) v)
    rw [he,←hf,autAction_inner]
    change e (W (f a) 0,W.dual (f a) v) = e (0,W.dual (f a) v)
    rw [map_zero]
  let P := BinaryConjugationSection.embeddedSubrepresentation (W.comp f) en hen
  let Q := BinaryConjugationSection.embeddedSubrepresentation (W.dual.comp f) ed hed
  refine ⟨d.invariantPreimage P,d.invariantPreimage Q,d.invariantPreimage_le P,
    d.invariantPreimage_le Q,⟨d.embeddedSection _ en hn hen⟩,
    ⟨d.embeddedSection _ ed hd hed⟩,?_,?_⟩
  · exact d.imageSpace_embeddedPreimage (W.comp f) en hen
  · exact d.imageSpace_embeddedPreimage (W.dual.comp f) ed hed

end BinaryLinearThree.NaturalDual
