module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.Matching
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.NativeCore
public import Theory.SpecificGroups.ReeF4.SmallCompletion.Weyl
public import Theory.GroupTheory.Simple

/-!
# Full Ree extension recognition conditional on the marked Weyl relation

The model relation holds for the actual orbit words. If those same marked
words have eighth-power relation in the supplied completion, the paired
comparison identifies the full extension carrier. Its inclusion into the
native automorphism group gives a faithful type-preserving action containing
all inner automorphisms. A simple completion is then the native group.

The relation remains an explicit local algebraic premise. Deriving it from
the order bound is the unresolved Cartan/apartment step; these conditional
results are not asserted to complete F.4.17 or F.4.24.
Source: Aschbacher–Smith F.4.10,16–17, pp.279,282–283.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
open Subgroup Theory.GroupTheory ReeF4.Parabolics

variable {m : ℕ} (E : SourceExtension m)

/-- The actual linear orbit word in the full left endpoint. -/
def leftReflection : E.left := nativeLeftLocal E (ReeF4.SmallCompletion.reflection m .linear)

/-- The actual Suzuki orbit word in the full right endpoint. -/
def rightReflection : E.right := nativeRightLocal E (ReeF4.SmallCompletion.reflection m .suzuki)

theorem leftReflection_sq : leftReflection E ^ 2 = 1 := by
  rw [leftReflection,←map_pow,ReeF4.SmallCompletion.reflection_sq,map_one]

theorem rightReflection_sq : rightReflection E ^ 2 = 1 := by
  rw [rightReflection,←map_pow,ReeF4.SmallCompletion.reflection_sq,map_one]

private theorem native_generate : parabolic m .linear ⊔ parabolic m .suzuki = ⊤ := by
  rw [sup_comm]
  exact GreenBook.LieModels.ReeFour.parabolics_generate m

/-- The concrete full-extension inclusion completion. -/
def modelCompletion : Completion E E.carrier := E.completion (by
  rw [sup_comm]
  exact GreenBook.LieModels.ReeFour.parabolics_generate m)

theorem modelCompletion_overlap :
    (modelCompletion E).left.range ⊓ (modelCompletion E).right.range =
      (modelCompletion E).middle.range := E.completion_overlap (native_generate (m := m))

variable {M : Type*} [Group M] (c : Completion E M)

/-- The product of the two native marked reflections in this completion. -/
def weylProduct : M := c.left (leftReflection E) * c.right (rightReflection E)

/-- The full model carrier retains the actual native eighth-power relation. -/
theorem modelCompletion_weylProduct_eight : weylProduct E (modelCompletion E)^8 = 1 := by
  apply Subtype.ext
  change (MulAut.conj (ReeF4.SmallCompletion.reflection m .linear).val *
    MulAut.conj (ReeF4.SmallCompletion.reflection m .suzuki).val)^8 = 1
  rw [←map_mul,←map_pow,ReeF4.SmallCompletion.reflection_product_eight,map_one]

private theorem leftReflection_out (hm : 0 < m) :
    c.left (leftReflection E) ∉ c.middle.range := by
  rintro ⟨b,hb⟩
  have he := congrArg Subtype.val (c.left_injective hb)
  change b.val = MulAut.conj (ReeF4.SmallCompletion.reflection m .linear).val at he
  have hr := (E.conj_mem_right_iff (ReeF4.SmallCompletion.conj_injective m hm) _).mp
    (he ▸ b.property.2)
  apply ReeF4.SmallCompletion.reflection_not_mem_borel m .linear
  have ho : parabolic m .linear ⊓ parabolic m .suzuki = borel m := by
    rw [inf_comm]
    exact GreenBook.LieModels.ReeFour.overlap m
  exact ho ▸ ⟨(ReeF4.SmallCompletion.reflection m .linear).property,hr⟩

private theorem rightReflection_out (hm : 0 < m) :
    c.right (rightReflection E) ∉ c.middle.range := by
  rintro ⟨b,hb⟩
  have he := congrArg Subtype.val (c.right_injective
    ((DFunLike.congr_fun c.compatible b).symm.trans hb))
  change b.val = MulAut.conj (ReeF4.SmallCompletion.reflection m .suzuki).val at he
  have hl := (E.conj_mem_left_iff (ReeF4.SmallCompletion.conj_injective m hm) _).mp
    (he ▸ b.property.1)
  apply ReeF4.SmallCompletion.reflection_not_mem_borel m .suzuki
  have ho : parabolic m .linear ⊓ parabolic m .suzuki = borel m := by
    rw [inf_comm]
    exact GreenBook.LieModels.ReeFour.overlap m
  exact ho ▸ ⟨hl,(ReeF4.SmallCompletion.reflection m .suzuki).property⟩

/-- Recognition from the literal marked relation, not from an unmarked
apartment or merely equal orders. No finiteness assumption is required. -/
theorem nonempty_mulEquiv_of_weyl_relation (hm : 0 < m)
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hw : weylProduct E c ^ 8 = 1) : Nonempty (M ≃* E.carrier) :=
  nonempty_mulEquiv_of_matching_involutions E c hm (modelCompletion E)
    hc (modelCompletion_overlap E) (leftReflection E) (rightReflection E)
    (leftReflection_sq E) (rightReflection_sq E)
    (leftReflection_out E c hm) (rightReflection_out E c hm)
    hw (modelCompletion_weylProduct_eight E)

/-- The conditional recognizer supplies the requested actual faithful action,
all native inner automorphisms, type preservation, and full order equality. -/
theorem faithful_extension_of_weyl_relation (hm : 0 < m)
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hw : weylProduct E c ^ 8 = 1) :
    Nat.card M = Nat.card E.carrier ∧
      ∃ a : M →* MulAut (ReeF4.Model m), Function.Injective a ∧
        (MulAut.conj : ReeF4.Model m →* MulAut (ReeF4.Model m)).range ≤ a.range ∧
        ∀ g : M, UnitaryNonbinary.PreservesTypes
          (parabolic m .linear) (parabolic m .suzuki) (a g) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_weyl_relation E c hm hc hw
  let a := E.carrier.subtype.comp e.toMonoidHom
  refine ⟨Nat.card_congr e.toEquiv,a,E.carrier.subtype_injective.comp e.injective,?_,?_⟩
  · intro f hf
    obtain ⟨g,hg⟩ := e.surjective ⟨f,E.contains_inner hf⟩
    exact ⟨g,congrArg Subtype.val hg⟩
  · intro g
    exact E.preserves_types _ (e g).property

/-- Ambient simplicity removes the outer part after conditional recognition;
no separate native simplicity theorem is assumed. -/
theorem nonempty_native_mulEquiv_of_simple_of_weyl_relation [IsSimpleGroup M]
    (hm : 0 < m) (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hw : weylProduct E c ^ 8 = 1) : Nonempty (M ≃* ReeF4.Model m) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_weyl_relation E c hm hc hw
  let : IsSimpleGroup E.carrier := e.symm.isSimpleGroup
  let I := (MulAut.innerSubgroup (ReeF4.Model m)).comap E.carrier.subtype
  have hr : E.baseHom.range = I := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨b,rfl⟩
    · rintro ⟨b,hb⟩
      exact ⟨b,Subtype.ext hb⟩
  have htop : I = ⊤ := (inferInstance : I.Normal).eq_bot_or_eq_top.resolve_left (by
    intro hi
    let w := (ReeF4.SmallCompletion.reflection m .linear).val
    have hmem : E.baseHom w ∈ I := hr ▸ (show E.baseHom w ∈ E.baseHom.range from ⟨w,rfl⟩)
    have hone : E.baseHom w = 1 := mem_bot.mp (hi ▸ hmem)
    have hw1 : w=1 := E.baseHom_injective (ReeF4.SmallCompletion.conj_injective m hm)
      (hone.trans (map_one E.baseHom).symm)
    apply ReeF4.SmallCompletion.reflection_not_mem_borel m .linear
    change w ∈ borel m
    rw [hw1]
    exact (borel m).one_mem)
  have hsurj : Function.Surjective E.baseHom := MonoidHom.range_eq_top.mp (hr.trans htop)
  exact ⟨e.trans (MulEquiv.ofBijective E.baseHom
    ⟨E.baseHom_injective (ReeF4.SmallCompletion.conj_injective m hm),hsurj⟩).symm⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
