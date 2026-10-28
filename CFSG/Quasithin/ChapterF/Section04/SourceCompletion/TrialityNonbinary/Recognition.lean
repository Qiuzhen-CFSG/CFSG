module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.Matching
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.NativeCore
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.WeylAction
public import Theory.GroupTheory.Simple

/-!
# Marked recognition of small nonbinary triality extensions

The full extension order bound closes the marked native apartment, including
its Cartan defect. Pairing with the concrete model then identifies both
endpoint maps and hence the whole extension. Inclusion in the native
automorphism group supplies the faithful type-preserving action; ambient
simplicity removes the outer part. No Weyl or recognition premise remains.

Source: Aschbacher--Smith F.4.10,16--17,24, pp.279,282--283,287--288.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
open Subgroup Theory.GroupTheory
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat

variable {m : ℕ} {hm : 0 < m} (E : SourceExtension m hm)

/-- The actual arms orbit word in the full left endpoint. -/
def leftReflection : E.left := E.nativeLeft (reflection m hm .arms)

/-- The actual central orbit word in the full right endpoint. -/
def rightReflection : E.right := E.nativeRight (reflection m hm .central)

theorem leftReflection_sq : leftReflection E ^ 2 = 1 := by
  rw [leftReflection,←map_pow,reflection_sq,map_one]

theorem rightReflection_sq : rightReflection E ^ 2 = 1 := by
  rw [rightReflection,←map_pow,reflection_sq,map_one]

/-- The actual full-extension inclusion completion. -/
def modelCompletion : Completion E E.carrier := E.completion (native_generate m hm)

theorem modelCompletion_overlap :
    (modelCompletion E).left.range ⊓ (modelCompletion E).right.range =
      (modelCompletion E).middle.range := E.completion_overlap (native_generate m hm)

variable {M : Type*} [Group M] (c : Completion E M)

/-- The product of the two native marked reflections in this completion. -/
def weylProduct : M := c.left (leftReflection E) * c.right (rightReflection E)

/-- The full model carrier retains the actual native sixth-power relation. -/
theorem modelCompletion_weylProduct_six : weylProduct E (modelCompletion E)^6 = 1 := by
  apply Subtype.ext
  change (MulAut.conj (reflection m hm .arms).val *
    MulAut.conj (reflection m hm .central).val)^6 = 1
  rw [←map_mul,←map_pow]
  have hpow : ((reflection m hm .arms).val*(reflection m hm .central).val)^6=1 := by
    change (simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) .arms *
      simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) .central)^6=1
    rw [←orderOf_simpleProduct (binaryParameters m hm) (binaryParameters_prime m hm)]
    exact pow_orderOf_eq_one _
  rw [hpow,map_one]

private theorem leftReflection_out :
    c.left (leftReflection E) ∉ c.middle.range := by
  rintro ⟨b,hb⟩
  have he := congrArg Subtype.val (c.left_injective hb)
  change b.val = MulAut.conj (reflection m hm .arms).val at he
  have hr := (E.conj_mem_right_iff (conj_injective m hm) _).mp
    (he ▸ b.property.2)
  apply reflection_not_mem_borel m hm .arms
  have ho : parabolic (binaryParameters m hm) .arms ⊓ parabolic (binaryParameters m hm) .central = borel (binaryParameters m hm) := by
    exact parabolic_inf_binary (binaryParameters m hm) (binaryParameters_prime m hm)
  exact ho ▸ ⟨(reflection m hm .arms).property,hr⟩

private theorem rightReflection_out :
    c.right (rightReflection E) ∉ c.middle.range := by
  rintro ⟨b,hb⟩
  have he := congrArg Subtype.val (c.right_injective
    ((DFunLike.congr_fun c.compatible b).symm.trans hb))
  change b.val = MulAut.conj (reflection m hm .central).val at he
  have hl := (E.conj_mem_left_iff (conj_injective m hm) _).mp
    (he ▸ b.property.1)
  apply reflection_not_mem_borel m hm .central
  have ho : parabolic (binaryParameters m hm) .arms ⊓ parabolic (binaryParameters m hm) .central = borel (binaryParameters m hm) := by
    exact parabolic_inf_binary (binaryParameters m hm) (binaryParameters_prime m hm)
  exact ho ▸ ⟨hl,(reflection m hm .central).property⟩

/-- The full order bound yields an isomorphism retaining both endpoint markings. -/
theorem exists_marked_mulEquiv_of_card_le [Finite M] (hm2 : 1 < m)
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    ∃ f : M ≃* E.carrier,
      (∀ x, f (c.left x) = (modelCompletion E).left x) ∧
      (∀ x, f (c.right x) = (modelCompletion E).right x) :=
  exists_mulEquiv_of_matching_involutions E c (modelCompletion E)
    hc (modelCompletion_overlap E) (leftReflection E) (rightReflection E)
    (leftReflection_sq E) (rightReflection_sq E)
    (leftReflection_out E c) (rightReflection_out E c)
    (marked_six_eq_one E c hm2 hc horder) (modelCompletion_weylProduct_six E)

/-- The conditional recognizer supplies the requested actual faithful action,
all native inner automorphisms, type preservation, and full order equality. -/
theorem faithful_extension_of_card_le [Finite M] (hm2 : 1 < m)
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    Nat.card M = Nat.card E.carrier ∧
      ∃ a : M →* MulAut (BinaryCarrier m hm), Function.Injective a ∧
        (MulAut.conj : BinaryCarrier m hm →* MulAut (BinaryCarrier m hm)).range ≤ a.range ∧
        ∀ g : M, UnitaryNonbinary.PreservesTypes
          (parabolic (binaryParameters m hm) .arms) (parabolic (binaryParameters m hm) .central) (a g) := by
  obtain ⟨e,_,_⟩ := exists_marked_mulEquiv_of_card_le E c hm2 hc horder
  let a := E.carrier.subtype.comp e.toMonoidHom
  refine ⟨Nat.card_congr e.toEquiv,a,E.carrier.subtype_injective.comp e.injective,?_,?_⟩
  · intro f hf
    obtain ⟨g,hg⟩ := e.surjective ⟨f,E.contains_inner hf⟩
    exact ⟨g,congrArg Subtype.val hg⟩
  · intro g
    exact E.preserves_types _ (e g).property

/-- Ambient simplicity removes the outer part after conditional recognition;
no separate native simplicity theorem is assumed. -/
theorem nonempty_native_mulEquiv_of_simple_of_card_le [Finite M] [IsSimpleGroup M]
    (hm2 : 1 < m) (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) : Nonempty (M ≃* BinaryCarrier m hm) := by
  obtain ⟨e,_,_⟩ := exists_marked_mulEquiv_of_card_le E c hm2 hc horder
  let : IsSimpleGroup E.carrier := e.symm.isSimpleGroup
  let I := (MulAut.innerSubgroup (BinaryCarrier m hm)).comap E.carrier.subtype
  have hr : E.baseHom.range = I := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩
      exact ⟨b,rfl⟩
    · rintro ⟨b,hb⟩
      exact ⟨b,Subtype.ext hb⟩
  have htop : I = ⊤ := (inferInstance : I.Normal).eq_bot_or_eq_top.resolve_left (by
    intro hi
    let w := (reflection m hm .arms).val
    have hmem : E.baseHom w ∈ I := hr ▸ (show E.baseHom w ∈ E.baseHom.range from ⟨w,rfl⟩)
    have hone : E.baseHom w = 1 := mem_bot.mp (hi ▸ hmem)
    have hw1 : w=1 := E.baseHom_injective (conj_injective m hm)
      (hone.trans (map_one E.baseHom).symm)
    apply reflection_not_mem_borel m hm .arms
    change w ∈ borel (binaryParameters m hm)
    rw [hw1]
    exact (borel (binaryParameters m hm)).one_mem)
  have hsurj : Function.Surjective E.baseHom := MonoidHom.range_eq_top.mp (hr.trans htop)
  exact ⟨e.trans (MulEquiv.ofBijective E.baseHom
    ⟨E.baseHom_injective (conj_injective m hm),hsurj⟩).symm⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
