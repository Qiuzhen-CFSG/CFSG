module

public import Theory.Representation.SL2FourNaturalOrbits.BorelFactors
public import CFSG.Quasithin.ChapterJ.Defs
public import Theory.GroupTheory.PCoreImage

/-!
# The actual marked Borel and its symmetric normalizer

The Borel is the image of the upper triangular subgroup under the supplied
SL₂(4) ≃ A₅ marking. Its upper root image is its two-core. Characteristicness
of this core makes its fixed plane invariant under the actual S₅ normalizer.
The two natural factors retain the literal restricted representation and
quotient action. Their irreducibility and noncentrality follow from the
Borel restriction, so no normalizer-equivariant marking is assumed.

Source: Aschbacher–Smith 14.7.70, printed p.1074 (PDF p.1091).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Subgroup Representation Representation.SL2FourNatural
open Representation.SL2FourNatural.BorelFactors

variable (r : ChapterJ.L2FourAction)

/-- The given marking followed by the actual alternating-group inclusion. -/
def markingHom : SL →* ChapterJ.S5 :=
  (alternatingGroup (Fin 5)).subtype.comp r.marking.toMonoidHom

/-- The image of the upper triangular Borel under the prescribed marking. -/
def borel : Subgroup ChapterJ.S5 := B0.map (markingHom r)

/-- Its literal normalizer in S₅. -/
def normalizer : Subgroup ChapterJ.S5 := Subgroup.normalizer (borel r : Set ChapterJ.S5)

/-- The marked upper root group, before identifying it with the two-core. -/
def root : Subgroup ChapterJ.S5 := U0.map (markingHom r)

theorem markingHom_injective : Function.Injective (markingHom r) :=
  (alternatingGroup (Fin 5)).subtype_injective.comp r.marking.injective

/-- Identification uses the actual embedded two-core and the same marking. -/
theorem borel_twoCore : (borel r).pCoreIn 2 = root r := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : IsPGroup 2 (markingHom r).ker := by
    rw [(markingHom r).ker_eq_bot_iff.mpr (markingHom_injective r)]
    exact IsPGroup.of_bot
  rw [borel, ← map_pCoreIn_of_ker_isPGroup (markingHom r) hk B0, twoCoreIn_B0]
  rfl

/-- The natural plane is the fixed space of the marked root group. -/
theorem mem_line_iff_root (v : V) :
    v ∈ upperFixed ↔ ∀ u ∈ root r, r.action u v = v := by
  constructor
  · intro hv u hu
    obtain ⟨g, hg, rfl⟩ := hu
    change r.action (r.marking g) v = v
    rw [r.restriction]
    exact (mem_upperFixed_iff_core v).mp hv g (twoCoreIn_B0.symm ▸ hg)
  · intro h
    apply (mem_upperFixed_iff_core v).mpr
    intro g hg
    rw [← r.restriction]
    exact h (markingHom r g) (mem_map.mpr ⟨g, twoCoreIn_B0 ▸ hg, rfl⟩)

/-- The actual normalizer preserves the core's fixed plane. -/
theorem normalizer_preserves_line (n : normalizer r) (v : V) (hv : v ∈ upperFixed) :
    r.action n v ∈ upperFixed := by
  have hn : normalizer r ≤ Subgroup.normalizer (root r : Set ChapterJ.S5) := by
    rw [← borel_twoCore]
    exact normalizer_le_normalizer_characteristic_image (borel r) (pCore 2 (borel r))
  apply (mem_line_iff_root r _).mpr
  intro u hu
  have hu' : (n : ChapterJ.S5)⁻¹ * u * n ∈ root r :=
    (Subgroup.mem_normalizer_iff.mp (hn ((normalizer r).inv_mem n.property)) u).mp hu
  have he := (mem_line_iff_root r v).mp hv _ hu'
  calc
    r.action u (r.action n v) = r.action (u * n) v := by
      rw [map_mul, Module.End.mul_apply]
    _ = r.action ((n : ChapterJ.S5) * ((n : ChapterJ.S5)⁻¹ * u * n)) v := by
      simp only [← mul_assoc, mul_inv_cancel, one_mul]
    _ = r.action n v := by rw [map_mul, Module.End.mul_apply, he]

/-- Restriction to any actual actor between the Borel and its normalizer. -/
def actorNatural (A : Subgroup ChapterJ.S5) : Representation (ZMod 2) A V :=
  r.action.comp A.subtype

/-- The same literal plane for the Borel and for the larger normalizer actor. -/
def actorLine (A : Subgroup ChapterJ.S5) (hAN : A ≤ normalizer r) :
    Subrepresentation (actorNatural r A) where
  toSubmodule := upperFixed
  apply_mem_toSubmodule a v hv := normalizer_preserves_line r ⟨a.val, hAN a.property⟩ v hv

/-- The actual quotient action, not an abstract space of the same dimension. -/
abbrev actorQuotient (A : Subgroup ChapterJ.S5) (hAN : A ≤ normalizer r) :=
  (actorLine r A hAN).quotientRepresentation

variable (A : Subgroup ChapterJ.S5) (hBA : borel r ≤ A) (hAN : A ≤ normalizer r)

/-- The original marking maps the Borel into each of the two actual actors. -/
def borelToActor : B0 →* A :=
  (markingHom r).comp B0.subtype |>.codRestrict A (fun g =>
    hBA (mem_map.mpr ⟨g.val, g.property, rfl⟩))

theorem actorLine_restriction (g : B0) (v : upperFixed) :
    (actorLine r A hAN).toRepresentation (borelToActor r A hBA g) v =
      line.toRepresentation g v := by
  apply Subtype.ext
  exact r.restriction g.val v.val

theorem actorQuotient_restriction (g : B0) (v : V ⧸ upperFixed) :
    actorQuotient r A hAN (borelToActor r A hBA g) v = quotient g v := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    change upperFixed.mkQ (r.action (r.marking g.val) v) = upperFixed.mkQ (action g.val v)
    rw [r.restriction]

include hBA in
theorem actorLine_irreducible : IsIrreducible (actorLine r A hAN).toRepresentation := by
  have : Nontrivial (actorLine r A hAN).toSubmodule := line_nontrivial
  apply irreducible_of_transitive
  intro v w hv hw
  obtain ⟨g, hg⟩ := line_transitive v w hv hw
  exact ⟨borelToActor r A hBA g, (actorLine_restriction r A hBA hAN g v).trans hg⟩

include hBA in
theorem actorQuotient_irreducible : IsIrreducible (actorQuotient r A hAN) := by
  have : Nontrivial (V ⧸ (actorLine r A hAN).toSubmodule) := quotient_nontrivial
  apply irreducible_of_transitive
  intro v w hv hw
  obtain ⟨g, hg⟩ := quotient_transitive v w hv hw
  exact ⟨borelToActor r A hBA g, (actorQuotient_restriction r A hBA hAN g v).trans hg⟩

include hBA in
theorem actorLine_noncentral : ∃ g v, (actorLine r A hAN).toRepresentation g v ≠ v := by
  obtain ⟨g, v, hv⟩ := line_noncentral
  exact ⟨borelToActor r A hBA g, v, fun h =>
    hv ((actorLine_restriction r A hBA hAN g v).symm.trans h)⟩

include hBA in
theorem actorQuotient_noncentral : ∃ g v, actorQuotient r A hAN g v ≠ v := by
  obtain ⟨g, v, hv⟩ := quotient_noncentral
  exact ⟨borelToActor r A hBA g, v, fun h =>
    hv ((actorQuotient_restriction r A hBA hAN g v).symm.trans h)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
