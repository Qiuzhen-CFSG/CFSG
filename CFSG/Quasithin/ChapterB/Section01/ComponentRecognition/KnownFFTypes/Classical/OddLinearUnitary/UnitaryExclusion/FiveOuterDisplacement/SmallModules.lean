module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement.Inputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement.SmallModules.AbsoluteInputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement.SmallModules.Degrees
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.FiveOuterDisplacement.SmallModules.SevenRestriction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.PrimeDegree.Inputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.PrimeDegree.CenterCoprime
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.PrimeDegree.RootGeometry
public import Theory.Representation.BinaryCoprimeDegree.RationalExtraspecial

/-!
# Small PSU₃(5) displacement on the original binary module

The absolute degree window and the order-seven restriction calculation
imply the binary projective bound. Schur-field descent preserves the actual
operators and forces the binary degree to be 20 or 21. For an arbitrary
central lift x, either x has order seven and the restriction calculation
applies, or x⁷ is a nonidentity central element and x has no fixed vector.

The degree minimum uses the existing rational extraspecial root geometry
and the prime-to-five order of the source cover's center. The unconditional
`five_small_module_projective_seven_bound` discharges these group inputs and
both absolute representation calculations. Their source cover lifts retain
the actual Hermitian form and scalar kernel, using the original faithful
binary action to eliminate the two-core. The conditional assembly remains
available. No outer involution, offender or cubic-ratio premise is used.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v

/-- The existing rational-root degree bound applies over every finite field
of characteristic two. Combining it with the separate 20–24 window supplies
the absolute input to Schur descent, on the literal source central cover. -/
theorem five_absolute_degree_window_of_local_inputs
    (hgeometry : PrimeDegreeRootGeometry)
    (hcenter : PrimeDegreeCenterCoprime.{u, v})
    (hdegree : FiveAbsoluteSmallDegreeWindow.{u, v})
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]
    (h : SourceHypotheses ρ L 5) :
    SU3.FiveSmallModules.AbsoluteDegreeWindow.{u, v} L := by
  intro K _ _ _ U _ _ _ τ hf hi hhi
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply hdegree ρ L h K U τ hf hi _ hhi
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h.quotient
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hsurj : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center L := by
    ext x
    change e ((QuotientGroup.mk' (center L)) x) = 1 ↔ x ∈ center L
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hcop := hcenter ρ L h (by decide : 3 < 5)
  have hlocal := (hgeometry F J (by decide : Nat.Prime 5) (by decide) hcard hconj).of_central_coprime
    f hsurj (by rw [hker]) (by rwa [hker])
  exact BinaryCoprimeDegree.finrank_ge_of_rational_extraspecial (by decide : 5 ≠ 2)
    τ hf hlocal

/-- Conditional assembly of the exact source bound, including arbitrary
central lifts and the original binary field and representation. -/
theorem five_small_module_projective_seven_bound_of_absolute_inputs
    (hgeometry : PrimeDegreeRootGeometry)
    (hcenter : PrimeDegreeCenterCoprime.{u, v})
    (hdegree : FiveAbsoluteSmallDegreeWindow.{u, v})
    (hseven : FiveAbsoluteSevenRestriction.{u, v}) :
    FiveSmallModuleProjectiveSevenBound.{u, v} := by
  intro G V _ _ _ _ _ ρ L _ h hlo hhi x hx
  let σ : Representation (ZMod 2) L V := ρ.comp L.subtype
  let : σ.IsIrreducible := h.irreducible
  have hf : Function.Injective σ := h.faithful.comp L.subtype_injective
  obtain ⟨_, hcalc⟩ := SU3.FiveSmallModules.binary_degree_and_seven_displacement_of_absolute_inputs
    σ hf hhi (five_absolute_degree_window_of_local_inputs hgeometry hcenter hdegree ρ L h)
      (hseven ρ L h)
  rcases SU3.FiveSmallModules.orderOf_eq_or_invariants_eq_bot_of_projective_prime_order
    σ hf h.irreducible x (by decide : Nat.Prime 7) hx with ho | hzero
  · exact (hcalc x ho hx).ge
  · have hdim := fixedCodim_add_finrank σ (zpowers x)
    change fixedSpace σ (zpowers x) = ⊥ at hzero
    change fixedCodim σ (zpowers x) +
      Module.finrank (ZMod 2) (fixedSpace σ (zpowers x)) = Module.finrank (ZMod 2) V at hdim
    rw [hzero, finrank_bot, add_zero] at hdim
    change 18 ≤ fixedCodim σ (zpowers x)
    omega

/-- Every projective order-seven element moves at least eighteen dimensions
on the original small binary source module. The absolute degree and restriction
calculations, root geometry and covering-center input are all discharged;
the element itself need not have order seven. -/
theorem five_small_module_projective_seven_bound :
    FiveSmallModuleProjectiveSevenBound.{u, v} :=
  five_small_module_projective_seven_bound_of_absolute_inputs
    primeDegreeRootGeometry primeDegreeCenterCoprime
    five_absolute_small_degree_window five_absolute_seven_restriction

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
