module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Sections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSeed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SixExclusion
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section

/-!
# The source subgroup and codimension deductions in the six-factor branch

The literal source action constructs a conjugation section with kernel V₁.
Its displacement formula and the critical relative-index comparison supply
the linear sieve inputs. Absence of offenders on a chief factor passes to
the maximal submodule. The sieve then gives Uγ*=Vγ* of order four and both
codimension equalities.

There is a separate lifting issue: containment of the image of A₁ alone does
not imply A₁≤U_H, because that image uses A₁∩U_H. We prove that the image is
nonzero. Otherwise the denominator is fixed, producing a forbidden offender
on the maximal submodule. Since A₁ has order two, this proves its actual
containment in U_H and then in the lifted maximal submodule.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25,
printed p.961 (PDF p.978), using 13.8.22 and F.9.13(6). The marked B.3.2(6)
calculation still has to provide rank two and absence of offenders on the
factor. Reversal and the strict 13.8.11 inclusion are not assumed or asserted.
-/

@[expose] public section

open Representation Representation.BinaryOffender Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open CriticalTransfer

section Literal
variable {G : Type*} [Group G] (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The actual quotient action, with relative kernel and conjugation on every
representative, supplies the section used by the subgroup transport lemmas. -/
def sourceConjugationSection
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (hUH : Source.UH H V₃ ≤ H) (hz : H ≤ centralizer (V₁ : Set G))
    (hline : V₁ ≤ Source.UH H V₃) :
    ConjugationSection H (Source.UH H V₃) V₁ ρ where
  le := hUH
  normalizes := le_normalizer_conjugateSpanBy V₃ H
  centralizes := hz
  line_le := hline
  quotient := {
    toFun u := Multiplicative.ofAdd (Additive.ofMul (sourceProjection H V₃ V₁ u))
    map_one' := by change sourceProjection H V₃ V₁ 1 = 1; exact map_one _
    map_mul' u v := by change sourceProjection H V₃ V₁ (u * v) = _; exact map_mul _ _ _ }
  surjective := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃))
  kernel := QuotientGroup.ker_mk' (V₁.subgroupOf (Source.UH H V₃))
  conjugates := hρ

end Literal

section Linear
variable {H U : Type*} [Group H] [Finite H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

/-- The two outputs required from the marked B.3.2(6) calculation. In the
source application A and V are the actual Uγ* and Vγ*. This specification
contains neither the critical codimension equalities nor strict inclusion. -/
def SixActorFacts (X Y : Subrepresentation ρ) (A V : Subgroup H) : Prop :=
  rank V = 2 ∧ ∀ B ≤ A, ¬ IsBestOffender (sectionRepresentation ρ X Y) B

/-- The line image is nonzero: if the denominator were fixed pointwise,
the source codimension comparison would produce an offender on W. -/
theorem line_ne_bot_of_no_bestOffender
    (W : Subrepresentation ρ) (D S : Submodule (ZMod 2) U) (A : Subgroup H)
    (hA : IsElementaryTwo A)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hno : ∀ B ≤ A, ¬ IsBestOffender W.toRepresentation B) : S ≠ ⊥ := by
  intro hS
  have hfixed : W.toSubmodule ⊓ D ≤ fixedSpace ρ A := by
    intro w hw a
    have hm := hcomm a a.property w hw.2
    rw [hS] at hm
    exact sub_eq_zero.mp hm
  obtain ⟨B, hBA, hB⟩ :=
    (submodule_offender_sieve ρ W D hA hfixed hdim).1.exists_bestOffender _
  exact hno B hBA hB

end Linear

section Source
variable {G U : Type*} [Group G] [Finite G] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- The subgroup of U_H lying over a linear subspace of its central quotient. -/
def liftedSubmodule (s : ConjugationSection H UH Z ρ) (W : Submodule (ZMod 2) U) :
    Subgroup G :=
  ((W.toAddSubgroup.toSubgroup).comap s.quotient).map UH.subtype

omit [Finite G] [FiniteDimensional (ZMod 2) U] in
theorem liftedSubmodule_le (s : ConjugationSection H UH Z ρ) (W : Submodule (ZMod 2) U) :
    liftedSubmodule s W ≤ UH := by
  rintro x ⟨u, _, rfl⟩
  exact u.property

omit [FiniteDimensional (ZMod 2) U] in
/-- Nonzero line image restores actual subgroup containment before lifting
its linear inclusion. This prevents the intersection-image convention from
silently supplying a false containment. -/
theorem line_le_liftedSubmodule (s : ConjugationSection H UH Z ρ)
    (A : Subgroup G) (hA : Nat.card A = 2) (W : Submodule (ZMod 2) U)
    (hne : s.image A ≠ ⊥) (hW : s.image A ≤ W) :
    A ≤ liftedSubmodule s W := by
  have hAU : A ≤ UH := by
    by_contra hn
    exact hne (s.image_eq_bot_of_not_le A hA hn)
  intro a ha
  refine ⟨⟨a, hAU ha⟩, ?_, rfl⟩
  exact hW ⟨⟨a, hAU ha⟩, ha, rfl⟩

/-- The full forward numerical deduction from a six-factor actor calculation.
The marked model supplies only rank two and no offenders on the factor.
Every line containment, subgroup equality and codimension below is proved. -/
theorem source_six_factor_codimensions
    (s : ConjugationSection H UH Z ρ) (g : G) (Vg : Subgroup G)
    (hZ : Nat.card Z = 2)
    (hback : UH ≤ H.map (MulAut.conj g).toMonoidHom)
    (hUV : UH.map (MulAut.conj g).toMonoidHom ≤ Vg) (hVH : Vg ≤ H)
    (hA : IsElementaryTwo (Source.starImage H (UH.map (MulAut.conj g).toMonoidHom)))
    (hV : IsElementaryTwo (Source.starImage H Vg)) (hVr : rank (Source.starImage H Vg) = 2)
    (hcritical : Nat.log 2 ((Source.DH UH (UH.map (MulAut.conj g).toMonoidHom)
      (Z.map (MulAut.conj g).toMonoidHom)).relIndex UH) ≤
      Nat.log 2 ((Source.Dgamma (UH.map (MulAut.conj g).toMonoidHom) UH Z).relIndex
        (UH.map (MulAut.conj g).toMonoidHom)))
    (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
    (hheads : AllNaturalHeads ρ eH)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (X Y : Subrepresentation ρ) (hXY : X ≤ Y) (hYW : Y ≤ W)
    (hno : ∀ A ≤ Source.starImage H (UH.map (MulAut.conj g).toMonoidHom),
      ¬ IsBestOffender (sectionRepresentation ρ X Y) A) :
    let Ug := UH.map (MulAut.conj g).toMonoidHom
    let A₁ := Z.map (MulAut.conj g).toMonoidHom
    let D := s.image (Source.DH UH Ug A₁)
    A₁ ≤ liftedSubmodule s W.toSubmodule ∧
      s.image A₁ ≤ W.toSubmodule ∧ ¬ W.toSubmodule ≤ D ∧
      Source.starImage H Ug = Source.starImage H Vg ∧
      rank (Source.starImage H Ug) = 2 ∧ Nat.card (Source.starImage H Ug) = 4 ∧
      Module.finrank (ZMod 2) ((U ⧸ W.toSubmodule) ⧸ D.map W.toSubmodule.mkQ) = 1 ∧
      Module.finrank (ZMod 2) (U ⧸ D) = 2 ∧
      fixedCodim W.quotientRepresentation (Source.starImage H Ug) = 1 := by
  dsimp only
  let Ug := UH.map (MulAut.conj g).toMonoidHom
  let A₁ := Z.map (MulAut.conj g).toMonoidHom
  have hUg : Ug ≤ H := hUV.trans hVH
  have hA₁ : Nat.card A₁ = 2 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hZ
  have hUA : UH ≤ normalizer (A₁ : Set G) :=
    hback.trans ((s.centralizes_conjugate_line g).trans (centralizer_le_normalizer _))
  have hfaith := IsNatural.faithful W.quotientRepresentation eH (hheads W hW)
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply hfaith
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with | _ v =>
    exact congrArg W.toSubmodule.mkQ (LinearMap.congr_fun hab v)
  have hbound := s.critical_bound Ug A₁ hUg hρ hcritical
  obtain ⟨hS, hcomm⟩ := s.critical_line_displacement Ug A₁ hUA hA₁
  have hnoW := no_bestOffender_of_section ρ X Y W hXY hYW (Source.starImage H Ug) hno
  have hne := line_ne_bot_of_no_bestOffender ρ W _ _ _ hA hcomm hbound hnoW
  obtain ⟨hSW, hWD, he, hr, hc, hq, hd, hf⟩ := six_factor_codimensions ρ W
    (s.image (Source.DH UH Ug A₁)) (s.image A₁) hS (Source.starImage H Ug)
    (Source.starImage H Vg) hA (map_mono (subgroupOf_mono H hUV)) hV hVr
    hcomm hbound hnoW hfaith
  exact ⟨line_le_liftedSubmodule s A₁ hA₁ W.toSubmodule hne hSW,
    hSW, hWD, he, hr, hc, hq, hd, hf⟩

end Source
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
