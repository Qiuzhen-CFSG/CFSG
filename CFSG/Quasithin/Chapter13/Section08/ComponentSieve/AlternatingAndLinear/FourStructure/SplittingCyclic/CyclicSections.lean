module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.Duality
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.CommutatorSpaces
public import Theory.Representation.BinaryOffender.FlagCodimension
public import Theory.Representation.BinaryOffender.SmallRank

/-!
# The module calculation in the cyclic L₄ case

The rank-one quadratic bound gives transvections on the lower module and
head. Every chief factor is faithful, so additivity of fixed codimension
forces W = I. The order-two displacement map then gives a two-dimensional
commutator space. Displacement on D_H identifies this space as the sum of
the lower commutator line and the critical line. The fixed intersection
also gives the hyperplane and supplement needed by the source argument.

All module identifications use the specified GL₄(2) equivalence. These are
conditional module deductions; they do not supply the ambient normalizer
or marked-vector facts required by the source cyclic contradiction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.961–962 (PDF pp.978–979).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic

open Representation Representation.BinaryOffender ChiefFactors
open CriticalTransfer.MarkedGeometry

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

/-- A transvection permits just one faithful chief factor below W, so W is the chosen
irreducible I. -/
theorem eq_atom_of_transvection (eH : H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (hchief : ChiefFactors.ChiefFactorsNaturalOrDual ρ eH)
    (I W : Subrepresentation ρ) (hI : IsAtom I) (hIW : I ≤ W)
    (A : Subgroup H) (hA : A ≠ ⊥) (hW : fixedCodim W.toRepresentation A = 1) :
    W = I := by
  classical
  let : Finite U := Module.finite_of_finite (ZMod 2)
  let : Finite (Subrepresentation ρ) :=
    Finite.of_injective (fun X : Subrepresentation ρ => (X : Set U)) SetLike.coe_injective
  by_contra hne
  obtain ⟨J, hIJ, hJW⟩ := exists_covBy_le_of_lt (lt_of_le_of_ne hIW (Ne.symm hne))
  have hIfaith := SplittingCyclic.AxisExclusions.naturalOrDual_faithful _ eH
    (SplittingCyclic.AxisExclusions.naturalOrDual_atom ρ eH hchief I hI)
  have hJfaith := SplittingCyclic.AxisExclusions.naturalOrDual_faithful _ eH
    (hchief I J hIJ).1
  have hpI := fixedCodim_pos_of_faithful I.toRepresentation hIfaith hA
  have hpJ := fixedCodim_pos_of_faithful (sectionRepresentation ρ I J) hJfaith hA
  have hsum := fixedCodim_section_add_lower_le ρ I J hIJ.le A
  have hmono := fixedCodim_subrepresentation_le W.toRepresentation (sectionLower ρ J W) A
  have he := fixedCodim_map_equivariant (sectionLower ρ J W).toRepresentation
    J.toRepresentation (MonoidHom.id H) (sectionLowerEquiv ρ hJW) (fun _ _ => rfl) A
  simp only [Subgroup.map_id] at he
  rw [he, hW] at hmono
  omega

/-- For an actor of order two, its commutator space is the image of its unique
nonidentity displacement map. -/
theorem commSpace_finrank_of_card_two (A : Subgroup H) (hA : Nat.card A = 2) :
    Module.finrank (ZMod 2) (commSpace ρ A) = fixedCodim ρ A := by
  obtain ⟨a, ha, hall⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  have he (b : A) : b = 1 ∨ b = a := by
    by_cases hb : b = 1
    · exact Or.inl hb
    · exact Or.inr (hall b hb)
  let f : U →ₗ[ZMod 2] U := ρ a - 1
  have hr : commSpace ρ A = f.range := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨b, u⟩, rfl⟩
      rcases he b with rfl | rfl
      · simp
      · exact ⟨u, rfl⟩
    · rintro _ ⟨u, rfl⟩
      exact Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) a u
  have hk : f.ker = fixedSpace ρ A := by
    ext u
    constructor
    · intro hu b
      have hu' : ρ a u = u := sub_eq_zero.mp hu
      rcases he b with rfl | rfl
      · simp
      · exact hu'
    · intro hu
      exact sub_eq_zero.mpr (hu a)
  have hf := f.finrank_range_add_finrank_ker
  have hc := fixedCodim_add_finrank ρ A
  rw [← hr, hk] at hf
  omega

omit [FiniteDimensional (ZMod 2) U] in
/-- The literal inclusion of a subrepresentation maps its commutators into the full
commutator space. -/
theorem commSpace_subrepresentation_le (W : Subrepresentation ρ) (A : Subgroup H) :
    (commSpace W.toRepresentation A).map W.toSubmodule.subtype ≤ commSpace ρ A := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, w⟩, rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) a (w : U)

/-- The rank-two commutator is the sum of the rank-one lower commutator and the critical
line, using displacement on an actual supplement. -/
theorem commSpace_eq_line_sup_of_supplement
    (W : Subrepresentation ρ) (D S : Submodule (ZMod 2) U) (A : Subgroup H)
    (hsup : W.toSubmodule ⊔ D = ⊤)
    (hD : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hS : Module.finrank (ZMod 2) S = 1)
    (hW : Module.finrank (ZMod 2) (commSpace W.toRepresentation A) = 1)
    (hU : Module.finrank (ZMod 2) (commSpace ρ A) = 2) :
    commSpace ρ A = (commSpace W.toRepresentation A).map W.toSubmodule.subtype ⊔ S := by
  let C := (commSpace W.toRepresentation A).map W.toSubmodule.subtype
  have hle : commSpace ρ A ≤ C ⊔ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, u⟩, rfl⟩
    have hu : u ∈ W.toSubmodule ⊔ D := hsup ▸ Submodule.mem_top
    obtain ⟨w, hw, d, hd, rfl⟩ := Submodule.mem_sup.mp hu
    have hwc : ρ a w - w ∈ C :=
      Submodule.mem_map.mpr ⟨W.toRepresentation a ⟨w, hw⟩ - ⟨w, hw⟩,
        Coinvariants.sub_mem_ker (ρ := W.toRepresentation.comp A.subtype) a _, rfl⟩
    have hdc := hD a a.property d hd
    have hh := (C ⊔ S).add_mem (Submodule.mem_sup_left hwc) (Submodule.mem_sup_right hdc)
    change ρ a (w + d) - (w + d) ∈ C ⊔ S
    simpa only [map_add, add_sub_add_comm] using hh
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hc : Module.finrank (ZMod 2) C = 1 := by
    rw [Submodule.finrank_map_subtype_eq]
    exact hW
  have hdim := C.finrank_sup_add_finrank_inf_eq S
  have hm := Submodule.finrank_mono hle
  rw [hU] at hm ⊢
  omega

/-- The rank-one quadratic bound forces W = I, a one-dimensional lower commutator, and a
two-dimensional full commutator. -/
theorem cyclic_sections
    (eH : H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (hchief : ChiefFactors.ChiefFactorsNaturalOrDual ρ eH)
    (I W : Subrepresentation ρ) (hI : IsAtom I) (hIW : I ≤ W)
    (hhead : ChiefFactors.IsNatural W.quotientRepresentation eH)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hrank : rank A = 1)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    W = I ∧ Module.finrank (ZMod 2) (commSpace W.toRepresentation A) = 1 ∧
      Module.finrank (ZMod 2) (commSpace ρ A) = 2 := by
  let : Finite (BinaryLinear.GL ChiefFactors.NaturalSpace) :=
    Finite.of_injective (fun g : BinaryLinear.GL ChiefFactors.NaturalSpace =>
      (g : ChiefFactors.NaturalSpace → ChiefFactors.NaturalSpace)) DFunLike.coe_injective
  let : Finite H := Finite.of_injective eH eH.injective
  have hIf := AxisExclusions.naturalOrDual_faithful _ eH
    (AxisExclusions.naturalOrDual_atom ρ eH hchief I hI)
  have hWf : Function.Injective W.toRepresentation := by
    intro g k hgk
    apply hIf
    ext v
    have hh := congrArg Subtype.val (LinearMap.congr_fun hgk ⟨v, hIW v.property⟩)
    exact hh
  have hQf := AxisExclusions.natural_faithful _ eH hhead
  obtain ⟨hw, _, hu⟩ := faithful_sections_of_fixedCodim_le_two ρ W hWf hQf hA.1
    (by simpa only [hrank, mul_one] using hbound)
  have hc : Nat.card A = 2 := by rw [hA.card_eq_two_pow_rank, hrank]; rfl
  exact ⟨eq_atom_of_transvection ρ eH hchief I W hI hIW A hA.1 hw,
    (commSpace_finrank_of_card_two W.toRepresentation A hc).trans hw,
    (commSpace_finrank_of_card_two ρ A hc).trans hu⟩

/-- A fixed intersection with a codimension-at-most-one space gives both the actor-fixed
hyperplane and the required supplement. -/
theorem hyperplane_and_supplement_of_fixed_intersection
    (I : Subrepresentation ρ) (hI : Function.Injective I.toRepresentation)
    (B : Subgroup H) (hB : B ≠ ⊥) (D : Submodule (ZMod 2) U)
    (hD : Module.finrank (ZMod 2) (U ⧸ D) ≤ 1)
    (hfix : I.toSubmodule ⊓ D ≤ fixedSpace ρ B) :
    fixedCodim I.toRepresentation B = 1 ∧ I.toSubmodule ⊔ D = ⊤ := by
  let E := D.comap I.toSubmodule.subtype
  have hEF : E ≤ fixedSpace I.toRepresentation B := by
    intro v hv b
    apply Subtype.ext
    exact hfix ⟨v.property, hv⟩ b
  have hm := Submodule.finrank_mono hEF
  have he := E.finrank_quotient_add_finrank
  have hf := fixedCodim_add_finrank I.toRepresentation B
  have hp := fixedCodim_pos_of_faithful I.toRepresentation hI hB
  have hc := codim_decomposition I.toSubmodule D
  change Module.finrank (ZMod 2) (U ⧸ (I.toSubmodule ⊔ D)) +
    Module.finrank (ZMod 2) (I.toSubmodule ⧸ E) = _ at hc
  refine ⟨by omega, ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have hs := (I.toSubmodule ⊔ D).finrank_quotient_add_finrank
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic
