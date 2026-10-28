module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.NaturalSections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.Linear
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.Section
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.DualLowerBound.UpperSection

/-!
# The multiple-factor contradiction in 13.8.26

Each faithful section is tested on a natural subquotient. In the strong-offender
branch its marking also identifies an opposite-action quotient of the upper module. A strong offender
would give the transvection cube on the lower section and a nonquadratic
action on the upper quotient. In the absence of strong offenders, 13.8.22
forces rank one. The larger critical actor and the actual pointwise
centralizers then contradict 13.8.23(4).

The final application uses U_H/V₁, D_H, A₁ and Uγ from the same critical
pair. In particular it also treats A₁ outside U_H: its image is zero, and
the fixed-subspace form of 13.8.22 gives a strong offender immediately.
The marked natural subquotients and upper quotient maps remain appendix
and earlier-source inputs; they do not assume component-section recognition.

Source: Aschbacher–Smith 13.8.22–23,26, printed pp.957–958,962.
-/

@[expose] public section

open Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition
open NaturalSix

variable {J E F : Type*} [Group J] [Finite J]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

/-- Two actions linked by the same marking. The upper map is surjective and
equivariant; no identification of the two outer-related actions is made. -/
structure OppositeUpper (σ : Representation (ZMod 2) J E)
    (τ : Representation (ZMod 2) J F) (A : Subgroup J) where
  lower : NaturalSection σ
  sylow : A.map lower.actor ≤ CFSG.Quasithin.ChapterB.Offenders.Six.sylowCarrier
  upper : F →ₗ[ZMod 2] Natural
  surjective : Function.Surjective upper
  intertwines : ∀ a v, upper (τ a v) = Marked.oppositeAction (lower.actor a) (upper v)

/-- The strict-case argument allows arbitrary central factors in W and U/W.
Compatible upper markings are required only in the strong-offender branch:
the two lower sections need not have the same marked natural action. -/
theorem no_two_faithful_sections
    (ρ : Representation (ZMod 2) J E) (τ : Representation (ZMod 2) J F)
    (W : Subrepresentation ρ) (A : Subgroup J)
    (hA : IsElementaryTwo A) (hquad : IsQuadratic τ A)
    (mW : NaturalSection W.toRepresentation)
    (mQ : NaturalSection W.quotientRepresentation)
    (oW : ∀ B ≤ A, IsStrongOffender W.toRepresentation B →
      Nonempty (OppositeUpper W.toRepresentation τ A))
    (oQ : ∀ B ≤ A, IsStrongOffender W.quotientRepresentation B →
      Nonempty (OppositeUpper W.quotientRepresentation τ A))
    (D S : Submodule (ZMod 2) E) (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (E ⧸ D) ≤ rank A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hlarge : rank A = 1 → ∃ B : Subgroup J, A < B ∧
      ∀ b ∈ B, ∀ v ∈ fixedSpace ρ A, ρ b v - v ∈ S) : False := by
  have hnW : ¬ ∃ B ≤ A, IsStrongOffender W.toRepresentation B := by
    rintro ⟨B, hBA, hB⟩
    obtain ⟨o⟩ := oW B hBA hB
    exact no_strong_of_opposite_quotient _ o.lower τ A hquad o.sylow o.upper
      o.surjective o.intertwines ⟨B, hBA, hB⟩
  have hnQ : ¬ ∃ B ≤ A, IsStrongOffender W.quotientRepresentation B := by
    rintro ⟨B, hBA, hB⟩
    obtain ⟨o⟩ := oQ B hBA hB
    exact no_strong_of_opposite_quotient _ o.lower τ A hquad o.sylow o.upper
      o.surjective o.intertwines ⟨B, hBA, hB⟩
  have hW := mW.faithful
  have hQ := mQ.faithful
  by_cases hzero : S = ⊥
  · have hfixed : D ≤ fixedSpace ρ A := by
      intro d hd a
      have hm := hcomm a a.property d hd
      rw [hzero] at hm
      exact sub_eq_zero.mp hm
    obtain ⟨B, hBA, _, hs⟩ :=
      strong_submodule_offender_of_fixed_subspace ρ W D hQ hA hfixed hdim
    exact hnW ⟨B, hBA, hs⟩
  · have hpos : 0 < Module.finrank (ZMod 2) S :=
      Nat.pos_of_ne_zero (fun hz => hzero (Submodule.finrank_eq_zero.mp hz))
    have hatom : IsAtom S := Submodule.isAtom_iff_finrank_eq_one.mpr (by omega)
    have hr := rank_one_of_no_strong_offenders ρ W D S hatom hW hQ hA hcomm hdim
      (by rintro ⟨B, hBA, _, hs⟩; exact hnW ⟨B, hBA, hs⟩)
      (by rintro ⟨B, hBA, _, hs⟩; exact hnQ ⟨B, hBA, hs⟩)
      (fun _ hE hc => mW.rank_one hE hc)
      (fun _ hE hc => mQ.rank_one hE hc)
    obtain ⟨B, hAB, hB⟩ := hlarge hr
    exact no_rank_one_faithful_sections ρ W S hatom hW hQ hA hAB hr hbound hB
      (fun _ hE _ hc => mW.fixed_kernel hE hc)
      (fun _ hE _ hc => mQ.fixed_kernel hE hc)

open AlternatingAndLinear.FourStructure.CriticalTransfer CriticalGeometry
open AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences

variable {G : Type*} [Group G] [Finite G] {L T H V V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

omit [Finite G] in
/-- The earlier double-commutator bound makes the actual V_H/U_H action
quadratic. The only quotient used here is the one specified by `t`. -/
theorem upper_quadratic_of_commutator
    (τ : Representation (ZMod 2) (Source.Hstar H) F)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (R : Subgroup G)
    (hc : ⁅R, ⁅R, Source.VH H V⁆⁆ ≤ Source.UH H V₃) :
    IsQuadratic τ (Source.starImage H R) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  obtain ⟨w, hw⟩ := t.surjective (Multiplicative.ofAdd v)
  have hv : (t.quotient w).toAdd = v := congrArg Multiplicative.toAdd hw
  rw [← hv, t.displacement]
  apply sub_eq_zero.mp
  rw [t.displacement]
  change (⟨⁅(a : G), ⁅(b : G), (w : G)⁆⁆, _⟩ : Source.VH H V) ∈ t.quotient.ker
  rw [t.kernel]
  exact hc (commutator_mem_commutator ha (commutator_mem_commutator hb w.property))

/-- Apply the contradiction to the literal source module and critical pair.
The rank and displacement comparisons are derived from the actual subgroup
denominators, rather than assumed for unrelated vector spaces. -/
theorem source_no_two_faithful_sections
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hf : Function.Injective ρ) (hUg : c.Ugamma V₃ ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hline : Nat.card V₁ = 2)
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)))
    (τ : Representation (ZMod 2) (Source.Hstar H) F)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (hquad : ⁅c.Ugamma V₃, ⁅c.Ugamma V₃, Source.VH H V⁆⁆ ≤ Source.UH H V₃)
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hbound : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (c.Ugamma V₃)))
    (hlarge : rank (Source.starImage H (c.Ugamma V₃)) = 1 →
      ∃ B : Subgroup (Source.Hstar H), Source.starImage H (c.Ugamma V₃) < B ∧
        ∀ b ∈ B, ∀ v ∈ fixedSpace ρ (Source.starImage H (c.Ugamma V₃)),
          ρ b v - v ∈ s.image (c.Aone V₁))
    (W : Subrepresentation ρ)
    (mW : NaturalSection W.toRepresentation)
    (mQ : NaturalSection W.quotientRepresentation)
    (oW : ∀ B ≤ Source.starImage H (c.Ugamma V₃), IsStrongOffender W.toRepresentation B →
      Nonempty (OppositeUpper W.toRepresentation τ (Source.starImage H (c.Ugamma V₃))))
    (oQ : ∀ B ≤ Source.starImage H (c.Ugamma V₃), IsStrongOffender W.quotientRepresentation B →
      Nonempty (OppositeUpper W.quotientRepresentation τ (Source.starImage H (c.Ugamma V₃)))) :
    False := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  obtain ⟨hd, hc⟩ := s.critical_line_displacement_of_conjugate
    (c.Ugamma V₃) (c.gb : G) hreverse hline
  exact no_two_faithful_sections ρ τ W _ hA
    (upper_quadratic_of_commutator τ t _ hquad) mW mQ oW oQ
    (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)))
    (s.image (c.Aone V₁)) hd hc
    (s.critical_bound (c.Ugamma V₃) (c.Aone V₁) hUg hf hcritical) hbound hlarge

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition
end
