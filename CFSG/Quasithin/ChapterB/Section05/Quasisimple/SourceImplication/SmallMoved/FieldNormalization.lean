module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.RankOneFieldSize
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Representation.SL2OrthogonalCover.Universal

/-!
# Normalizing the small-field linear action rows

A perfect nontrivial actor excludes SL₂(2), so the small-plane bound makes
its rank-one defining field have order four. A single field isomorphism
acts entrywise on matrices and coordinatewise on vectors, preserving the
actual action equivalence. The degree-one SL₃ row uses the existing binary
field transport. These conversions retain the actor marking required when
the B.5 section returns to the original component quotient.

Source: Aschbacher–Smith, B.4.2, B.5.1 and 13.7.18, printed pp.85–86,
99–103 and 945.
-/

@[expose] public section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved

/-- The coefficient-field marking used on matrices and vectors alike. -/
noncomputable def degreeTwoFieldEquiv (F : BinaryField) (hF : F.degree = 2) :
    F.Carrier ≃+* SL2FourNatural.F := by
  letI := Fintype.ofFinite F.Carrier
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, F.card_eq, hF, SL2FourNatural.card_field]
  decide

/-- Degree-two natural rank-one rows use the literal four-field model. -/
noncomputable def degreeTwoLinearTwoEquiv (F : BinaryField) (hF : F.degree = 2) :
    ActionEquiv (linearNatural F 2)
      (SL2OrthogonalCover.binaryNatural (F := SL2FourNatural.F)) := by
  let e := degreeTwoFieldEquiv F hF
  let l : F.Carrier ≃ₗ[ZMod 2] SL2FourNatural.F :=
    { e.toAddEquiv with map_smul' := ZMod.map_smul e }
  refine ⟨Atlas.fieldEquivSL 2 e, LinearEquiv.piCongrRight (fun _ : Fin 2 => l), ?_⟩
  intro g v
  funext i
  change e (∑ j, g.val i j * v j) = ∑ j, e (g.val i j) * e (v j)
  simp only [map_sum, map_mul]

variable {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) A V}

/-- Perfect nontrivial rank-one actors cannot use the degree-one row. -/
theorem linearTwo_degree_eq_two [Group.IsPerfect A] [Nontrivial A]
    (F : BinaryField) (hF : F.degree ≤ 2)
    (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier) : F.degree = 2 := by
  have hlarge := perfect_linear_two_field_large F e
  have hpos := F.degree_pos
  have hn : F.degree ≠ 1 := by
    intro hn
    rw [F.card_eq, hn] at hlarge
    norm_num at hlarge
  omega

/-- Preserve both the module equivalence and the exact composed actor map
when normalizing the small-plane SL₂ row. -/
noncomputable def linearTwoFourActionEquiv [Group.IsPerfect A] [Nontrivial A]
    (F : BinaryField) (hF : F.degree ≤ 2)
    (e : ActionEquiv ρ (linearNatural F 2)) :
    ActionEquiv ρ (SL2OrthogonalCover.binaryNatural (F := SL2FourNatural.F)) :=
  let q := degreeTwoLinearTwoEquiv F (linearTwo_degree_eq_two F hF e.groupEquiv)
  ⟨e.groupEquiv.trans q.groupEquiv, e.linearEquiv.trans q.linearEquiv,
    fun g v => (congrArg q.linearEquiv (e.intertwines g v)).trans
      (q.intertwines (e.groupEquiv g) (e.linearEquiv v))⟩

/-- The binary SL₃ row retains its given marking through degree-one transport. -/
noncomputable def linearThreeTwoActionEquiv
    (F : BinaryField) (hF : F.degree = 1)
    (e : ActionEquiv ρ (linearNatural F 3)) :
    ActionEquiv ρ (linearNatural BinaryField.two 3) :=
  let q := ExtensionConsequences.degreeOneNaturalEquiv F hF 3
  ⟨e.groupEquiv.trans q.groupEquiv, e.linearEquiv.trans q.linearEquiv,
    fun g v => (congrArg q.linearEquiv (e.intertwines g v)).trans
      (q.intertwines (e.groupEquiv g) (e.linearEquiv v))⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
