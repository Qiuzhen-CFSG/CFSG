module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.LocalCounts
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Valence
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveNative
public import Theory.GroupAction.RankTwoCosetGeometry.ExtensionGeometry

/-!
# The exceptional unitary-five full-extension census

The actual PSU₅(4) group is centerless, while its SU₅ projection retains
the five scalar matrices. Thus the marked matrix, projective and full
extension coset geometries agree. The native point and plane counts are
17425 and 66625, and their degrees are 65 and 17. Whole-overlap faithful
completions inherit these degrees. The genuine full-extension order bound
then forces distinct nonbacktracking four-walks with a common endpoint,
from either root type. This is a numerical collision, not yet geodesicity
or identification of the Hermitian quadrangle.

Source: Aschbacher–Smith F.4.3–6,13,24, printed pp.274–280,287,
and the fixed PSU₅(4) model in F.1.12(7), printed pp.263–264.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo SimpleGraph SimpleGraph.BasedWalk
open Theory.SpecificGroups.UnitaryFive
variable (U : GreenBook.UnitaryFive.Model 4)

@[expose] def fiveDegree (i : Bool) : ℕ := if i then 17 else 65

@[expose] def fiveCosetCount (i : Bool) : ℕ := if i then 66625 else 17425

theorem five_conj_injective : Function.Injective
    (MulAut.conj : U.Carrier →* MulAut U.Carrier) :=
  SmallCompletion.conj_injective U.form U.card U.conjugation U.matrix

/-- The special-unitary parabolics retain the entire central scalar kernel. -/
abbrev fiveMatrixFamily (i : Bool) : Subgroup U.form.specialSubgroup :=
  if i then specialStabilizer U.form (plane U.F) else specialStabilizer U.form (line U.F)

private theorem five_projection_preimage (i : Bool) :
    (SourceExtension.nativeFamily (P₀ := U.leftParabolic) (P₁ := U.rightParabolic) i).comap
      (project U.form) = fiveMatrixFamily U i := by
  cases i <;> exact Subgroup.comap_map_eq_self (ker_project_le_specialStabilizer U.form _)

private theorem five_projection_representative (a : U.Carrier) :
    ∃ b : U.form.specialSubgroup, (project U.form b)⁻¹*a ∈ U.leftParabolic ⊓ U.rightParabolic := by
  obtain ⟨b,rfl⟩ := project_surjective U.form a
  exact ⟨b,by simp⟩

/-- Projectivization gives a typed graph isomorphism despite its order-five kernel. -/
def fiveProjectionGraphIso : graph (fiveMatrixFamily U) ≃g
    graph (SourceExtension.nativeFamily (P₀ := U.leftParabolic) (P₁ := U.rightParabolic)) :=
  ExtensionGeometry.graphIso _ _ (project U.form)
    (five_projection_preimage U) (five_projection_representative U)

/-- The full extension, including outer automorphisms, has the native projective graph. -/
def fiveGraphIso (E : FiveExtension U) :
    graph (SourceExtension.nativeFamily (P₀ := U.leftParabolic) (P₁ := U.rightParabolic)) ≃g
      graph E.family := E.graphIso (five_conj_injective U)

/-- The actual projective point and plane cosets, with unequal parameters (16,64). -/
theorem five_native_card_coset (i : Bool) :
    Nat.card (U.Carrier ⧸ SourceExtension.nativeFamily
      (P₀ := U.leftParabolic) (P₁ := U.rightParabolic) i) = fiveCosetCount i := by
  have hp : U.leftParabolic.index = 17425 :=
    SmallCompletion.line_index U.form U.card U.conjugation U.matrix
  cases i
  · exact hp
  · have he := (relIndex_mul_index (show U.overlap ≤ U.leftParabolic from inf_le_left)).trans
      (relIndex_mul_index (show U.overlap ≤ U.rightParabolic from inf_le_right)).symm
    rw [show U.overlap.relIndex U.leftParabolic = 65 from U.overlap_index_eq_sixtyFive,
      show U.overlap.relIndex U.rightParabolic = 17 from U.overlap_rightParabolic_index,hp] at he
    change U.rightParabolic.index = 66625
    omega

theorem five_completion_card_neighbors (E : FiveExtension U)
    {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range = c.middle.range) (v : Vertex c.cosetFamily) :
    Nat.card ((graph c.cosetFamily).neighborSet v) = fiveDegree v.type := by
  obtain ⟨a,ha⟩ := exists_smul_base c.cosetFamily v
  have he := Nat.card_congr ((translationGraphIso c.cosetFamily a).mapNeighborSet
    (base c.cosetFamily v.type))
  change Nat.card ((graph c.cosetFamily).neighborSet (base c.cosetFamily v.type)) =
    Nat.card ((graph c.cosetFamily).neighborSet (a • base c.cosetFamily v.type)) at he
  rw [ha] at he
  exact he.symm.trans ((E.completion_card_neighbors_eq_native_of_finite c (five_conj_injective U)
    ho v.type).trans (five_native_card_neighbors U (base _ v.type)))

theorem five_completion_card_coset_le (E : FiveExtension U)
    {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (horder : Nat.card M ≤ Nat.card E.carrier) (i : Bool) :
    Nat.card (M ⧸ c.cosetFamily i) ≤ fiveCosetCount i :=
  (E.completion_card_coset_le_native_of_finite c (five_conj_injective U) horder i).trans_eq
    (five_native_card_coset U i)

/-- The literal branching factors give the four-walk census on either root type. -/
theorem five_completion_card_four_paths (E : FiveExtension U)
    {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range = c.middle.range) (i : Bool) :
    Nat.card {p : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily i) // p.Nonbacktracking} =
      if i then 1114112 else 1064960 := by
  have hc := five_completion_card_neighbors U E c ho
  have (v : Vertex c.cosetFamily) : Finite ((graph c.cosetFamily).neighborSet v) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; cases v.type <;> decide)
  have hf : ∀ {v w : Vertex c.cosetFamily}, (graph c.cosetFamily).Adj v w → w.type = !v.type := by
    intro v w h
    have hh := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have h := card_nonbacktracking_succ (graph c.cosetFamily)
    (fun v : Vertex c.cosetFamily => v.type) fiveDegree hf hc 3 (base c.cosetFamily i)
  change Nat.card {p : BasedWalk (graph c.cosetFamily) (3+1) (base c.cosetFamily i) // p.Nonbacktracking} = _
  rw [h]
  cases i <;> norm_num [fiveDegree,forwardCount,base]

/-- The genuine full-extension order bound forces a collision of four-walks
on either root type. No geodesicity or Hermitian recognition is assumed. -/
theorem five_completion_four_path_collision (E : FiveExtension U)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range = c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) (i : Bool) :
    ∃ p q : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily i),
      p.Nonbacktracking ∧ q.Nonbacktracking ∧ p.endpoint = q.endpoint ∧ p ≠ q := by
  classical
  let : Finite (Vertex c.cosetFamily) := Finite.of_equiv _ (vertexEquivSum c.cosetFamily).symm
  have hv : Nat.card (Vertex c.cosetFamily) ≤ 84050 := by
    rw [Nat.card_congr (vertexEquivSum c.cosetFamily),Nat.card_sum]
    exact Nat.add_le_add (five_completion_card_coset_le U E c horder false)
      (five_completion_card_coset_le U E c horder true)
  have hp : Nat.card (Vertex c.cosetFamily) <
      Nat.card {p : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily i) // p.Nonbacktracking} := by
    rw [five_completion_card_four_paths U E c ho]
    cases i <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  have hn : ¬ Function.Injective (fun p :
      {p : BasedWalk (graph c.cosetFamily) 4 (base c.cosetFamily i) // p.Nonbacktracking} =>
        p.val.endpoint) := by
    intro hi
    exact (Nat.not_le_of_gt hp) (Nat.card_le_card_of_injective _ hi)
  obtain ⟨p,q,he,hne⟩ := Function.not_injective_iff.mp hn
  exact ⟨p.val,q.val,p.property,q.property,he,fun h => hne (Subtype.ext h)⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
