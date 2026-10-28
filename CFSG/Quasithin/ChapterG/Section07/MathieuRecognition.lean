module

public import CFSG.Quasithin.ChapterG.Section07.Setup
public import CFSG.Quasithin.ChapterG.Section07.MathieuRecognition.DegreeBounds
public import Theory.Representation.Mathieu.SmallModules.Models
public import Theory.Representation.BinaryIrreducibleRank
public import Theory.Mathieu.M22.Properties.TwoRank
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# Simple Mathieu inputs to G.7.3(2)

The odd-prime degree bounds hold for the actual native carriers, and the
intrinsic M₂₂ and M₂₃ automorphism-rank bounds follow from the certified
Sylow geometry and automorphism coverage. Applied to the source's
irreducibly acting generalized Fitting subgroup, these prove the M₂₃
exclusion and the degree-ten-to-twelve window in the M₂₂ case.

The imported model predicates specify actual group and representation
equivalences for the remaining James recognition inputs. Completeness
for M₁₂, M₂₂ and M₂₄, and the M₁₂ and M₂₄ rank bounds, remain obligations;
this module does not assert the full sporadic alternative of G.7.3(2).

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.7.3(2),
printed p.348 (PDF p.359); James, J. Algebra 27 (1973), 57--111.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section07.MathieuRecognition
open Sporadic.Mathieu Theory.GroupTheory

universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}

/-- The simple M₂₃ branch of G.7.3(2) is impossible under the original (*).
The ambient rank bound is proved from the irreducible action of F*(G). -/
theorem m23_excluded (h : QuasisimpleSetup K ρ)
    (hd : SmallDegree (G := G) (V := V)) :
    ¬ Nonempty (generalizedFitting G ≃* M23) := by
  rintro ⟨e⟩
  let : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype) :=
    h.irreducible
  have hr := Representation.BinaryIrreducibleCentralizer.primeRank_le_automorphisms
    ρ (generalizedFitting G) h.faithful
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  have hu := hr.trans m23_automorphism_twoRank_le_four
  have hl := eleven_le_finrank_of_m23 (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp Subtype.val_injective) e
  unfold SmallDegree at hd
  omega

/-- The source hypotheses force the exact small-degree window needed by
James recognition for the simple M₂₂ branch. -/
theorem m22_degree_window (h : QuasisimpleSetup K ρ)
    (hd : SmallDegree (G := G) (V := V)) (e : generalizedFitting G ≃* M22) :
    10 ≤ Module.finrank (ZMod 2) V ∧ Module.finrank (ZMod 2) V ≤ 12 := by
  let : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype) :=
    h.irreducible
  have hr := Representation.BinaryIrreducibleCentralizer.primeRank_le_automorphisms
    ρ (generalizedFitting G) h.faithful
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  have hu := hr.trans m22_automorphism_twoRank_le_five
  refine ⟨ten_le_finrank_of_m22 (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp Subtype.val_injective) e, ?_⟩
  unfold SmallDegree at hd
  omega

end CFSG.Quasithin.ChapterG.Section07.MathieuRecognition
