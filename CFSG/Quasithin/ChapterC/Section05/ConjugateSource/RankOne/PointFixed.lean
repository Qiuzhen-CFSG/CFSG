module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Setup
/-!
# A single noncentral actor detects the full fixed space

In the original natural-action coordinates, a nonzero transvection parameter
forces the second coordinate of a fixed vector to vanish. All Baumann actors
then fix its projection, and intrinsic fixed-point lifting fixes the vector
in the full cover, retaining its central layer.

Source application: Aschbacher–Smith, Lemma 2.4.8(7), printed p.531.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {R L : Subgroup G} {F : Type*} [Field F]

/-- A noncentral Baumann actor detects the common fixed space in the full cover. -/
theorem Setup.fixed_by_noncentral_imp_fixed_by_all (h : Setup R L F)
    (a : S R) (ha : (a:G) ∉ centralizer (U L : Set G))
    (v : U L) (hv : moduleConjugate h.coordinates.normalizes a v=v) :
    (v:G) ∈ centralizer (S R : Set G) := by
  let c := h.coordinates
  have hap : (c.parameter a).toAdd ≠ 0 := by
    intro he
    apply ha
    exact (c.parameter_kernel a).mp (Multiplicative.toAdd.injective he)
  have hvp : (c.projection v).toAdd 1=0 := by
    have he := congrFun (c.equivariant a v) 0
    rw [hv] at he
    simp only [Matrix.cons_val_zero] at he
    have hzero : (c.parameter a).toAdd * (c.projection v).toAdd 1 = 0 := by
      have hh := congrArg (fun z => z - (c.projection v).toAdd 0) he
      simpa using hh.symm
    exact (mul_eq_zero.mp hzero).resolve_left hap
  apply mem_centralizer_iff.mpr
  intro b hb
  have hp : c.projection (moduleConjugate c.normalizes ⟨b,hb⟩ v)=c.projection v := by
    apply Multiplicative.toAdd.injective
    rw [c.equivariant,hvp]
    ext i
    fin_cases i <;> simp [hvp]
  have he := congrArg Subtype.val (h.fixedLift ⟨b,hb⟩ v hp)
  exact mul_inv_eq_iff_eq_mul.mp he
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
