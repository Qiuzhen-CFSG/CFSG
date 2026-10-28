module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.RankTwo
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Excluding the full even special-linear-three covering row

The two projective parabolics lift through the actual central quotient.
A proper subgroup of a perfect group cannot surject modulo a central kernel,
and solvability of the parabolic intersection lifts through that kernel.
Thus the lifted pair still exhausts proper full-Sylow overgroups. The original
odd-action argument then excludes the full special-linear quotient, including
its scalar center. The final escape application uses the same component and
quotient as the J₁ recognition owner qt-d-1222-natural-line-action.

Source: Aschbacher--Smith, A.3.12 and 3.3.12, pp.47--48,589--590.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

private theorem two_sylow_overgroups_of_perfect_central_quotient
    {H K : Type*} [Group H] [Group K] [Finite H] [Group.IsPerfect H]
    (q : H →* K) (hq : Function.Surjective q) (hz : q.ker ≤ center H)
    (geometry : ∀ U : Sylow 2 K, ∃ P Q : Subgroup K,
      IsCoatom P ∧ IsCoatom Q ∧ (U : Subgroup K) ≤ P ∧ (U : Subgroup K) ≤ Q ∧
      Group.IsSolvable (P ⊓ Q : Subgroup K) ∧
      ∀ J : Subgroup K, (U : Subgroup K) ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q)
    (U : Sylow 2 H) :
    ∃ P Q : Subgroup H, IsCoatom P ∧ IsCoatom Q ∧
      (U : Subgroup H) ≤ P ∧ (U : Subgroup H) ≤ Q ∧
      Group.IsSolvable (P ⊓ Q : Subgroup H) ∧
      ∀ J : Subgroup H, (U : Subgroup H) ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q := by
  obtain ⟨P,Q,hP,hQ,hUP,hUQ,hsol,hcover⟩ := geometry (U.mapSurjective hq)
  refine ⟨P.comap q,Q.comap q,isCoatom_comap_of_surjective hq hP,
    isCoatom_comap_of_surjective hq hQ,map_le_iff_le_comap.mp hUP,
    map_le_iff_le_comap.mp hUQ,?_,?_⟩
  · let B := P.comap q ⊓ Q.comap q
    let a : B →* (P ⊓ Q : Subgroup K) := (q.comp B.subtype).codRestrict _ (fun x => x.property)
    have hk : a.ker ≤ center B := by
      intro x hx
      have hh : (x : H) ∈ q.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_center_iff.mp (hz hh) y.val)
    let : Group.IsSolvable a.ker := Group.isSolvable_of_comm (fun x y =>
      Subtype.ext (mem_center_iff.mp (hk y.property) x.val))
    let := hsol
    exact Group.isSolvable_of_ker_le_range a.ker.subtype a (by simp)
  · intro J hUJ hJ
    have hm : J.map q ≠ ⊤ := by
      intro he
      apply hJ
      apply top_unique
      apply perfect_le_of_map_le_of_central_kernel q hz (⊤ : Subgroup H) J
      rw [he]
      exact le_top
    rcases hcover (J.map q) (map_mono hUJ) hm with hp | hq
    · exact .inl (map_le_iff_le_comap.mp hp)
    · exact .inr (map_le_iff_le_comap.mp hq)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- The scalar center is retained: even special-linear-three covers are
excluded by lifting the genuine projective parabolics through the center. -/
theorem quotient_not_even_special_linear_three {n : ℕ} (hn : 1 ≤ n) :
    ¬ Chapter1.Section02.LocalModels.IsSL (E.component ⧸ pCore 2 E.component) 3 (2^n) := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect (E.component ⧸ pCore 2 E.component) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let q : (E.component ⧸ pCore 2 E.component) →* PSL(3,F) :=
    (QuotientGroup.mk' (center SL(3,F))).comp e.toMonoidHom
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hz : q.ker ≤ center (E.component ⧸ pCore 2 E.component) := by
    intro x hx
    have he : e x ∈ center SL(3,F) := (QuotientGroup.eq_one_iff _).mp hx
    have hh := (centerCongr e.symm ⟨e x,he⟩).property
    change e.symm (e x) ∈ center _ at hh
    simpa only [e.symm_apply_apply] using hh
  exact E.false_of_two_sylow_overgroups
    (two_sylow_overgroups_of_perfect_central_quotient q hq hz
      (Matrix.PSL3.LinearThree.OddSupplement.two_sylow_overgroups_of_equiv hF hn (MulEquiv.refl _)))

end MovedComponent

/-- The original normalizer escape excludes the complete even linear-three
covering family in its literal component two-core quotient. -/
theorem exists_moved_component_not_even_special_linear_three (f : InvariantFlag c)
    (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A, ∀ n, 1 ≤ n →
      ¬ Chapter1.Section02.LocalModels.IsSL (E.component ⧸ pCore 2 E.component) 3 (2^n) := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,fun _ hn => E.quotient_not_even_special_linear_three hn⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
