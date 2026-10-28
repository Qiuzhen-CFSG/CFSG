module
public import CFSG.Quasithin.ChapterA.Section03.RankThreeLocal
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting
public import Theory.GroupTheory.AutomizerEmbedding
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
/-!
# Defining-prime Fitting kernels in the odd ternary embedding branch

A perfect subgroup acts trivially on a solvable induced automizer.
A.3.21(c) supplies that solvability for every cross-characteristic odd
prime subgroup. Every prime dividing the Fitting subgroup of the actual
noncentral A.3.6 component is active, so only the defining prime remains.
This identifies the literal Fitting subgroup with its prime core in both
SL₃(p) and SU₃(p), without assuming a core-support conclusion.

Source: Aschbacher–Smith A.3.21(c) and its nonquasisimple branch, pp.55–56;
used in the actual case-ten argument of Proposition 1.3.8, p.513.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G]

theorem perfect_centralizes_of_solvable_automizer (B Q : Subgroup G)
    [Group.IsPerfect B] (hBQ : B ≤ normalizer (Q : Set G))
    [Group.IsSolvable Q.normalizerMonoidHom.range] : B ≤ centralizer (Q : Set G) := by
  let f := Q.normalizerMonoidHom.rangeRestrict.comp (inclusion hBQ)
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hf : f.range = ⊥ := by
    by_contra h
    let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr h
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have he : f = 1 := MonoidHom.range_eq_bot_iff.mp hf
  intro b hb
  have hk : inclusion hBQ ⟨b,hb⟩ ∈ Q.normalizerMonoidHom.ker := by
    change Q.normalizerMonoidHom _ = 1
    exact congrArg Subtype.val (DFunLike.congr_fun he ⟨b,hb⟩)
  rwa [normalizerMonoidHom_ker] at hk

/-- The cross-characteristic part of the A.3.21 nonquasisimple argument:
a perfect normalizer centralizes each cross-characteristic odd core. -/
theorem rankThree_perfect_centralizes_odd_core
    {p residue : ℕ} (h : RankThreeLocalStructure G p residue)
    {q : ℕ} [Fact q.Prime] (ho : Odd q) (hne : q ≠ p)
    (B Q : Subgroup G) [Group.IsPerfect B] (hQ : IsPGroup q Q)
    (hBQ : B ≤ normalizer (Q : Set G)) : B ≤ centralizer (Q : Set G) := by
  have hs : Group.IsSolvable Q.normalizerMonoidHom.range := by
    rcases h.automizers q ho hne Q hQ with ⟨_,j,hj⟩ | ⟨_,_,hs⟩
    · let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
        let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
        exact Group.isSolvable_of_isSolvable_injective
          (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
      exact Group.isSolvable_of_isSolvable_injective hj
    · exact hs
  let := hs
  exact perfect_centralizes_of_solvable_automizer B Q hBQ

/-- For an actual noncentral-Fitting C-component faithfully embedded in an odd
ternary group, the Fitting subgroup is its defining-prime core. -/
theorem rankThree_fitting_eq_defining_core
    {A : Type*} [Group A] [Finite A] {κ : GroupClass}
    (hA : IsSQTK κ A) (hO : pCore 2 A = ⊥) {B : Subgroup A}
    (hB : B.IsCComponent) (hn : ¬ fittingSubgroup B ≤ center B)
    {p residue : ℕ} [Fact p.Prime] (h : RankThreeLocalStructure G p residue)
    (f : B →* G) (hf : Function.Injective f) : fittingSubgroup B = pCore p B := by
  let : Group.IsPerfect B := hB.perfect
  have hquot := NoncentralFitting.primeSL2FittingQuotient_of_noncentral
    RankActions.primeSL2CoverRigidity hA hO hB hn
  apply NoncentralFitting.CoreShapes.fitting_eq_core_of_support
  intro q hq hd
  let : Fact q.Prime := ⟨hq⟩
  by_contra hne
  have ho : Odd q := (NoncentralFitting.fitting_odd_card hB hO).of_dvd_nat hd
  let Q := (pCore q B).map f
  let D := f.range
  let : Group.IsPerfect D := Group.IsPerfect.range f
  have hDQ : D ≤ normalizer (Q : Set G) := by
    change f.range ≤ normalizer ((pCore q B).map f : Set G)
    rw [MonoidHom.range_eq_map]
    exact (map_mono (show (⊤ : Subgroup B) ≤ normalizer (pCore q B : Set B) by
      rw [(pCore q B).normalizer_eq_top])).trans ((pCore q B).le_normalizer_map f)
  have hc := rankThree_perfect_centralizes_odd_core h ho hne D Q (pCore_isPGroup.map f) hDQ
  apply NoncentralFitting.CoreShapes.core_not_central_of_dvd RankActions.primeSL2CoverRigidity hB hquot hd
  intro b hb
  apply mem_center_iff.mpr
  intro a
  apply hf
  simpa only [map_mul] using ((hc ⟨a,rfl⟩) (f b) (mem_map_of_mem f hb)).symm


/-- A.3.21(c) applied to the exact prime-field special-linear carrier. -/
theorem sl3_fitting_eq_defining_core
    {A : Type*} [Group A] [Finite A] {κ : GroupClass}
    (hA : IsSQTK κ A) (hO : pCore 2 A = ⊥) {B : Subgroup A}
    (hB : B.IsCComponent) (hn : ¬ fittingSubgroup B ≤ center B)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (f : B →* Matrix.SpecialLinearGroup (Fin 3) (ZMod p))
    (hf : Function.Injective f) : fittingSubgroup B = pCore p B :=
  rankThree_fitting_eq_defining_core hA hO hB hn (sl3_local_structure p hp) f hf

/-- A.3.21(c) applied to the source's actual unitary carrier. -/
theorem su3_fitting_eq_defining_core
    {A : Type*} [Group A] [Finite A] {κ : GroupClass}
    (hA : IsSQTK κ A) (hO : pCore 2 A = ⊥) {B : Subgroup A}
    (hB : B.IsCComponent) (hn : ¬ fittingSubgroup B ≤ center B)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (f : B →* RankThreeSU p) (hf : Function.Injective f) :
    fittingSubgroup B = pCore p B :=
  rankThree_fitting_eq_defining_core hA hO hB hn (su3_local_structure p hp) f hf

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
