module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LocalFactorEmbedding

/-!
# The exact center kernel and nonsolvability of an original perfect local factor

When the canonical simple root covers the original quotient Sylow,
LocalFactorEmbedding identifies the two-root-generated group with the
original L_i/O2(L_i). A central element of that quotient fixes every
Sylow-normalizer coset. The original equivariant panel bijection therefore
puts the whole root-group center in the full panel kernel. The converse
is the existing central-cover theorem, so the kernel equals the center.

The root group is nontrivial and perfect. If the actual local permutation
group were solvable, its central-kernel extension would make the root
group solvable too. This excludes the solvable type VI local action
before assuming (2B). PerfectLocalCatalogue discharges the quotient-Sylow
surjectivity premise for every original perfect endpoint.

Source: Fong--Seitz I (2A), (5B)--(5C), pp.7--9,25--26, specialized to
Aschbacher--Smith F.1.1--3. Nonperfect factors and rank-two recognition
are separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  [Finite (L i)] (hp : Group.IsPerfect (L i))
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)

/-- Once the original quotient Sylow is covered, the full root-action kernel
is exactly the center of the root-generated group, before (2B). -/
theorem root_projection_ker_eq_center_of_full_sylow
    (hroot : Function.Surjective (simpleRootSylowProjection Q e h split i hp T hT)) :
    (RootLocalCover.projection Q split i).ker = center (rankOne Q split i) := by
  apply le_antisymm (RootLocalCover.projection_ker_central Q split i)
  intro z hz
  let a := rankOneQuotientEquiv Q e h split i hp T hT hroot
  have hza : a z ∈ center ((L i) ⧸ pCore 2 (L i)) :=
    MulEquivClass.apply_mem_center a hz
  have hfix : ∀ c : ((L i) ⧸ pCore 2 (L i)) ⧸ sylowNormalizer (quotientSylow T), a z • c = c := by
    intro c
    induction c using Quotient.inductionOn with
    | h c =>
      change QuotientGroup.mk (a z * c) = QuotientGroup.mk c
      rw [← mem_center_iff.mp hza c]
      apply QuotientGroup.eq.mpr
      have hn : a z ∈ sylowNormalizer (quotientSylow T) :=
        center_le_normalizer _ hza
      simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using
        (sylowNormalizer (quotientSylow T)).inv_mem hn
  change RootLocalCover.projection Q split i z = 1
  apply Subtype.ext
  ext c
  rw [RootLocalCover.projection_apply, localAction_eq_panelAction]
  obtain ⟨ω,rfl⟩ := (localBorelPanel Q e h i).surjective c
  have he : factorInEndpoint Q e i (rankOneLift Q e h split i hp z) =
      ⟨z,rankOne_le_parabolic Q split i z.property⟩ :=
    Subtype.ext (factorMap_rankOneLift Q e h split i hp z)
  change (⟨z,rankOne_le_parabolic Q split i z.property⟩ :
    Q.tits.standardParabolic {Q.simple i}) • localBorelPanel Q e h i ω = _
  rw [← he, ← localBorelPanel_smul]
  apply congrArg (localBorelPanel Q e h i)
  apply (localBorelCosetEquiv (L i) S T hT).injective
  rw [localBorelCosetEquiv_smul]
  simpa only [a, rankOneQuotientEquiv_apply] using hfix ((localBorelCosetEquiv (L i) S T hT) ω)



/-- A perfect original factor whose quotient Sylow is covered excludes the
solvable local groups of Fong--Seitz (2A)(V)--(VI), without using (2B). -/
theorem localGroup_not_isSolvable_of_full_sylow
    (hroot : Function.Surjective (simpleRootSylowProjection Q e h split i hp T hT)) :
    ¬ Group.IsSolvable (localGroup Q split i) := by
  let : Group.IsPerfect (L i) := hp
  let a := rankOneQuotientEquiv Q e h split i hp T hT hroot
  let : Group.IsPerfect (rankOne Q split i) :=
    Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let : Nontrivial (rankOne Q split i) := (nontrivial_iff_ne_bot _).mpr (by
    intro he
    exact simpleRoot_ne_bot Q split i (eq_bot_iff.mpr
      ((show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left).trans_eq he)))
  intro hsol
  let := hsol
  let p := RootLocalCover.projection Q split i
  let : Group.IsSolvable (center (rankOne Q split i)) := Group.isSolvable_of_comm
    (fun x y => Subtype.ext (mem_center_iff.mp x.property y.val).symm)
  let : Group.IsSolvable p.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (RootLocalCover.projection_ker_central Q split i)) (inclusion_injective _)
  apply Group.IsPerfect.not_isSolvable (rankOne Q split i)
  exact Group.isSolvable_of_ker_le_range p.ker.subtype p (by rw [range_subtype])

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
