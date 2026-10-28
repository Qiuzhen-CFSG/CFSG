module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.Faithfulness
public import Theory.SpecificGroups.PSL3.SmallCompletion.PointTransport

/-!
# The literal point comparison between small full-extension completions

Pair both completions and transfer the unique two-edge paths. The resulting
bijection matches the entire left endpoint action, fixes the marked point,
and matches the right endpoint orbit on the marked line. No field coordinates
or group recognition are assumed. Full right equivariance remains a separate
step using the native translation action off the marked line.

Source: Aschbacher–Smith F.3.3–4 and F.4.8, printed pp.270,278
(`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.SmallCompletion
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.Completion
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {E : SourceExtension F} {G H : Type*} [Group G] [Group H]
variable (c : Completion E G) (d : Completion E H)

omit [Finite F] [CharP F 2] in
theorem pair_overlap (ho : c.left.range ⊓ c.right.range = c.middle.range) :
    (c.pairCompletion d).left.range ⊓ (c.pairCompletion d).right.range =
      (c.pairCompletion d).middle.range := by
  let z := c.pairCompletion d
  apply le_antisymm _ (le_inf z.middle_le_left z.middle_le_right)
  rintro a ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  have hxy : c.left x=c.right y := by
    have he := congrArg (c.pairFst d) (hx.trans hy.symm)
    simpa only [z,RankTwoAmalgam.FaithfulCompletion.pairFst_left,
      RankTwoAmalgam.FaithfulCompletion.pairFst_right] using he
  obtain ⟨b,hb⟩ := ho.le
    (show c.left x ∈ c.left.range ⊓ c.right.range from ⟨⟨x,rfl⟩,⟨y,hxy.symm⟩⟩)
  have hbx : E.amalgam.left b = x := c.left_injective hb
  refine ⟨b,?_⟩
  change z.left _ = a
  rw [hbx]
  exact hx

variable (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hd : d.left.range ⊓ d.right.range = d.middle.range)

include hc in
omit [Finite F] [CharP F 2] in
theorem firstCover : CoverData (c.pairCompletion d).cosetFamily c.family (c.pairFst d) :=
  RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
    (by ext x; exact c.pairFst_left d x) (by ext x; exact c.pairFst_right d x)
    (c.pair_overlap d hc) hc

include hc hd in
omit [Finite F] [CharP F 2] in
theorem secondCover : CoverData (c.pairCompletion d).cosetFamily d.family (c.pairSnd d) :=
  RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
    (by ext x; exact c.pairSnd_left d x) (by ext x; exact c.pairSnd_right d x)
    (c.pair_overlap d hc) hd

variable {n : ℕ} (hF : Nat.card F=2^n)
    (dc : ∀v w,c.graph.dist v w≤3) (dd : ∀v w,d.graph.dist v w≤3)

/-- Short paths identify all points while retaining the entire left endpoint action. -/
def pointComparison : Point c.family ≃ Point d.family := by
  let v := base (c.pairCompletion d).cosetFamily false
  have e := PointCoordinates.compare (c.firstCover d hc) (c.secondCover d hc hd)
    c.generated d.generated (c.uniqueGeodesicsBelow_three hc hF)
    (d.uniqueGeodesicsBelow_three hd hF) dc dd v
  exact e

private theorem pointComparison_pair_base :
    c.pointComparison d hc hd hF dc dd ⟨(c.firstCover d hc).vertex
      (base (c.pairCompletion d).cosetFamily false),rfl⟩ =
      ⟨(c.secondCover d hc hd).vertex (base (c.pairCompletion d).cosetFamily false),rfl⟩ :=
  PointCoordinates.compare_base _ _ _ _ _ _ _ _ _

theorem pointComparison_base :
    c.pointComparison d hc hd hF dc dd ⟨base c.family false,rfl⟩ = ⟨base d.family false,rfl⟩ := by
  simpa only [CoverData.vertex_base] using c.pointComparison_pair_base d hc hd hF dc dd

theorem pointComparison_left (a : E.left) (x : Point c.family) :
    c.pointComparison d hc hd hF dc dd (c.left a • x) =
      d.left a • c.pointComparison d hc hd hF dc dd x := by
  let z := c.pairCompletion d
  let a' : stabilizer z.cosetFamily (base z.cosetFamily false) :=
    ⟨z.left a,by
      rw [stabilizer,base,CosetGeometry.stabilizer_base]
      exact ⟨a,rfl⟩⟩
  have h := PointCoordinates.compare_smul (c.firstCover d hc) (c.secondCover d hc hd)
    c.generated d.generated (c.uniqueGeodesicsBelow_three hc hF)
    (d.uniqueGeodesicsBelow_three hd hF) dc dd (base z.cosetFamily false) a' x
  change c.pointComparison d hc hd hF dc dd
    (c.pairFst d ((c.pairCompletion d).left a) • x) =
    c.pairSnd d ((c.pairCompletion d).left a) • c.pointComparison d hc hd hF dc dd x at h
  rw [c.pairFst_left,c.pairSnd_left] at h
  exact h

/-- On the marked line, the comparison also preserves the literal right action. -/
theorem pointComparison_right_base (a : E.right) :
    c.pointComparison d hc hd hF dc dd (c.right a • (⟨base c.family false,rfl⟩ : Point c.family)) =
      d.right a • (⟨base d.family false,rfl⟩ : Point d.family) := by
  let z := c.pairCompletion d
  let v := base z.cosetFamily false
  let l := base z.cosetFamily true
  have hzfix : z.right a • l=l := by
    change z.right a ∈ stabilizer z.cosetFamily l
    rw [stabilizer,show l = base z.cosetFamily true from rfl,base,CosetGeometry.stabilizer_base]
    exact ⟨a,rfl⟩
  have hadj : (RankTwo.graph z.cosetFamily).Adj v l := ⟨Bool.false_ne_true,incident_base _ false true⟩
  by_cases hfix : z.right a • v=v
  · have hcf : c.right a • base c.family false=base c.family false := by
      have h := congrArg (c.firstCover d hc).vertex hfix
      simpa only [z,v,CoverData.vertex_smul,CoverData.vertex_base,
        RankTwoAmalgam.FaithfulCompletion.pairFst_right] using h
    have hdf : d.right a • base d.family false=base d.family false := by
      have h := congrArg (c.secondCover d hc hd).vertex hfix
      simpa only [z,v,CoverData.vertex_smul,CoverData.vertex_base,
        RankTwoAmalgam.FaithfulCompletion.pairSnd_right] using h
    rw [show c.right a • (⟨base c.family false,rfl⟩ : Point c.family)=⟨base c.family false,rfl⟩ from Subtype.ext hcf,
      c.pointComparison_base d hc hd hF dc dd]
    exact Subtype.ext hdf.symm
  · have hnext : (RankTwo.graph z.cosetFamily).Adj l (z.right a • v) := by
      have h := (translationGraphIso z.cosetFamily (z.right a)).toHom.map_adj hadj.symm
      change (RankTwo.graph z.cosetFamily).Adj (z.right a • l) (z.right a • v) at h
      rwa [hzfix] at h
    let p : PointCoordinates.TwoPaths z.cosetFamily v :=
      ⟨⟨⟨l,hadj⟩,⟨⟨z.right a • v,hnext⟩,PUnit.unit⟩⟩,hfix,trivial⟩
    have h := PointCoordinates.compare_path (c.firstCover d hc) (c.secondCover d hc hd)
      c.generated d.generated (c.uniqueGeodesicsBelow_three hc hF)
      (d.uniqueGeodesicsBelow_three hd hF) dc dd v p
    have h₁ : PointCoordinates.endpoint c.family ((c.firstCover d hc).vertex v)
        (some ((c.firstCover d hc).nbPathEquiv 2 v p)) =
        c.right a • (⟨base c.family false,rfl⟩ : Point c.family) := by
      apply Subtype.ext
      change (c.firstCover d hc).vertex (z.right a • v)=c.right a • base c.family false
      rw [CoverData.vertex_smul,CoverData.vertex_base,c.pairFst_right]
    have h₂ : PointCoordinates.endpoint d.family ((c.secondCover d hc hd).vertex v)
        (some ((c.secondCover d hc hd).nbPathEquiv 2 v p)) =
        d.right a • (⟨base d.family false,rfl⟩ : Point d.family) := by
      apply Subtype.ext
      change (c.secondCover d hc hd).vertex (z.right a • v)=d.right a • base d.family false
      rw [CoverData.vertex_smul,CoverData.vertex_base,c.pairSnd_right]
    exact (congrArg (c.pointComparison d hc hd hF dc dd) h₁).symm.trans (h.trans h₂)

end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.Completion
