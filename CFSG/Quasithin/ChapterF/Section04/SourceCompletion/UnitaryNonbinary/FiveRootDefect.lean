module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveDefect
public import Theory.GroupTheory.SylowKernelCore
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveRoots

/-!
# Native root invariance of the PSU₅(4) completion defect

An automorphism preserving the two marked parabolics preserves their whole
intersection, hence its canonical two-core. The concrete Weyl-intersection
calculations recover both simple roots directly inside that projective
intersection using fourth powers. The scalar kernel of the SU₅ cover is
retained. This proves setwise invariance, leaving pointwise fixation separate.

Source: Aschbacher–Smith F.4.10,16–17, printed pp.279,282–283 of
`refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.UnitaryFive
variable (U : GreenBook.UnitaryFive.Model 4)
variable (t : U.F) (ht : t + U.form.conj t = 1)

/-- The canonical two-core of the actual projective line--plane overlap. -/
def overlapTwoCore : Subgroup U.Carrier := (U.leftParabolic ⊓ U.rightParabolic).pCoreIn 2

/-- Any automorphism preserving both native parabolics preserves the canonical
two-core of their literal projective overlap. -/
theorem constraints_preserve_overlapTwoCore (a : MulAut U.Carrier)
    (ha : SourceExtension.CartanFixedInvolution (point U t ht) (plane U t ht)
      (diagonalCartan U t) a) :
    (overlapTwoCore U).map a.toMonoidHom = overlapTwoCore U := by
  let H : Subgroup U.Carrier := U.leftParabolic ⊓ U.rightParabolic
  have hH : H.map a.toMonoidHom = H := by
    ext b
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨(ha.preserves_left x).2 hx.1, (ha.preserves_right x).2 hx.2⟩
    · intro hb
      refine ⟨a.symm b, ?_, a.apply_symm_apply b⟩
      constructor
      · apply (ha.preserves_left (a.symm b)).mp
        rw [a.apply_symm_apply]
        exact hb.1
      · apply (ha.preserves_right (a.symm b)).mp
        rw [a.apply_symm_apply]
        exact hb.2
  change (H.pCoreIn 2).map a.toMonoidHom = H.pCoreIn 2
  rw [Subgroup.map_pCoreIn_of_injective 2 H a.toMonoidHom a.injective, hH]

/-- The actual PSU₅(4) fourth-power defect preserves the canonical two-core
of the whole projective overlap, including the order-five covering kernel. -/
theorem fourth_defect_preserves_overlapTwoCore
    (t : U.F) (ht : t + U.form.conj t = 1) (E : FiveExtension U)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range = c.middle.range)
    (hcard : Nat.card M ≤ Nat.card E.carrier) :
    ∃ a : E.middle, c.middle a = rotation U t ht E c ^ 4 ∧
      (overlapTwoCore U).map a.val.toMonoidHom = overlapTwoCore U := by
  obtain ⟨a, ha, hfix⟩ := fourth_defect U t ht E c ho hcard
  exact ⟨a, ha, constraints_preserve_overlapTwoCore U t ht a.val hfix⟩


/-- Invariance of both actual relative simple roots, with the nonabelian root
parametrized by its Hermitian relation over the field of sixteen elements. -/
def SimpleRootsInvariant (a : MulAut U.Carrier) : Prop :=
  (∀ x : U.F, ∃ y : U.F,
    a (project U.form (SmallCompletion.FiveRoots.linearRoot U.form t ht U.matrix x))=
      project U.form (SmallCompletion.FiveRoots.linearRoot U.form t ht U.matrix y)) ∧
  (∀ x z : U.F, ∀ hz : z+U.form.conj z=x*U.form.conj x, ∃ y v hv,
    a (project U.form (SmallCompletion.FiveRoots.hermitianRoot U.form U.matrix x z hz))=
      project U.form (SmallCompletion.FiveRoots.hermitianRoot U.form U.matrix y v hv))

/-- The literal Weyl intersections recover root invariance from the existing
defect constraints. The projective proof retains the five-element scalar kernel. -/
theorem constraints_preserve_simpleRoots (a : MulAut U.Carrier)
    (ha : SourceExtension.CartanFixedInvolution (point U t ht) (plane U t ht)
      (diagonalCartan U t) a) : SimpleRootsInvariant U t ht a := by
  have hB (b : U.Carrier) (hb : b∈U.leftParabolic ⊓ U.rightParabolic) :
      a b∈U.leftParabolic ⊓ U.rightParabolic :=
    ⟨(ha.preserves_left b).mpr hb.1,(ha.preserves_right b).mpr hb.2⟩
  exact ⟨SmallCompletion.FiveRoots.preserves_projective_linearRoot
      U.form t ht U.matrix U.conjugation U.card a hB ha.fixes_point ha.fixes_plane,
    SmallCompletion.FiveRoots.preserves_projective_hermitianRoot
      U.form t ht U.matrix U.conjugation U.card a hB ha.fixes_point ha.fixes_plane⟩

/-- The actual fourth-power defect preserves both marked simple roots. -/
theorem fourth_root_defect (E : FiveExtension U)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) :
    ∃ a : E.middle, c.middle a=rotation U t ht E c ^ 4 ∧
      SourceExtension.CartanFixedInvolution (point U t ht) (plane U t ht)
        (diagonalCartan U t) a.val ∧ SimpleRootsInvariant U t ht a.val := by
  obtain ⟨a,ha,hfix⟩ := fourth_defect U t ht E c ho hcard
  exact ⟨a,ha,hfix,constraints_preserve_simpleRoots U t ht a.val hfix⟩

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
