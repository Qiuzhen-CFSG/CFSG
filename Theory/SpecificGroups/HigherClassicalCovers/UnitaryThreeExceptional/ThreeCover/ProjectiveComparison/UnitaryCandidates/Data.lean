module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.UnitaryGeometry

/-!
# Explicit unitary matrices matching both block generators

Two matrices over the computable field of nine elements preserve the identity
Hermitian form and have determinant one. Their compound matrices act, up to
sign, exactly like the two degree-252 block generators under the displayed
bijection of points. All inverse, unitary, determinant and action identities
are checked in Lean's kernel. Generation of the full projective unitary group
is deliberately not asserted here.

The candidate matrices and labeling were found by a GAP comparison of the
original block group with the exterior action of an explicitly generated
unitary matrix group. This search and its order/isomorphism calculations are
not used as proof oracles. The numerical witnesses are retained in
`ProjectiveComparison/source/unitary-candidate.json`; coefficients [x,y] mean
x+yi with i²=-1. Source: ATLAS U₄(3) numerical data (see `BlockData`), GLS3 §2.7,
and Aschbacher–Smith I.1.4(5), printed p.408.
-/

public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryCandidates
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open Atlas.Order20160A8.Bivectors UnitaryGeometry

set_option Elab.async false

@[expose] def matrixFirst : Matrix (Fin 4) (Fin 4) FiniteField.Nine :=
  ![![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩],
    ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩],
    ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩],
    ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

@[expose] def matrixSecond : Matrix (Fin 4) (Fin 4) FiniteField.Nine :=
  ![![⟨0, 2⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩],
    ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 2⟩],
    ![⟨1, 1⟩, ⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 2⟩]]

@[expose] def adjoint (A : Matrix (Fin 4) (Fin 4) FiniteField.Nine) :
    Matrix (Fin 4) (Fin 4) FiniteField.Nine := fun i j => star (A j i)

theorem first_unitary : adjoint matrixFirst * matrixFirst = 1 := by decide +kernel
theorem first_inverse : matrixFirst * adjoint matrixFirst = 1 := by decide +kernel
theorem first_det : matrixFirst.det = 1 := by decide +kernel
theorem second_unitary : adjoint matrixSecond * matrixSecond = 1 := by decide +kernel
theorem second_inverse : matrixSecond * adjoint matrixSecond = 1 := by decide +kernel
theorem second_det : matrixSecond.det = 1 := by decide +kernel

@[expose] def labelFn (p : BlockAction.Block) : Index :=
  ⟨((1662532054647822789213395742626533912810098724287566694268098715924874106360433875876150043385263896658277111742643760678881370021214133942962693273992628841566923035900736396983918977618652569230006375989651200251621936359372198684393085672327996008720810408148545083022507185815437841834444745258422713380012364149634917224010416841793429724981614631856262418770329503113449775488806626463116587275477944528833593362637999947126719076807223294736665422946807501764727148970993814623093823346772661947345082258277793487230951002180153231438114718898057106590539406094418310092869660564261534670200858597231 : Nat) >>> (8 * p.val)) % 256 % 252, Nat.mod_lt _ (by decide)⟩

@[expose] def labelInv (p : Index) : BlockAction.Block :=
  ⟨((4516059620909541465080322897213049251724313689684361621366018169718921257797628532459155973403596609292468655835793482967796626390868800640690970658647056596542687698251918373794013197624284660890353846690382930988081436521957676562342782336870369674832328560919385163031909953290133807481454307081943782515749992479508217336135394552658642081474386898442617369917673230134934758827687010241890686254764450616101003931851316378456684551164875714967076438271606067339002659242294696532488350450185570568173697636784024258894347128081432418867638823623596501994662143031165129946992029092169065735206141811231 : Nat) >>> (8 * p.val)) % 256 % 252, Nat.mod_lt _ (by decide)⟩

private theorem label_left_inverse : ∀ p, labelInv (labelFn p) = p := by decide +kernel
private theorem label_right_inverse : ∀ p, labelFn (labelInv p) = p := by decide +kernel

/-- One bijection simultaneously matches both original generators. -/
@[expose] def labeling : BlockAction.Block ≃ Index :=
  ⟨labelFn, labelInv, by exact label_left_inverse, by exact label_right_inverse⟩

/-- The first compound matrix has the required action on all 252 nonisotropic lines. -/
theorem matrixFirst_action : ∀ i,
    exteriorMap matrixFirst (point (labeling i)) =
        point (labeling (BlockAction.blockA i)) ∨
    exteriorMap matrixFirst (point (labeling i)) =
        -point (labeling (BlockAction.blockA i)) := by
  decide +kernel

/-- The second compound matrix uses exactly the same labeling and signs. -/
theorem matrixSecond_action : ∀ i,
    exteriorMap matrixSecond (point (labeling i)) =
        point (labeling (BlockAction.blockB i)) ∨
    exteriorMap matrixSecond (point (labeling i)) =
        -point (labeling (BlockAction.blockB i)) := by
  decide +kernel


end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryCandidates
