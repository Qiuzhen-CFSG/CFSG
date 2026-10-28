module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.Actual
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Levi
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.GroupTheory.Amalgam.LocalStructure
public import Theory.GroupTheory.PCoreSurjective


/-!
# Quotients and the abelian core of the binary derived G₂ parabolics

The checked root-word realizations identify both actual parabolics with
96 rows. Sending their common generator to a reflection and their cubic
to a rotation defines surjections onto D₆. Multiplicativity follows from
192 checked generator identities and word induction, rather than checking
all 96² products. Each kernel has order 16 and is exactly the two-core.
The existing full-parabolic quotient identifies D₆ with the actual PSL₂(2).

On the second side, rows 3 and 41 give commuting generators of order four.
The explicit 16-row map from C₄ × C₄ is injective and its image is the kernel.
On the first side, the existing marked Q₈ ◦ C₄ isomorphism is retained.
All groups here are the embedded parabolics of the actual commutator group;
no abstract family tag or unproved table realization is used.

Source: Aschbacher--Smith, F.1.12(I)(8), printed p.263 (PDF p.274),
and 14.2.21, printed p.988. The root-word tables and their actual
realization are the licensed ATLAS port cited in the imports; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
open Atlas.G2.LieAutomorphismExtensions
open Atlas.G2.BinaryParabolicPair Atlas.G2.LieParabolicSetup
open Theory.GroupTheory
open scoped MatrixGroups
namespace Atlas.G2.ExceptionalLocalQuotients
noncomputable section

private def rowQuotient (T : WordTable) (i : Fin 96) : DihedralGroup 3 :=
  groupWord (.sr 0) (.r 1) (T.word i)

/-- Generator identities extend to the whole group through its checked positive words. -/
private def quotientHom {G : Type*} [Group G] (T : WordTable) (E : T.Realization G)
    (hT : T.Valid) (h0 : rowQuotient T 0 = 1)
    (hgen : ∀ (b : Bool) i,
      rowQuotient T (T.mul (if b then 2 else 1) i) =
        (if b then DihedralGroup.r 1 else .sr 0) * rowQuotient T i) :
    G →* DihedralGroup 3 := by
  let f : G → DihedralGroup 3 := fun g => rowQuotient T (E.equiv.symm g)
  have fone : f 1 = 1 := by
    change rowQuotient T (E.equiv.symm 1) = 1
    rw [← E.one_eq, E.equiv.symm_apply_apply, h0]
  have step (b : Bool) (g : G) :
      f ((if b then E.equiv 2 else E.equiv 1) * g) =
        (if b then DihedralGroup.r 1 else .sr 0) * f g := by
    obtain ⟨i, rfl⟩ := E.equiv.surjective g
    cases b
    · simpa only [f, Bool.false_eq_true, if_false, ← E.mul_eq,
        E.equiv.symm_apply_apply] using hgen false i
    · simpa only [f, if_true, ← E.mul_eq,
        E.equiv.symm_apply_apply] using hgen true i
  have word (w : List Bool) (g : G) :
      f (groupWord (E.equiv 1) (E.equiv 2) w * g) =
        groupWord (DihedralGroup.sr 0) (.r 1) w * f g := by
    induction w with
    | nil => simp only [groupWord, one_mul]
    | cons b w ih =>
      simp only [groupWord, mul_assoc, step, ih]
  refine { toFun := f, map_one' := fone, map_mul' := ?_ }
  intro x y
  obtain ⟨i, rfl⟩ := E.equiv.surjective x
  rw [← E.word_eq hT i]
  have hw := word (T.word i) (1 : G)
  rw [mul_one, fone, mul_one] at hw
  rw [word, hw]

private theorem left_generators : ∀ (b : Bool) i,
    rowQuotient leftTable (leftTable.mul (if b then 2 else 1) i) =
      (if b then DihedralGroup.r 1 else .sr 0) * rowQuotient leftTable i := by
  decide +kernel

private theorem right_generators : ∀ (b : Bool) i,
    rowQuotient rightTable (rightTable.mul (if b then 2 else 1) i) =
      (if b then DihedralGroup.r 1 else .sr 0) * rowQuotient rightTable i := by
  decide +kernel

/-- The first quotient map is evaluated on the original embedded root words. -/
def firstQuotient : BinaryLeft →* DihedralGroup 3 :=
  quotientHom leftTable binaryConcreteRealization.left left_valid (by decide +kernel)
    left_generators

/-- The second quotient map uses the corresponding long-root word realization. -/
def secondQuotient : BinaryRight →* DihedralGroup 3 :=
  quotientHom rightTable binaryConcreteRealization.right right_valid (by decide +kernel)
    right_generators

private theorem firstQuotient_row (i : Fin 96) :
    firstQuotient (binaryConcreteRealization.left.equiv i) = rowQuotient leftTable i :=
  congrArg (rowQuotient leftTable) (Equiv.symm_apply_apply _ _)

private theorem secondQuotient_row (i : Fin 96) :
    secondQuotient (binaryConcreteRealization.right.equiv i) = rowQuotient rightTable i :=
  congrArg (rowQuotient rightTable) (Equiv.symm_apply_apply _ _)

theorem firstQuotient_surjective : Function.Surjective firstQuotient := by
  intro d
  have hc : ∀ d : DihedralGroup 3, ∃ i : Fin 7,
      rowQuotient leftTable (⟨i.val, by omega⟩ : Fin 96) = d := by decide +kernel
  obtain ⟨i,hi⟩ := hc d
  exact ⟨binaryConcreteRealization.left.equiv ⟨i.val,by omega⟩,
    (firstQuotient_row _).trans hi⟩

theorem secondQuotient_surjective : Function.Surjective secondQuotient := by
  intro d
  have hc : ∀ d : DihedralGroup 3, ∃ i : Fin 7,
      rowQuotient rightTable (⟨i.val, by omega⟩ : Fin 96) = d := by decide +kernel
  obtain ⟨i,hi⟩ := hc d
  exact ⟨binaryConcreteRealization.right.equiv ⟨i.val,by omega⟩,
    (secondQuotient_row _).trans hi⟩

/-- The already checked full short-parabolic quotient identifies D₆ with PSL₂(2). -/
def dihedralEquivPSL : DihedralGroup 3 ≃* PSL(2,ZMod 2) :=
  firstParabolicTwoCoreQuotientEquiv.symm.trans
    ((LocalCoreTransport.quotientEquiv 2 (MulEquiv.subgroupCongr local₁_binary.symm)).trans
      local₁CoreQuotientEquivPSL)

private theorem dihedral_twoCore : pCore 2 (DihedralGroup 3) = ⊥ := by
  let e := dihedralEquivPSL.trans (longSLEquivPSL (F := ZMod 2)).symm
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [pCore_map_iso, Subgroup.map_bot, Matrix.SL2.twoCore_eq_bot]

private theorem kernel_card {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 96) (f : G →* DihedralGroup 3) (hf : Function.Surjective f) :
    Nat.card f.ker = 16 := by
  have hc := f.ker.card_mul_index
  have he : f.ker.index = 6 := by
    change Nat.card (G ⧸ f.ker) = 6
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [he, hG] at hc
  omega

theorem firstQuotient_ker : firstQuotient.ker = pCore 2 BinaryLeft := by
  have he := firstQuotient.comap_pCore_of_ker_isPGroup firstQuotient_surjective
    (IsPGroup.of_card (p := 2) (n := 4) (kernel_card card_binaryLeft _ firstQuotient_surjective))
  simpa only [dihedral_twoCore, MonoidHom.comap_bot] using he

theorem secondQuotient_ker : secondQuotient.ker = pCore 2 BinaryRight := by
  have he := secondQuotient.comap_pCore_of_ker_isPGroup secondQuotient_surjective
    (IsPGroup.of_card (p := 2) (n := 4) (kernel_card card_binaryRight _ secondQuotient_surjective))
  simpa only [dihedral_twoCore, MonoidHom.comap_bot] using he

/-- The actual first derived parabolic quotient, not just its order. -/
def firstCoreQuotientEquiv : BinaryLeft ⧸ pCore 2 BinaryLeft ≃* PSL(2,ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq firstQuotient_ker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective firstQuotient
      firstQuotient_surjective).trans dihedralEquivPSL)

def secondCoreQuotientEquiv : BinaryRight ⧸ pCore 2 BinaryRight ≃* PSL(2,ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq secondQuotient_ker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective secondQuotient
      secondQuotient_surjective).trans dihedralEquivPSL)

/-- The literal product of two cyclic groups of order four. -/
abbrev C4Square := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)

private def squareRow (x : C4Square) : Fin 96 :=
  (![![0,41,19,79], ![3,76,50,94], ![14,93,23,62], ![46,57,54,44]] :
    Fin 4 → Fin 4 → Fin 96) x.1.toAdd x.2.toAdd

private theorem squareRow_mul : ∀ x y,
    squareRow (x*y) = rightTable.mul (squareRow x) (squareRow y) := by
  decide +kernel

private theorem squareRow_injective : Function.Injective squareRow := by decide +kernel

private theorem squareRow_kernel : ∀ x, rowQuotient rightTable (squareRow x) = 1 := by
  decide +kernel

/-- Explicit C₄ × C₄ inside the second embedded parabolic, generated by rows 3 and 41. -/
def secondCoreEmbedding : C4Square →* BinaryRight where
  toFun x := binaryConcreteRealization.right.equiv (squareRow x)
  map_one' := binaryConcreteRealization.right.one_eq
  map_mul' x y := by rw [squareRow_mul, binaryConcreteRealization.right.mul_eq]

theorem secondCoreEmbedding_injective : Function.Injective secondCoreEmbedding :=
  binaryConcreteRealization.right.equiv.injective.comp squareRow_injective

private def secondCoreToKernel : C4Square →* secondQuotient.ker :=
  secondCoreEmbedding.codRestrict _ (fun x =>
    (secondQuotient_row (squareRow x)).trans (squareRow_kernel x))

/-- The intrinsic second two-core is the displayed C₄ × C₄, through the original rows. -/
def secondCoreEquiv : pCore 2 BinaryRight ≃* C4Square :=
  (MulEquiv.subgroupCongr secondQuotient_ker.symm).trans
    (MulEquiv.ofBijective secondCoreToKernel
      ((show Function.Injective secondCoreToKernel from
        fun x y h => secondCoreEmbedding_injective (congrArg Subtype.val h)).bijective_of_nat_card_le
          (by rw [kernel_card card_binaryRight secondQuotient secondQuotient_surjective]
              rw [Nat.card_eq_fintype_card]
              decide +kernel))).symm

/-- The word-table left group is the already marked restricted first parabolic. -/
def firstMarkedEquiv : BinaryLeft ≃* derivedFirst :=
  MulEquiv.subgroupCongr (by
    change (parabolic₁ (F := ZMod 2)).subgroupOf DerivedModel = _
    rw [parabolic₁_binary]
    rfl)

/-- Restriction of the previously constructed quaternion--cyclic core identification. -/
def firstCoreEquiv : pCore 2 BinaryLeft ≃* QuaternionCyclic.Model :=
  (LocalCoreTransport.coreEquiv 2 firstMarkedEquiv).trans derivedIntrinsicCoreEquiv

/-- The quotient identification on the original first-parabolic API. -/
def derivedFirstQuotientEquiv : derivedFirst ⧸ pCore 2 derivedFirst ≃* PSL(2,ZMod 2) :=
  (LocalCoreTransport.quotientEquiv 2 firstMarkedEquiv.symm).trans firstCoreQuotientEquiv

/-- The word-table right group is definitionally the original second parabolic. -/
def derivedSecondQuotientEquiv : derivedSecond ⧸ pCore 2 derivedSecond ≃* PSL(2,ZMod 2) :=
  secondCoreQuotientEquiv

def derivedSecondCoreEquiv : pCore 2 derivedSecond ≃* C4Square := secondCoreEquiv

/-- The inverse core equivalence has precisely the displayed embedded root words. -/
@[simp] theorem secondCoreEquiv_symm_val (x : C4Square) :
    (secondCoreEquiv.symm x).val = secondCoreEmbedding x := (rfl)

/-- Both quotient equivalences retain their actual quotient homomorphisms. -/
@[simp] theorem firstCoreQuotientEquiv_mk (x : BinaryLeft) :
    firstCoreQuotientEquiv (QuotientGroup.mk x) = dihedralEquivPSL (firstQuotient x) := (rfl)

@[simp] theorem secondCoreQuotientEquiv_mk (x : BinaryRight) :
    secondCoreQuotientEquiv (QuotientGroup.mk x) = dihedralEquivPSL (secondQuotient x) := (rfl)

end
end Atlas.G2.ExceptionalLocalQuotients
