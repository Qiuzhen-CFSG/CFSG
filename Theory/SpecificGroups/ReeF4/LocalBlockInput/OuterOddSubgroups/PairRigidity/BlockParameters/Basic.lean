module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.Basic

/-!
# Diagonal parameters for the four Ree simple blocks

The inverse F₄ Cartan matrix has integral entries. Hence arbitrary nonzero
scales on its four simple roots determine an explicit diagonal matrix on the
Chevalley lattice. The integral torus conjugation formula proves its action
on every split root curve. If the scales respect the exceptional long–short
parameter powers, conjugation commutes with the supplied twist and restricts
to the actual fixed group, preserving each of the four signed simple blocks.

This does not yet put the diagonal matrix in the root-generated fixed group.
Nor does it assert that an arbitrary block-preserving automorphism has a
common field action. These are separate obligations. The final cancellation
lemma exposes precisely the matrix realization needed after that action has
been proved. The scalar normalization lemma recovers a field automorphism
from an additive parameter equivalence and a scaled multiplication identity.

Sources: GLS3, Table 2.4 (types V and VI), 2.4.7, and 2.5.1(b,c),
in `refs/KGroup/GLS3/chapter2.tex`. All parameter powers use `d.twist_root`;
on long roots the exponent is `2^m`, on short roots it is `2^(m+1)`.
The conjugation convention is `T⁻¹ * x * T`, so its eventual inner
representative is the inverse diagonal matrix.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open LargeLocalSeeds Subgroup
variable {m : ℕ}

/-- Simple-coroot coordinates of the integral F₄ diagonal torus. -/
abbrev TorusParameters (m : ℕ) :=
  IntegralChevalleyTorusParameter (b := typeF4RootPairing_base) (CoefficientField m)

/-- The concrete diagonal unit on the Cartan-plus-root lattice. -/
def torusMatrix (u : TorusParameters m) : MatrixUnits m :=
  F4Chevalley.torusConjugation.torusElement u

/-- The root character evaluated at the torus parameters. -/
def rootScale (u : TorusParameters m) (r : F4Chevalley.Root) :
    (CoefficientField m)ˣ :=
  integralChevalleyRootScale (P := typeF4RootPairing) u r

/-- Compatibility with the supplied twist, including its unequal root powers. -/
def TwistCompatible (u : TorusParameters m) : Prop :=
  ∀ r : F4Chevalley.Root,
    exceptionalParameter r ((rootScale u r : CoefficientField m) ^ (2 ^ m)) =
      (rootScale u (exceptionalRootPermutation r) : CoefficientField m)

theorem rootScale_simple (u : TorusParameters m) (i : Fin 4) :
    rootScale u (typeF4SimpleRootIndex i) =
      ∏ j : Fin 4, u (typeF4RootPairing_baseEquiv j) ^ typeF4CartanMatrix i j := by
  rw [rootScale, integralChevalleyRootScale,
    ← typeF4RootPairing_baseEquiv.prod_comp]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  exact typeF4RootPairing_base_cartan_apply i j

/-- Solve the four simple-root character equations using the inverse Cartan matrix. -/
def torusParametersOfSimpleScales
    (c : Fin 4 → (CoefficientField m)ˣ) : TorusParameters m := fun q =>
  ![c 0 ^ 2 * c 1 ^ 3 * c 2 ^ 4 * c 3 ^ 2,
    c 0 ^ 3 * c 1 ^ 6 * c 2 ^ 8 * c 3 ^ 4,
    c 0 ^ 2 * c 1 ^ 4 * c 2 ^ 6 * c 3 ^ 3,
    c 0 * c 1 ^ 2 * c 2 ^ 3 * c 3 ^ 2]
    (typeF4RootPairing_baseEquiv.symm q)

/-- The chosen diagonal parameters realize every specified simple-root scale. -/
theorem rootScale_torusParametersOfSimpleScales
    (c : Fin 4 → (CoefficientField m)ˣ) (i : Fin 4) :
    rootScale (torusParametersOfSimpleScales c) (typeF4SimpleRootIndex i) = c i := by
  rw [rootScale_simple, Fin.prod_univ_four]
  simp only [torusParametersOfSimpleScales, Equiv.symm_apply_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  fin_cases i <;> norm_num [typeF4CartanMatrix, Fin.ext_iff]
  all_goals
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
    <;> ring_nf
    <;> rfl

theorem torusMatrix_conjugation (u : TorusParameters m)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    (torusMatrix u)⁻¹ * F4Chevalley.rootCurve r t * torusMatrix u =
      F4Chevalley.rootCurve r ((rootScale u r : CoefficientField m) * t) :=
  F4Chevalley.rootCurve_torus_conjugation u r t

def matrixTorusConj (u : TorusParameters m) : MulAut (MatrixUnits m) :=
  MulAut.conj (torusMatrix u)⁻¹

theorem matrixTorusConj_apply (u : TorusParameters m) (x : MatrixUnits m) :
    matrixTorusConj u x = (torusMatrix u)⁻¹ * x * torusMatrix u := by
  simp only [matrixTorusConj, MulAut.conj_apply, inv_inv]

theorem matrixTorusConj_root (u : TorusParameters m)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    matrixTorusConj u (F4Chevalley.rootCurve r t) =
      F4Chevalley.rootCurve r ((rootScale u r : CoefficientField m) * t) := by
  rw [matrixTorusConj_apply, torusMatrix_conjugation]

theorem matrixTorusConj_mem (u : TorusParameters m) {x : MatrixUnits m}
    (hx : x ∈ SplitGroup m) : matrixTorusConj u x ∈ SplitGroup m := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨⟨r, t⟩, rfl⟩ := hx
      simpa only [rootGenerator_apply, matrixTorusConj_root] using
        rootGenerator_mem m (r, (rootScale u r : CoefficientField m) * t)
  | one => simp
  | mul x y _ _ hx hy => simpa using (SplitGroup m).mul_mem hx hy
  | inv x _ hx => simpa using (SplitGroup m).inv_mem hx

def splitTorusConjHom (u : TorusParameters m) : SplitGroup m →* SplitGroup m :=
  ((matrixTorusConj u).toMonoidHom.comp (SplitGroup m).subtype).codRestrict
    (SplitGroup m) (fun x => matrixTorusConj_mem u x.property)

theorem splitTorusConjHom_injective (u : TorusParameters m) :
    Function.Injective (splitTorusConjHom u) := by
  intro x y h
  apply Subtype.ext
  exact (matrixTorusConj u).injective (congrArg Subtype.val h)

/-- Diagonal conjugation on the actual root-generated split carrier. -/
def splitTorusConj (u : TorusParameters m) : MulAut (SplitGroup m) :=
  MulEquiv.ofBijective (splitTorusConjHom u)
    (Finite.injective_iff_bijective.mp (splitTorusConjHom_injective u))

theorem splitTorusConj_coe (u : TorusParameters m) (x : SplitGroup m) :
    (splitTorusConj u x).val = (torusMatrix u)⁻¹ * x.val * torusMatrix u :=
  matrixTorusConj_apply u x.val

theorem splitTorusConj_root (u : TorusParameters m)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    splitTorusConj u (rootGeneratorInGroup m r t) =
      rootGeneratorInGroup m r ((rootScale u r : CoefficientField m) * t) :=
  Subtype.ext (matrixTorusConj_root u r t)

private theorem exceptionalParameter_mul (r : F4Chevalley.Root)
    (t v : CoefficientField m) :
    exceptionalParameter r (t * v) =
      exceptionalParameter r t * exceptionalParameter r v := by
  classical
  by_cases hr : IsLongRoot r
  · simp only [exceptionalParameter_of_long hr]
  · simp only [exceptionalParameter_of_short hr, mul_pow]

/-- Root-character compatibility makes diagonal conjugation commute with the twist. -/
theorem splitTorusConj_commutes_twist (d : LocalBlockInput m)
    (u : TorusParameters m) (hu : TwistCompatible u) :
    (splitTorusConj u).toMonoidHom.comp d.twist.toMonoidHom =
      d.twist.toMonoidHom.comp (splitTorusConj u).toMonoidHom := by
  apply splitGroup_hom_ext
  intro r t
  change splitTorusConj u (d.twist (rootGeneratorInGroup m r t)) =
    d.twist (splitTorusConj u (rootGeneratorInGroup m r t))
  rw [d.twist_root, splitTorusConj_root, splitTorusConj_root, d.twist_root,
    mul_pow, exceptionalParameter_mul, hu r]

theorem splitTorusConj_mem_fixed (d : LocalBlockInput m)
    (u : TorusParameters m) (hu : TwistCompatible u)
    {x : SplitGroup m} (hx : x ∈ d.fixedGroup) :
    splitTorusConj u x ∈ d.fixedGroup := by
  change d.twist (splitTorusConj u x) = splitTorusConj u x
  have he := DFunLike.congr_fun (splitTorusConj_commutes_twist d u hu) x
  change splitTorusConj u (d.twist x) = d.twist (splitTorusConj u x) at he
  rw [(d.mem_fixedGroup x).mp hx] at he
  exact he.symm

def fixedTorusConjHom (d : LocalBlockInput m)
    (u : TorusParameters m) (hu : TwistCompatible u) : d.fixedGroup →* d.fixedGroup :=
  ((splitTorusConj u).toMonoidHom.comp d.fixedGroup.subtype).codRestrict
    d.fixedGroup (fun x => splitTorusConj_mem_fixed d u hu x.property)

theorem fixedTorusConjHom_injective (d : LocalBlockInput m)
    (u : TorusParameters m) (hu : TwistCompatible u) :
    Function.Injective (fixedTorusConjHom d u hu) := by
  intro x y h
  apply Subtype.ext
  exact (splitTorusConj u).injective (congrArg Subtype.val h)

/-- Restriction to the fixed carrier; no assertion of innerness is made here. -/
def fixedTorusConj (d : LocalBlockInput m)
    (u : TorusParameters m) (hu : TwistCompatible u) : MulAut d.fixedGroup :=
  MulEquiv.ofBijective (fixedTorusConjHom d u hu)
    (Finite.injective_iff_bijective.mp (fixedTorusConjHom_injective d u hu))

theorem fixedTorusConj_coe (d : LocalBlockInput m)
    (u : TorusParameters m) (hu : TwistCompatible u) (x : d.fixedGroup) :
    (fixedTorusConj d u hu x).val.val =
      (torusMatrix u)⁻¹ * x.val.val * torusMatrix u :=
  splitTorusConj_coe u x.val

private theorem splitTorusConj_mem_closure (u : TorusParameters m)
    (P : F4Chevalley.Root → Prop) {x : SplitGroup m}
    (hx : x ∈ closure {y | ∃ (r : F4Chevalley.Root) (t : CoefficientField m),
      P r ∧ y = rootGeneratorInGroup m r t}) :
    splitTorusConj u x ∈ closure
      {y | ∃ (r : F4Chevalley.Root) (t : CoefficientField m),
        P r ∧ y = rootGeneratorInGroup m r t} := by
  let H : Subgroup (SplitGroup m) := closure
    {y | ∃ (r : F4Chevalley.Root) (t : CoefficientField m),
      P r ∧ y = rootGeneratorInGroup m r t}
  have hle : H ≤ H.comap (splitTorusConj u).toMonoidHom := by
    apply (closure_le _).mpr
    rintro y ⟨r, t, hr, rfl⟩
    change splitTorusConj u (rootGeneratorInGroup m r t) ∈ H
    rw [splitTorusConj_root]
    exact subset_closure ⟨r, _, hr, rfl⟩
  exact hle hx

/-- Compatible diagonal conjugation preserves each signed fixed block. -/
theorem fixedTorusConj_preservesSimpleBlocks (d : LocalBlockInput m)
    (u : TorusParameters m) (hu : TwistCompatible u) :
    PreservesSimpleBlocks d (fixedTorusConj d u hu) := by
  intro s positive
  let H := simpleBlock d s positive
  let a := fixedTorusConj d u hu
  have hm : ∀ x ∈ H, a x ∈ H := by
    intro x hx
    exact splitTorusConj_mem_closure u (IsSimpleBlockRoot s positive) hx
  let f : H →* H := (a.toMonoidHom.comp H.subtype).codRestrict H
    (fun x => hm x x.property)
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (a.injective (congrArg Subtype.val h))
  have hs := (Finite.injective_iff_bijective.mp hf).surjective
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hm y hy
  · intro x hx
    obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
    exact ⟨y, y.property, congrArg Subtype.val hy⟩

/-- Apply a coefficient-field automorphism to every entry of a matrix unit. -/
def matrixFieldMap (σ : CoefficientField m ≃+* CoefficientField m) :
    MatrixUnits m →* MatrixUnits m :=
  Units.map σ.toRingHom.mapMatrix.toMonoidHom

theorem matrixFieldMap_entry (σ : CoefficientField m ≃+* CoefficientField m)
    (x : MatrixUnits m) (i j : F4Chevalley.BasisIndex) :
    (matrixFieldMap σ x : MatrixCarrier m) i j = σ ((x : MatrixCarrier m) i j) := rfl

/-- The exact matrix formula to be derived from the four block actions.
This is an explicit intermediate property, not a hypothesis of the final theorem. -/
def HasTorusFieldAction (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (u : TorusParameters m) (σ : CoefficientField m ≃+* CoefficientField m) : Prop :=
  ∀ s positive, ∀ x ∈ simpleBlock d s positive,
    (a x).val.val = (torusMatrix u)⁻¹ * matrixFieldMap σ x.val.val * torusMatrix u

/-- Normalize an additive parameter equivalence whose product defect is its value at one. -/
theorem exists_fieldEquiv_of_scaled_multiplicative
    (f : CoefficientField m ≃+ CoefficientField m)
    (hmul : ∀ t v, f (t * v) * f 1 = f t * f v) :
    ∃ σ : CoefficientField m ≃+* CoefficientField m,
      ∀ t, f t = f 1 * σ t := by
  have h1 : f 1 ≠ 0 := by
    intro h
    have he : f 1 = f 0 := h.trans (map_zero f).symm
    exact one_ne_zero (f.injective he)
  let g : CoefficientField m →+* CoefficientField m :=
    { toFun := fun t => f t / f 1
      map_zero' := by simp
      map_one' := div_self h1
      map_add' := fun t v => by simp only [map_add, add_div]
      map_mul' := fun t v => by
        rw [div_mul_div_comm, ← hmul t v]
        field_simp }
  refine ⟨RingEquiv.ofBijective g (Finite.injective_iff_bijective.mp g.injective), ?_⟩
  intro t
  change f t = f 1 * (f t / f 1)
  field_simp

/-- Cancel a realized diagonal adjustment, leaving entrywise field action.
Both the field-action formula and the actual fixed-group representative are explicit inputs. -/
theorem entries_of_torus_realization (d : LocalBlockInput m)
    (a : MulAut d.fixedGroup) (u : TorusParameters m)
    (σ : CoefficientField m ≃+* CoefficientField m)
    (ha : HasTorusFieldAction d a u σ)
    (g : d.fixedGroup) (hg : g.val.val = (torusMatrix u)⁻¹) :
    ∀ s positive, ∀ x ∈ simpleBlock d s positive,
      ∀ i j : F4Chevalley.BasisIndex,
        ((((MulAut.conj g)⁻¹ * a) x).val.val : MatrixCarrier m) i j =
          σ ((x.val.val : MatrixCarrier m) i j) := by
  intro s positive x hx i j
  have he : (((MulAut.conj g)⁻¹ * a) x).val.val = matrixFieldMap σ x.val.val := by
    change g.val.val⁻¹ * (a x).val.val * g.val.val = _
    rw [ha s positive x hx, hg, inv_inv]
    group
  rw [he, matrixFieldMap_entry]

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters

end
