module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.AmbientCoordinates
public import Mathlib.Tactic.FinCases

/-!
# The embedded source subgroups for Janko Case III

The subgroups are formed using the original kernel and complement embeddings:
`sourceH = E<a,b>` and `sourceT = E<a,b,d>`. The source vector `z1` is
identified with the original central involution, using the center of its
actual centralizer. No Sylow status or cardinality is assumed here.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 1, pp.2–3, DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseThreeExclusion
open Subgroup
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K)
  (R : JankoCoordinates (D.binaryAction K hK) .three)

/-- The source elementary kernel, with its actual ambient embedding. -/
@[expose] public noncomputable def sourceE : Subgroup G := (R.ambientBasis D K hK).range

/-- The source subgroup `E<a,b>`. -/
@[expose] public noncomputable def sourceH : Subgroup G :=
  sourceE D K hK R ⊔ closure
    ({jankoAmbientComplement D K hK jankoA,
      jankoAmbientComplement D K hK jankoB} : Set G)

/-- A literal coordinate word in `E<a,b>`, with binary source exponents. -/
@[expose] public noncomputable def sourceHWord (v : BinaryFour) (i j : Fin 2) : G :=
  R.ambientBasis D K hK v *
    jankoAmbientComplement D K hK (jankoA ^ i.val * jankoB ^ j.val)

/-- Every source word belongs to the actual generated subgroup. -/
public theorem sourceHWord_mem (v : BinaryFour) (i j : Fin 2) :
    sourceHWord D K hK R v i j ∈ sourceH D K hK R := by
  have ha : jankoAmbientComplement D K hK jankoA ∈ sourceH D K hK R :=
    (show closure ({jankoAmbientComplement D K hK jankoA,
      jankoAmbientComplement D K hK jankoB} : Set G) ≤ sourceH D K hK R from
        le_sup_right) (subset_closure (Set.mem_insert _ _))
  have hb : jankoAmbientComplement D K hK jankoB ∈ sourceH D K hK R :=
    (show closure ({jankoAmbientComplement D K hK jankoA,
      jankoAmbientComplement D K hK jankoB} : Set G) ≤ sourceH D K hK R from
        le_sup_right) (subset_closure (Set.mem_insert_of_mem _ rfl))
  have hv : R.ambientBasis D K hK v ∈ sourceH D K hK R :=
    (show sourceE D K hK R ≤ sourceH D K hK R from le_sup_left) ⟨v, rfl⟩
  simpa only [sourceHWord, map_mul, map_pow] using
    (sourceH D K hK R).mul_mem hv
      ((sourceH D K hK R).mul_mem ((sourceH D K hK R).pow_mem ha i.val)
        ((sourceH D K hK R).pow_mem hb j.val))

/-- The source subgroup `E<a,b,d>`, without an identification with `D.sylow`. -/
@[expose] public noncomputable def sourceT : Subgroup G :=
  sourceH D K hK R ⊔ zpowers (jankoAmbientComplement D K hK jankoD)

/-- The literal source vector `z1`. -/
@[expose] public noncomputable def sourceZ : G :=
  R.ambientBasis D K hK (Multiplicative.ofAdd ![1, 0, 0, 0])

/-- The index-two candidate is a subgroup of the source two-group candidate. -/
public theorem sourceH_le_sourceT : sourceH D K hK R ≤ sourceT D K hK R := le_sup_left

/-- The complement involution belongs to the source two-group candidate. -/
public theorem sourceD_mem_sourceT :
    jankoAmbientComplement D K hK jankoD ∈ sourceT D K hK R :=
  (show zpowers (jankoAmbientComplement D K hK jankoD) ≤ sourceT D K hK R from
    le_sup_right) (mem_zpowers _)

omit [Finite G] in
/-- The literal source complement element is an involution. -/
public theorem sourceD_order : orderOf (jankoAmbientComplement D K hK jankoD) = 2 := by
  rw [orderOf_injective _ (jankoAmbientComplement_injective D K hK)]
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

/-- Both source subgroups lie in the actual centralizer of the original involution. -/
public theorem sourceT_le_centralizer : sourceT D K hK R ≤ D.centralizer := by
  apply sup_le
  · apply sup_le
    · rw [sourceE, R.ambientBasis_range D K hK]
      exact map_subtype_le _
    · apply (closure_le _).mpr
      intro x hx
      rcases hx with rfl | hx
      · exact ((D.complementEquiv K hK).symm jankoA : D.centralizer).property
      · rcases hx with rfl
        exact ((D.complementEquiv K hK).symm jankoB : D.centralizer).property
  · apply zpowers_le.mpr
    exact ((D.complementEquiv K hK).symm jankoD : D.centralizer).property

private theorem fixed_first_vector (s : SymmetricFour) :
    D.binaryAction K hK s (R.basis (Multiplicative.ofAdd ![1, 0, 0, 0])) =
      R.basis (Multiplicative.ofAdd ![1, 0, 0, 0]) := by
  let v : BinaryFour := Multiplicative.ofAdd ![1, 0, 0, 0]
  have ha : jankoSourceA .three v = v := by decide +kernel
  have hb : jankoSourceB .three v = v := by decide +kernel
  have hc : jankoSourceC v = v := by decide +kernel
  have hd : jankoSourceD .three v = v := by decide +kernel
  change D.binaryAction K hK s (R.basis v) = R.basis v
  obtain ⟨i, j, k, l, rfl⟩ := janko_decomposition s
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp only [pow_zero, pow_succ,
      map_one, map_mul, MulAut.mul_apply, MulAut.one_apply, R.action_a, R.action_b,
      R.action_c_left, R.action_d, ha, hb, hc, hd]

/-- The source marking is the original involution, not just a new central line. -/
public theorem sourceZ_eq : sourceZ D K hK R = D.z := by
  let v : BinaryFour := Multiplicative.ofAdd ![1, 0, 0, 0]
  let w : D.kernel := D.kernelBinaryEquiv.symm (R.basis v)
  have hfixed (s : SymmetricFour) :
      jankoAmbientComplement D K hK s * sourceZ D K hK R =
        sourceZ D K hK R * jankoAmbientComplement D K hK s := by
    have h := R.ambient_conjugation_of_action D K hK s v v
      (fixed_first_vector D K hK R s⁻¹)
    have hh := congrArg (fun x => jankoAmbientComplement D K hK s * x) h
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, sourceZ, v] using hh.symm
  have hwcentral : (w : D.centralizer) ∈ center D.centralizer := by
    apply mem_center_iff.mpr
    intro x
    obtain ⟨⟨f, k⟩, hfk, _⟩ := hK.existsUnique x
    dsimp at hfk
    rw [← hfk]
    have hf : (f : D.centralizer) * w = w * f := by
      let := D.kernel_elementary
      exact congrArg D.kernel.subtype (mul_comm f w)
    have hk : (k : D.centralizer) * w = w * k := by
      apply Subtype.ext
      have hh := hfixed (D.complementEquiv K hK k)
      simp only [jankoAmbientComplement, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at hh
      exact hh
    calc
      (f : D.centralizer) * k * w = f * ((k : D.centralizer) * w) := mul_assoc _ _ _
      _ = f * (w * k) := by rw [hk]
      _ = w * ((f : D.centralizer) * k) := by rw [← mul_assoc, hf, mul_assoc]
  have hwne : (w : D.centralizer) ≠ 1 := by
    intro he
    have h : sourceZ D K hK R = 1 := congrArg D.centralizer.subtype he
    have hv : v = 1 := (R.ambientBasis_injective D K hK)
      (h.trans (map_one _).symm)
    have hvne : v ≠ 1 := by decide +kernel
    exact hvne hv
  let wz : center D.centralizer := ⟨w, hwcentral⟩
  let zz : center D.centralizer := ⟨D.centralInvolution, D.centralInvolution_mem_center⟩
  obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : center D.centralizer)).mp D.center_card
  have hwz : wz ≠ 1 := fun he => hwne (congrArg Subtype.val he)
  have hzz : zz ≠ 1 := fun he => D.z_ne_one
    (congrArg (fun y : center D.centralizer => ((y : D.centralizer) : G)) he)
  exact congrArg (fun y : center D.centralizer => ((y : D.centralizer) : G))
    ((ha wz hwz).trans (ha zz hzz).symm)

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseThreeExclusion
