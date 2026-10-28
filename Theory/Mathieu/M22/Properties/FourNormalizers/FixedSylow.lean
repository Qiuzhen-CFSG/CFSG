module

public import Theory.Mathieu.M22.Properties.FourNormalizers.FixedSylow.Checks
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion

/-!
# Every Sylow-normal four-group fixes a hexad pointwise

The 128 certified words exhaust the pair–partition Sylow subgroup. A square-one
element outside the hexad kernel has four distinct conjugates in that Sylow.
A normal subgroup of order four cannot contain those and the identity. Thus
every elementary normal four-group lies in the pointwise kernel. Sylow
conjugacy gives the same conclusion, with a transported hexad, for any Sylow.

This proves exhaustive coverage for the M₂₂ normalizer calculation in
Aschbacher–Smith 15.3.43, printed p.1140, using the native degree-22 model.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22FourNormalizers
open Subgroup M22ValueBound.Concrete
open scoped Pointwise
namespace FixedSylow

noncomputable def wordElement : List (Fin 3) → M22
  | [] => 1
  | j :: w => generator j * wordElement w

theorem wordElement_mem (w : List (Fin 3)) : wordElement w ∈ M22EvenGeometry.sylow := by
  induction w with
  | nil => exact (M22EvenGeometry.sylow : Subgroup M22).one_mem
  | cons j w ih =>
    exact (M22EvenGeometry.sylow : Subgroup M22).mul_mem (generator_mem_standard j) ih

theorem wordElement_apply (w : List (Fin 3)) (x : Fin 22) :
    (wordElement w).val x = wordAction w x := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change generatorTable j ((wordElement w).val x) = _
    rw [ih]
    rfl

noncomputable def rowElement (i : Fin 128) : M22 := wordElement (rowWord i)

theorem rowElement_apply (i : Fin 128) (x : Fin 22) :
    (rowElement i).val x = rowTable i x :=
  (wordElement_apply _ _).trans (row_word_table i x)

theorem rowElement_inv_apply (i : Fin 128) (x : Fin 22) :
    ((rowElement i)⁻¹).val x = rowInvTable i x := by
  apply (rowElement i).val.injective
  change (rowElement i).val ((rowElement i).val.symm x) = _
  rw [Equiv.apply_symm_apply, rowElement_apply, row_table_inv]

noncomputable def rowSylow (i : Fin 128) : M22EvenGeometry.sylow :=
  ⟨rowElement i, wordElement_mem _⟩

theorem rowSylow_surjective : Function.Surjective rowSylow := by
  have hi : Function.Injective rowSylow := by
    intro i j h
    apply row_key_injective
    have he := congrArg (fun x : M22EvenGeometry.sylow => permutationKey x.val.val) h
    simpa only [permutationKey, rowSylow, rowElement_apply] using he
  exact (hi.bijective_of_nat_card_le (by
    change Nat.card (M22EvenGeometry.sylow : Subgroup M22) ≤ Nat.card (Fin 128)
    rw [M22EvenGeometry.sylow_card, Nat.card_fin])).2

/-- This uses normality only inside the specified Sylow subgroup. -/
theorem four_le_hexadKernel (V : Subgroup M22)
    (hVP : V ≤ (M22EvenGeometry.sylow : Subgroup M22))
    (hPV : (M22EvenGeometry.sylow : Subgroup M22) ≤ normalizer (V : Set M22))
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 4) :
    V ≤ m22HexadPointwiseKernel m22Hexad123 := by
  intro v hv
  obtain ⟨i, hi⟩ := rowSylow_surjective ⟨v, hVP hv⟩
  have hev : rowElement i = v := congrArg Subtype.val hi
  have hiv : rowElement i ∈ V := hev.symm ▸ hv
  rcases row_cases i with hfix | hsquare | horbit
  · apply (mem_m22HexadPointwiseKernel _ _).mpr
    intro a ha
    rw [← hev]
    change (rowElement i).val a = a
    exact (rowElement_apply i a).trans (hfix a ha)
  · let := hV
    have hs := congrArg (fun x : M22 => x.val (squarePoint i))
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (rowElement i) hiv)
    rw [pow_two] at hs
    change (rowElement i).val ((rowElement i).val (squarePoint i)) = squarePoint i at hs
    rw [rowElement_apply, rowElement_apply] at hs
    exact (hsquare hs).elim
  · let f : Fin 5 → V := Fin.cases 1 fun j =>
      ⟨rowElement (conjugatorIndex i j) * rowElement i *
          (rowElement (conjugatorIndex i j))⁻¹,
        (mem_normalizer_iff.mp (hPV (wordElement_mem _)) _).mp hiv⟩
    have hkey (j : Fin 5) : permutationKey (f j).val.val = fiveKey i j := by
      refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · change permutationKey (fun x =>
          (rowElement (conjugatorIndex i k)).val ((rowElement i).val
            (((rowElement (conjugatorIndex i k))⁻¹).val x))) = _
        simp only [permutationKey, rowElement_apply, rowElement_inv_apply,
          fiveKey, Fin.cases_succ]
    have hinj : Function.Injective f := by
      intro j k he
      apply horbit
      rw [← hkey, ← hkey, he]
    have hbound := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_fin, hc] at hbound
    omega

end FixedSylow

/-- Exhaustive coverage: every elementary four-group normal in an ambient
Sylow two-subgroup lies in the pointwise kernel of an actual Witt hexad. -/
theorem exists_hexad_kernel (P : Sylow 2 M22) (V : Subgroup M22)
    (hVP : V ≤ (P : Subgroup M22))
    (hPV : (P : Subgroup M22) ≤ normalizer (V : Set M22))
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 4) :
    ∃ B ∈ m22Blocks, V ≤ m22HexadPointwiseKernel B := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 P M22EvenGeometry.sylow
  let e := MulAut.conj g
  have hP : (P : Subgroup M22).map e.toMonoidHom =
      (M22EvenGeometry.sylow : Subgroup M22) := congrArg Sylow.toSubgroup hg
  have hVP' : V.map e.toMonoidHom ≤ (M22EvenGeometry.sylow : Subgroup M22) :=
    hP ▸ map_mono hVP
  have hPV' : (M22EvenGeometry.sylow : Subgroup M22) ≤
      normalizer (V.map e.toMonoidHom : Set M22) := by
    rw [← hP, ← map_equiv_normalizer_eq]
    exact map_mono hPV
  let := hV
  have hW := FixedSylow.four_le_hexadKernel _ hVP' hPV'
    (IsElementaryAbelian.map e.toMonoidHom)
    ((card_map_of_injective e.injective).trans hc)
  refine ⟨g⁻¹ • m22Hexad123, ?_, ?_⟩
  · exact m22_smul_block_mem g⁻¹ _ m22Hexad123_mem
  · rw [m22HexadPointwiseKernel_smul]
    intro v hv
    refine ⟨e v, hW (mem_map_of_mem _ hv), ?_⟩
    simp [e, MulAut.conj_apply, mul_assoc]

end Sporadic.Mathieu.M22FourNormalizers
