module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Seed
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules.HeckeAction.FixedSpace

/-!
# Simplicity of the literal binary adjoint quotient

Conjugation by an upper transvection cannot change an endomorphism by a
nonzero scalar: a diagonal coordinate outside its two indices is unchanged.
Thus an upper-fixed quotient class has an upper-fixed representative, and
commutation with the positive roots forces that representative to be a
scalar plus a multiple of E₀₃.

The adjacent coordinate exchanges carry E₀₃ to every off-diagonal matrix
unit. Further transvection conjugates give the diagonal differences, which
together span the trace kernel. Every nonzero invariant subspace of the
quotient has a nonzero upper-fixed vector by the two-group fixed-vector
theorem, and therefore contains the generating highest-root line.

This proves simplicity on `Endpoint.Model`'s actual carrier and quotient
map, discharging the `hsimple` premise of endpoint recognition. It assumes
no module recognition or catalogue.

Source: Aschbacher–Smith K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section

open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint

private abbrev e (i : Fin 4) : Natural := Pi.single i 1

private theorem transvection_apply (i j : Fin 4) (h : i ≠ j) (x : Natural) :
    natural (Matrix.SpecialLinearGroup.transvection h (1 : ZMod 2)) x =
      x + x j • e i := by
  ext k
  simp [natural, specialLinearNatural_apply, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_mulVec, Matrix.single_mulVec_eq, e, Pi.single_apply]

private theorem upper_lift_fixed (f : TraceZero) (hf : UpperFixed adjoint (mkAdjoint f))
    (i j : Fin 4) (hij : i < j) :
    traceAction (Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) 1) f = f := by
  let t := Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) (1 : ZMod 2)
  have hz : mkAdjoint (traceAction t f - f) = 0 := by
    rw [mkAdjoint.map_sub, ← adjoint_mk, hf i j hij, sub_self]
  obtain ⟨c, hc⟩ := (mkAdjoint_eq_zero_iff _).mp hz
  have hex : ∀ i j : Fin 4, ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := hex i j
  have he := congrArg (fun z : TraceZero => z.val (e k) k) hc
  have hinv : t⁻¹ = t := by
    simp [t, Matrix.SpecialLinearGroup.transvection_inv, show (-1 : ZMod 2) = 1 by decide]
  have htk : natural t (e k) = e k := by
    rw [transvection_apply]
    simp [e, hkj]
  have hleft (x : Natural) : natural t x k = x k := by
    rw [transvection_apply]
    simp [e, hki]
  have hc0 : c = 0 := by
    simpa [scalarVector, traceAction_apply, LinearMap.comp_apply, hinv, htk, hleft,
      e, Pi.single_apply] using he
  rw [hc0, zero_smul] at hc
  exact sub_eq_zero.mp hc.symm

private theorem upper_commute_entries (f : TraceZero) (hf : UpperFixed adjoint (mkAdjoint f))
    (i j : Fin 4) (hij : i < j) (k l : Fin 4) :
    (if k = i then f.val (e l) j else 0) =
      (if l = j then f.val (e i) k else 0) := by
  let t := Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) (1 : ZMod 2)
  have h := upper_lift_fixed f hf i j hij
  have he := congrArg (fun z : TraceZero => z.val (natural t (e l)) k) h
  have ht : natural t⁻¹ (natural t (e l)) = e l := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  change natural t (f.val (natural t⁻¹ (natural t (e l)))) k =
    f.val (natural t (e l)) k at he
  rw [ht, transvection_apply, transvection_apply, map_add, map_smul] at he
  by_cases hki : k = i <;> by_cases hlj : l = j
  · simpa [e, Pi.single_apply, hki, hlj, eq_comm] using he
  · simpa [e, Pi.single_apply, hki, hlj, eq_comm] using he
  · simpa [e, Pi.single_apply, hki, hlj, eq_comm] using he
  · simp [hki, hlj]

private theorem upper_fixed_representative (f : TraceZero)
    (hf : UpperFixed adjoint (mkAdjoint f)) :
    f = f.val (e 0) 0 • scalarVector + f.val (e 3) 0 • highestRoot := by
  apply Subtype.ext
  apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
  intro l
  ext k
  simp only [Pi.basisFun_apply]
  change f.val (e l) k = _
  by_cases hk : k = 0
  · subst k
    by_cases hl : l = 3
    · subst l
      simp [scalarVector, highestRoot, e]
    · have hlt : l < 3 := by omega
      have he := upper_commute_entries f hf l 3 hlt 0 3
      have hd := upper_commute_entries f hf 0 3 (by decide) 0 3
      simp only [ite_true] at hd
      simpa [scalarVector, highestRoot, e, Pi.single_apply, hl, hd, eq_comm] using he.symm
  · have hlt : (0 : Fin 4) < k := by omega
    have he := upper_commute_entries f hf 0 k hlt 0 l
    simpa [scalarVector, highestRoot, e, Pi.single_apply, ite_apply, hk, eq_comm] using he

/-- The upper-fixed space is the line through the marked root class. -/
theorem adjoint_upperFixed_line (x : Adjoint) (hx : UpperFixed adjoint x) :
    ∃ c : ZMod 2, x = c • mkAdjoint highestRoot := by
  obtain ⟨f, rfl⟩ := mkAdjoint_surjective x
  refine ⟨f.val (e 3) 0, ?_⟩
  have hs : mkAdjoint scalarVector = 0 :=
    (mkAdjoint_eq_zero_iff _).mpr ⟨1, one_smul _ _⟩
  conv_lhs => rw [upper_fixed_representative f hx]
  rw [map_add, map_smul, map_smul, hs, smul_zero, zero_add]

private def matrixUnit (i j : Fin 4) : Module.End (ZMod 2) Natural :=
  (LinearMap.proj j).smulRight (e i)

private def root (i j : Fin 4) : TraceZero :=
  ⟨if i = j then 0 else matrixUnit i j, by
    split_ifs with h
    · simp
    · simp [matrixUnit, LinearMap.trace_smulRight, e, Ne.symm h]⟩

private def cartan (i : Fin 3) : TraceZero :=
  ⟨matrixUnit i.castSucc i.castSucc - matrixUnit 3 3, by
    simp [matrixUnit, LinearMap.trace_smulRight, e]⟩

private theorem root_swap (i : Fin 3) (j k : Fin 4) :
    traceAction (simpleSwap i) (root j k) =
      root (Equiv.swap i.castSucc i.succ j) (Equiv.swap i.castSucc i.succ k) := by
  apply Subtype.ext
  rw [traceAction_apply, inv_eq_of_mul_eq_one_right (HeckeAction.swap_sq i)]
  apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
  intro l
  ext m
  simp only [LinearMap.comp_apply, Pi.basisFun_apply]
  revert i j k l m
  decide

private theorem cartan_conjugate (i : Fin 3) :
    cartan i = traceAction
      (Matrix.SpecialLinearGroup.transvection (i := i.castSucc) (j := 3) (Fin.castSucc_ne_last i) 1)
        (root 3 i.castSucc) + root 3 i.castSucc + root i.castSucc 3 := by
  apply Subtype.ext
  change (cartan i).val =
    (traceAction (Matrix.SpecialLinearGroup.transvection (Fin.castSucc_ne_last i) 1)
      (root 3 i.castSucc)).val + (root 3 i.castSucc).val + (root i.castSucc 3).val
  rw [traceAction_apply, Matrix.SpecialLinearGroup.transvection_inv]
  apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
  intro l
  ext m
  simp only [Pi.basisFun_apply]
  revert i l m
  decide

private theorem trace_entries (f : TraceZero) :
    f.val (e 0) 0 + f.val (e 1) 1 + f.val (e 2) 2 + f.val (e 3) 3 = 0 := by
  have ht := f.property
  change LinearMap.trace (ZMod 2) Natural f.val = 0 at ht
  rw [LinearMap.trace_eq_matrix_trace (ZMod 2) (Pi.basisFun (ZMod 2) (Fin 4))] at ht
  simpa [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Fin.sum_univ_succ,
    Pi.basisFun_apply, e, add_assoc] using ht

private theorem root_cartan_decomposition (f : TraceZero) :
    f = (∑ i : Fin 4, ∑ j : Fin 4, f.val (e j) i • root i j) +
      ∑ i : Fin 3, f.val (e i.castSucc) i.castSucc • cartan i := by
  have ht := trace_entries f
  apply Subtype.ext
  apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
  intro l
  ext k
  fin_cases l <;> fin_cases k <;>
    simp [Fin.sum_univ_succ, root, cartan, matrixUnit, e]
  linear_combination (norm := ring_nf) ht
  simp [show (2 : ZMod 2) = 0 by decide]

private theorem root_mem_of_highestRoot (W : Subrepresentation traceAction)
    (h : highestRoot ∈ W) : ∀ i j, root i j ∈ W := by
  have hs (a : Fin 3) (i j : Fin 4) (hij : root i j ∈ W) :
      root (Equiv.swap a.castSucc a.succ i) (Equiv.swap a.castSucc a.succ j) ∈ W := by
    rw [← root_swap]
    exact W.apply_mem_toSubmodule _ hij
  have h03 : root 0 3 ∈ W := h
  have h13 : root 1 3 ∈ W := hs 0 0 3 h03
  have h02 : root 0 2 ∈ W := hs 2 0 3 h03
  have h23 : root 2 3 ∈ W := hs 1 1 3 h13
  have h12 : root 1 2 ∈ W := hs 0 0 2 h02
  have h01 : root 0 1 ∈ W := hs 1 0 2 h02
  have h32 : root 3 2 ∈ W := hs 2 2 3 h23
  have h21 : root 2 1 ∈ W := hs 1 1 2 h12
  have h10 : root 1 0 ∈ W := hs 0 0 1 h01
  have h31 : root 3 1 ∈ W := hs 2 2 1 h21
  have h20 : root 2 0 ∈ W := hs 1 1 0 h10
  have h30 : root 3 0 ∈ W := hs 2 2 0 h20
  intro i j
  fin_cases i <;> fin_cases j <;> first | assumption | exact W.toSubmodule.zero_mem

/-- The marked highest-root vector generates the whole trace kernel. -/
theorem traceAction_eq_top_of_highestRoot (W : Subrepresentation traceAction)
    (h : highestRoot ∈ W) : W = ⊤ := by
  have hr := root_mem_of_highestRoot W h
  have hd (i : Fin 3) : cartan i ∈ W := by
    rw [cartan_conjugate]
    exact W.toSubmodule.add_mem
      (W.toSubmodule.add_mem (W.apply_mem_toSubmodule _ (hr _ _)) (hr _ _)) (hr _ _)
  apply top_unique
  intro f _
  rw [root_cartan_decomposition f]
  exact W.toSubmodule.add_mem
    (W.toSubmodule.sum_mem fun i _ => W.toSubmodule.sum_mem fun j _ =>
      W.toSubmodule.smul_mem _ (hr i j))
    (W.toSubmodule.sum_mem fun i _ => W.toSubmodule.smul_mem _ (hd i))

/-- The literal highest-root class generates the adjoint quotient. -/
theorem adjoint_eq_top_of_highestRoot (W : Subrepresentation adjoint)
    (h : mkAdjoint highestRoot ∈ W) : W = ⊤ := by
  let U : Subrepresentation traceAction :=
    { toSubmodule := W.toSubmodule.comap mkAdjoint
      apply_mem_toSubmodule := by
        intro g f hf
        change mkAdjoint (traceAction g f) ∈ W
        rw [← adjoint_mk]
        exact W.apply_mem_toSubmodule g hf }
  have hU : U = ⊤ := traceAction_eq_top_of_highestRoot U h
  apply top_unique
  intro x _
  obtain ⟨f, rfl⟩ := mkAdjoint_surjective x
  have hf : f ∈ U := by rw [hU]; trivial
  exact hf

/-- Conjugation on the literal binary adjoint quotient is irreducible. -/
theorem adjoint_isIrreducible : Representation.IsIrreducible adjoint := by
  let : Nontrivial Adjoint := ⟨⟨mkAdjoint highestRoot, 0, mkAdjoint_highestRoot_ne_zero⟩⟩
  let : Nontrivial (Subrepresentation adjoint) := ⟨⟨⊥, ⊤, by
    intro h
    have hm : mkAdjoint highestRoot ∈ (⊤ : Subrepresentation adjoint) := trivial
    rw [← h] at hm
    exact mkAdjoint_highestRoot_ne_zero hm⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  have hW' : W.toSubmodule ≠ ⊥ := by
    intro h
    exact hW (Subrepresentation.toSubmodule_injective h)
  let : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hW'
  obtain ⟨w, hw, hfix⟩ := HeckeAction.exists_nonzero_upperFixed W.toRepresentation
  have hw0 : (w : Adjoint) ≠ 0 := by
    intro h
    exact hw (Subtype.ext h)
  have hfix' : UpperFixed adjoint (w : Adjoint) := by
    intro i j hij
    exact congrArg Subtype.val (hfix i j hij)
  obtain ⟨c, hc⟩ := adjoint_upperFixed_line w hfix'
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hc
    exact hw0 hc
  apply adjoint_eq_top_of_highestRoot W
  have hm := W.toSubmodule.smul_mem c⁻¹ w.property
  rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at hm
  exact hm

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint
