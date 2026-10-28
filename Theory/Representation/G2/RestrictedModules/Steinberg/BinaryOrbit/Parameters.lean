module

public import Theory.Representation.G2.RestrictedModules.Steinberg.Construction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.PGroup

/-!
# The binary unipotent group in the concrete G₂ representation

The six zero/one parameters bijectively enumerate the actual unipotent subgroup
of G₂ over the prime field. Its polynomial multiplication law, mapped through
the prime-field embedding, gives a homomorphism to the actual G₂ model over any
characteristic-two field. Consequently the prescribed tensor orbit is an orbit
of a group of order 64, and all six binary root fixers fix this group.

Source: the unipotent parametrization in the attributed ATLAS G₂ port;
GLS3, 2.8.7 and Example 2.8.10(g), for the application to the Steinberg factor.
-/

public noncomputable section
open scoped BigOperators
namespace Atlas.G2.Restricted.Steinberg

/-- The actual unipotent subgroup over the prime field. -/
abbrev BinaryUnipotent := unipotentRange (K := ZMod 2)

private def bitEquiv : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun a := a == 1
  left_inv b := by cases b <;> decide
  right_inv a := by fin_cases a <;> rfl

private def parameterEquiv : (Fin 6 → ZMod 2) ≃ BinaryUnipotent where
  toFun t := ⟨unipotentProduct t, t, rfl⟩
  invFun g := unipotentParameters g.val
  left_inv := unipotentParameters_product
  right_inv g := by
    rcases g with ⟨g, t, rfl⟩
    apply Subtype.ext
    exact congrArg unipotentProduct (unipotentParameters_product t)

/-- Binary tuples enumerate the genuine prime-field unipotent group. -/
def binaryIndexEquiv : BinaryIndex ≃ BinaryUnipotent :=
  (Equiv.piCongrRight fun _ => bitEquiv).trans parameterEquiv

instance binaryUnipotentFintype : Fintype BinaryUnipotent := Fintype.ofEquiv BinaryIndex binaryIndexEquiv

theorem card_binaryUnipotent : Nat.card BinaryUnipotent = 64 := by
  rw [← Nat.card_congr binaryIndexEquiv]
  simp [BinaryIndex]

theorem binaryUnipotent_isTwoGroup : IsPGroup 2 BinaryUnipotent :=
  IsPGroup.of_card (n := 6) card_binaryUnipotent

private theorem parameters_map {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (t u : Fin 6 → K) :
    (fun i => φ (unipotentProductParameters t u i)) =
      unipotentProductParameters (fun i => φ (t i)) (fun i => φ (u i)) := by
  ext i
  fin_cases i <;> simp [unipotentProductParameters, map_ofNat]

/-- Left translation, explicitly transported through the six unipotent parameters. -/
def binaryTranslation (g : BinaryUnipotent) : Equiv.Perm BinaryIndex :=
  binaryIndexEquiv.trans ((Equiv.mulLeft g).trans binaryIndexEquiv.symm)

@[simp] theorem binaryIndexEquiv_translation (g : BinaryUnipotent) (t : BinaryIndex) :
    binaryIndexEquiv (binaryTranslation g t) = g * binaryIndexEquiv t := by
  simp [binaryTranslation]

/-- The six binary root elements, with their actual positions in the ordered product. -/
def binaryRoot (i : Fin 6) : BinaryUnipotent :=
  binaryIndexEquiv (fun j => decide (j = i))

variable (F : Type*) [Field F] [CharP F 2]

/-- The prime-field unipotent group acts by the actual root elements over F. -/
def binaryUnipotentHom : BinaryUnipotent →* Model F where
  toFun g := unipotentProduct (fun i => ZMod.castHom (dvd_refl 2) F (unipotentParameters g.val i))
  map_one' := by
    have h : unipotentParameters (1 : Model (ZMod 2)) = 0 := by
      rw [← unipotentProduct_zero, unipotentParameters_product]
    change unipotentProduct (fun i => ZMod.castHom (dvd_refl 2) F (unipotentParameters 1 i)) = 1
    simp only [h, Pi.zero_apply, map_zero]
    exact unipotentProduct_zero
  map_mul' g h := by
    rcases g with ⟨g, t, rfl⟩
    rcases h with ⟨h, u, rfl⟩
    simp only [Subgroup.coe_mul, unipotentProduct_mul, unipotentParameters_product]
    rw [parameters_map]

@[simp] theorem binaryUnipotentHom_index (t : BinaryIndex) :
    binaryUnipotentHom F (binaryIndexEquiv t) = unipotentProduct (binaryParameters F t) := by
  change unipotentProduct (fun i => ZMod.castHom (dvd_refl 2) F
    (unipotentParameters (unipotentProduct (binaryParameters (ZMod 2) t)) i)) = _
  rw [unipotentParameters_product]
  congr 1
  funext i
  simp [binaryParameters, apply_ite]

/-- Restriction to the 64-element unipotent group, valid over every characteristic-two field. -/
def binaryUnipotentAction : Representation F BinaryUnipotent (Ambient F) :=
  (ambientAction F).comp (binaryUnipotentHom F)

@[simp] theorem binaryUnipotentAction_index (t : BinaryIndex) (v : Ambient F) :
    binaryUnipotentAction F (binaryIndexEquiv t) v =
      ambientAction F (unipotentProduct (binaryParameters F t)) v := by
  change ambientAction F (binaryUnipotentHom F (binaryIndexEquiv t)) v = _
  rw [binaryUnipotentHom_index]

theorem binaryOrbitVector_eq (t : BinaryIndex) :
    binaryOrbitVector F t = binaryUnipotentAction F (binaryIndexEquiv t)
      (ambientAction F (longestWeyl F) (seed F)) := by
  rw [binaryUnipotentAction_index, binaryOrbitVector, map_mul, Module.End.mul_apply]

/-- Fixing the six positive root involutions implies fixation by the whole binary group. -/
theorem binaryUnipotentAction_fixed (v : Ambient F)
    (hA : ambientAction F (rootA 1) v = v)
    (hB : ambientAction F (rootB 1) v = v)
    (hC : ambientAction F (rootC 1) v = v)
    (hD : ambientAction F (rootD 1) v = v)
    (hE : ambientAction F (rootE 1) v = v)
    (hF : ambientAction F (rootF 1) v = v) :
    ∀ g, binaryUnipotentAction F g v = v := by
  intro g
  obtain ⟨t, rfl⟩ := binaryIndexEquiv.surjective g
  rw [binaryUnipotentAction_index]
  have h (r : F → Model F) (hr : r 0 = 1) (hf : ambientAction F (r 1) v = v)
      (b : Bool) : ambientAction F (r (if b then 1 else 0)) v = v := by
    cases b <;> simp [hr, hf]
  simp only [unipotentProduct, map_mul, Module.End.mul_apply, binaryParameters]
  rw [h rootF rootF_zero hF, h rootE rootE_zero hE, h rootD rootD_zero hD,
    h rootC rootC_zero hC, h rootB rootB_zero hB, h rootA rootA_zero hA]
/-- The basis candidates carry the regular left permutation action. -/
theorem binaryUnipotentAction_binaryOrbitVector (g : BinaryUnipotent) (t : BinaryIndex) :
    binaryUnipotentAction F g (binaryOrbitVector F t) =
      binaryOrbitVector F (binaryTranslation g t) := by
  simp only [binaryOrbitVector_eq, binaryIndexEquiv_translation,
    map_mul, Module.End.mul_apply]

@[simp] theorem binaryUnipotentHom_root (i : Fin 6) :
    binaryUnipotentHom F (binaryRoot i) =
      ![rootA (1 : F), rootB 1, rootC 1, rootD 1, rootE 1, rootF 1] i := by
  rw [binaryRoot, binaryUnipotentHom_index]
  fin_cases i <;> simp [binaryParameters, unipotentProduct]

/-- Each of the six actual binary roots permutes the orbit by left translation. -/
theorem binary_root_permutation (i : Fin 6) (t : BinaryIndex) :
    ambientAction F (![rootA (1 : F), rootB 1, rootC 1, rootD 1, rootE 1, rootF 1] i)
      (binaryOrbitVector F t) = binaryOrbitVector F (binaryTranslation (binaryRoot i) t) := by
  rw [← binaryUnipotentHom_root]
  exact binaryUnipotentAction_binaryOrbitVector F (binaryRoot i) t

/-- Stability under the binary unipotent group follows already from its permutation action. -/
theorem binaryUnipotentAction_mem_binarySpan (g : BinaryUnipotent)
    {v : Ambient F} (hv : v ∈ binarySpan F) :
    binaryUnipotentAction F g v ∈ binarySpan F := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, rfl⟩ := hv
    rw [binaryUnipotentAction_binaryOrbitVector]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => simp
  | add v w _ _ hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
  | smul a v _ hv => simpa only [map_smul] using Submodule.smul_mem _ a hv

end Atlas.G2.Restricted.Steinberg
