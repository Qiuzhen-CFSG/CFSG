module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Certificates

/-!
# The unique singular six-space and its scalar intersection

The six displacement identities force every singular subspace invariant
under the first vector stabilizer into an explicit six-dimensional space.
An order comparison therefore identifies every such subspace of order 64.
A checked scalar action intersects that space with its conjugate in exactly
the binary two-space spanned by the first vector and its cubic scalar image.

This is the native linear geometry used in Aschbacher–Segev,
*The uniqueness of groups of type J₄*, Invent. Math. 105 (1991), proof of
(4.3)(2), p.597, DOI 10.1007/BF01232280. The source transport in
`ThreeSpace.Intersection` uses the original core, its center quotient and
its full cubic stabilizer action.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open M22TripleCover.Ambient
open Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Native
open VectorOrbits

def constraint : M22TripleCover.BinarySpace →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  LinearMap.pi (fun j => linear (masks j))

def space : Submodule (ZMod 2) M22TripleCover.BinarySpace := constraint.ker

theorem mem_space (v : M22TripleCover.BinarySpace) : v ∈ space ↔
    v 1 + v 3 + v 11 = 0 ∧
    v 0 + v 1 + v 3 + v 4 + v 9 = 0 ∧
    v 0 + v 1 + v 4 + v 8 = 0 ∧
    v 1 + v 7 = 0 ∧ v 1 + v 3 + v 6 = 0 ∧ v 1 + v 5 = 0 := by
  change (fun j => linear (masks j) v) = 0 ↔ _
  rw [funext_iff]
  simp [linear,masks,vector,Fin.forall_fin_succ,Fin.sum_univ_succ,add_assoc,Nat.testBit]

def param (v : Fin 6 → ZMod 2) : M22TripleCover.BinarySpace :=
  ![v 0, v 1, v 2, v 3, v 4, v 1, v 1+v 3, v 1,
    v 0+v 1+v 4, v 0+v 1+v 3+v 4, v 5, v 1+v 3]

def project (v : M22TripleCover.BinarySpace) : Fin 6 → ZMod 2 :=
  ![v 0,v 1,v 2,v 3,v 4,v 10]

theorem param_mem (v : Fin 6 → ZMod 2) : param v ∈ space := by
  rw [mem_space]
  dsimp [param]
  constructor
  · ring_nf; rfl
  constructor
  · ring_nf; rfl
  constructor
  · ring_nf; rfl
  constructor
  · ring_nf; rfl
  constructor <;> ring_nf <;> rfl

theorem project_param (v : Fin 6 → ZMod 2) : project (param v) = v := by
  ext i
  fin_cases i <;> rfl

theorem param_project (v : M22TripleCover.BinarySpace) (hv : v ∈ space) :
    param (project v) = v := by
  obtain ⟨h₀,h₁,h₂,h₃,h₄,h₅⟩ := (mem_space v).mp hv
  ext i
  fin_cases i <;> dsimp [param,project]
  · linear_combination (norm := ring_nf) h₅ ; simp [show (2 : ZMod 2) = 0 from rfl]
  · linear_combination (norm := ring_nf) h₄ ; simp [show (2 : ZMod 2) = 0 from rfl]
  · linear_combination (norm := ring_nf) h₃ ; simp [show (2 : ZMod 2) = 0 from rfl]
  · linear_combination (norm := ring_nf) h₂ ; simp [show (2 : ZMod 2) = 0 from rfl]
  · linear_combination (norm := ring_nf) h₁ ; simp [show (2 : ZMod 2) = 0 from rfl]
  · linear_combination (norm := ring_nf) h₀ ; simp [show (2 : ZMod 2) = 0 from rfl]

noncomputable def spaceEquiv : (Fin 6 → ZMod 2) ≃ space where
  toFun v := ⟨param v,param_mem v⟩
  invFun v := project v
  left_inv := project_param
  right_inv v := Subtype.ext (param_project v v.property)

theorem space_card : Nat.card space = 64 := by
  rw [← Nat.card_congr spaceEquiv]
  simp

theorem word_stable (U : Submodule (ZMod 2) M22TripleCover.BinarySpace)
    (hs : ∀ g ∈ nativeVectorStabilizer (decode 4), ∀ v ∈ U, binaryAction g v ∈ U)
    (l : List (Fin 5)) (v : M22TripleCover.BinarySpace) (hv : v ∈ U) :
    binaryAction (word l) v ∈ U := hs _ (word_mem l) v hv

theorem singular_stable_le (U : Submodule (ZMod 2) M22TripleCover.BinarySpace)
    (hq : ∀ v ∈ U, M22TripleCover.Unitary.quadraticForm v = 0)
    (hs : ∀ g ∈ nativeVectorStabilizer (decode 4), ∀ v ∈ U, binaryAction g v ∈ U) :
    U ≤ space := by
  intro v hv
  change (fun j => linear (masks j) v) = 0
  ext j
  have he := congrArg (fun q : QuadraticForm (ZMod 2) M22TripleCover.BinarySpace => q v)
    (linear_identity j)
  have hz : sumDisplacement j v = 0 := by
    change QuadraticMap.evalAddMonoidHom v ((identityWords j).map displacement).sum = 0
    rw [map_list_sum]
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ha
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp hd
    change quadratic (v + binaryAction (word l) v) = 0
    rw [quadratic_eq_native]
    exact hq _ (U.add_mem hv (word_stable U hs l v hv))
  rw [hz,QuadraticMap.linMulLin_apply] at he
  exact (mul_self_eq_zero.mp he.symm)

theorem singular_stable_eq (U : Submodule (ZMod 2) M22TripleCover.BinarySpace)
    (hc : Nat.card U = 64)
    (hq : ∀ v ∈ U, M22TripleCover.Unitary.quadraticForm v = 0)
    (hs : ∀ g ∈ nativeVectorStabilizer (decode 4), ∀ v ∈ U, binaryAction g v ∈ U) :
    U = space := by
  apply Submodule.toAddSubgroup_injective
  exact AddSubgroup.eq_of_le_of_card_ge (singular_stable_le U hq hs)
    (by change Nat.card space ≤ Nat.card U; rw [space_card,hc])

def scalarColumns : Fin 12 → Nat :=
  ![723,3514,1467,1867,883,3911,3663,2261,1571,2130,3935,2772]

theorem scalar_action : binaryAction scalarElement = columnMap scalarColumns := by
  apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
  intro i
  simp only [Pi.basisFun_apply]
  revert i
  decide +kernel

def paramMap : (Fin 6 → ZMod 2) →ₗ[ZMod 2] M22TripleCover.BinarySpace where
  toFun := param
  map_add' v w := by ext i; fin_cases i <;> simp [param] <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp [param,mul_add]

def scalarConstraints : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun u := ![u 1+u 5, u 0+u 1+u 4+u 5, u 0+u 1, u 4+u 5,
    u 0+u 3+u 4+u 5, u 1+u 3+u 4+u 5]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp [mul_add]

theorem scalar_constraints :
    constraint.comp ((binaryAction scalarElement).comp paramMap) = scalarConstraints := by
  rw [scalar_action]
  apply (Pi.basisFun (ZMod 2) (Fin 6)).ext
  intro i
  simp only [Pi.basisFun_apply]
  revert i
  decide +kernel

def lineMap : (Fin 2 → ZMod 2) →ₗ[ZMod 2] M22TripleCover.BinarySpace where
  toFun u := u 0 • vector 4 + u 1 • vector 1467
  map_add' v w := by simp [add_smul]; abel
  map_smul' c v := by simp [smul_add,smul_smul]

def line : Submodule (ZMod 2) M22TripleCover.BinarySpace := lineMap.range

theorem lineMap_coordinates (u : Fin 2 → ZMod 2) :
    lineMap u 2 = u 0 ∧ lineMap u 1 = u 1 := by
  simp [lineMap,vector,Nat.testBit]

theorem lineMap_injective : Function.Injective lineMap := by
  intro u v he
  ext i
  fin_cases i
  · exact (lineMap_coordinates u).1.symm.trans
      ((congrFun he 2).trans (lineMap_coordinates v).1)
  · exact (lineMap_coordinates u).2.symm.trans
      ((congrFun he 1).trans (lineMap_coordinates v).2)

theorem line_card : Nat.card line = 4 := by
  change Nat.card lineMap.range = 4
  rw [← Nat.card_congr (LinearEquiv.ofInjective lineMap lineMap_injective).toEquiv]
  simp

theorem line_le_space : line ≤ space := by
  rintro v ⟨u,rfl⟩
  change u 0 • vector 4 + u 1 • vector 1467 ∈ space
  apply Submodule.add_mem
  · exact space.smul_mem _ ((mem_space _).mpr (by decide +kernel))
  · exact space.smul_mem _ ((mem_space _).mpr (by decide +kernel))

theorem param_line (u : Fin 6 → ZMod 2) (hu : scalarConstraints u = 0) :
    param u = lineMap ![u 2,u 1] := by
  have h (i : Fin 6) := congrFun hu i
  have h₀ : u 1+u 5=0 := h 0
  have h₁ : u 0+u 1+u 4+u 5=0 := h 1
  have h₂ : u 0+u 1=0 := h 2
  have h₃ : u 4+u 5=0 := h 3
  have h₄ : u 0+u 3+u 4+u 5=0 := h 4
  have h₅ : u 1+u 3+u 4+u 5=0 := h 5
  have e₀ : u 0=u 1 := by linear_combination (norm := ring_nf) h₂ ; simp [show (2 : ZMod 2) = 0 from rfl]
  have e₃ : u 3=u 1 := by linear_combination (norm := ring_nf) h₅-h₃ ; simp [show (2 : ZMod 2) = 0 from rfl]
  have e₄ : u 4=u 1 := by linear_combination h₃-h₀
  have e₅ : u 5=u 1 := by linear_combination (norm := ring_nf) h₀ ; simp [show (2 : ZMod 2) = 0 from rfl]
  ext i
  fin_cases i <;> simp [param,lineMap,vector,Nat.testBit,e₀,e₃,e₄,e₅]

theorem scalar_intersection_le : space ⊓ space.comap (binaryAction scalarElement) ≤ line := by
  intro v hv
  have he := LinearMap.congr_fun scalar_constraints (project v)
  change constraint (binaryAction scalarElement (param (project v))) = scalarConstraints (project v) at he
  rw [param_project v hv.1] at he
  have hs : scalarConstraints (project v) = 0 := he.symm.trans hv.2
  rw [← param_project v hv.1,param_line _ hs]
  exact ⟨_,rfl⟩

theorem scalar_line (v : M22TripleCover.BinarySpace) (hv : v ∈ line) :
    binaryAction scalarElement v ∈ line := by
  obtain ⟨u,rfl⟩ := hv
  refine ⟨![u 1,u 0+u 1],?_⟩
  have h₄ : binaryAction scalarElement (vector 4) = vector 1467 := by
    rw [scalar_action,← vector_packedAction]
    decide +kernel
  have h₁₄ : binaryAction scalarElement (vector 1467) = vector 4 + vector 1467 := by
    rw [scalar_action,← vector_packedAction,← vector_xor]
    decide +kernel
  change _ = binaryAction scalarElement (u 0 • vector 4 + u 1 • vector 1467)
  rw [map_add,map_smul,map_smul,h₄,h₁₄]
  simp only [lineMap,LinearMap.coe_mk,AddHom.coe_mk,Matrix.cons_val_zero,Matrix.cons_val_one]
  module

theorem scalar_intersection : space ⊓ space.comap (binaryAction scalarElement) = line := by
  apply le_antisymm scalar_intersection_le
  intro v hv
  change v ∈ space ∧ binaryAction scalarElement v ∈ space
  constructor
  · exact line_le_space hv
  · exact line_le_space (scalar_line v hv)

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Native
