module

public import Theory.SpecificGroups.MathieuAmalgamCompletion.Relators
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourEndpointInclusions
public import Theory.SpecificGroups.PSL3.SmallCompletion.Weyl

/-!
# Concrete simultaneous linear-side matrix marking

The two point-local matrices and the coordinate three-cycle realize the first
thirteen exact finite-amalgam words. Calculations use the existing computable
field F2[w]/(w²+w+1), then its actual field isomorphism transports into the
original canonical PSL3(4) carrier. Shared torus and reflection words are kept.
This does not identify an arbitrary source cubic with the chosen three-cycle.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3Four.MathieuAmalgamMarking
open Subgroup.CosetWordCertificate
abbrev NativeF := Representation.SL2FourNatural.F
abbrev NativeSL := SpecialLinearGroup (Fin 3) NativeF

def w : NativeF := ⟨0,1⟩

def nativePair : Fin 2 → NativeSL
  | 0 => ⟨!![1,w^2,1;0,w^2,w^2;0,0,w],by decide +kernel⟩
  | 1 => ⟨!![1,1,w;0,w^2,w;0,w,w^2],by decide +kernel⟩

def nativeCycle : NativeSL := ⟨!![0,1,0;0,0,1;1,0,0],by decide +kernel⟩
def nativeTorus : NativeSL := ⟨!![w,0,0;0,1,0;0,0,w^2],by decide +kernel⟩
def nativeReflection : NativeSL := ⟨!![1,0,0;0,0,1;0,1,0],by decide +kernel⟩

def nativeGenerator : Fin 4 → NativeSL := ![nativePair 0,nativePair 1,nativeCycle,1]

theorem nativePair_mem (i : Fin 2) :
    nativePair i ∈ Matrix.PSL3.LinearThree.pointLocalSL NativeF := by
  rw [Matrix.PSL3.LinearThree.mem_pointLocalSL_iff]
  fin_cases i <;> decide +kernel

private theorem native_relators : ∀ i : Fin 13,
    ∃ a : NativeF, a^3=1 ∧ scalar (Fin 3) a =
      (eval nativeGenerator (Theory.SpecificGroups.MathieuAmalgamCompletion.relator
        ⟨i.val,by omega⟩)).val := by
  decide +kernel

noncomputable def fieldMap : NativeSL →* SL :=
  SpecialLinearGroup.map Representation.SL2FourNatural.fieldEquiv.toRingHom

noncomputable def project : NativeSL →* PSL := (Matrix.PSL3.projection F).comp fieldMap

noncomputable def pair (i : Fin 2) : PSL := project (nativePair i)
noncomputable def cycle : PSL := project nativeCycle
noncomputable def torus : PSL := project nativeTorus
noncomputable def reflection : PSL := project nativeReflection
noncomputable def generator : Fin 4 → PSL := fun i => project (nativeGenerator i)

private theorem map_eval {G H α : Type*} [Group G] [Group H] (f : G →* H)
    (g : α → G) (v : Word α) : f (eval g v) = eval (fun i => f (g i)) v := by
  induction v with
  | nil => simp
  | cons a v ih =>
    rw [eval_cons,eval_cons,map_mul,ih]
    cases a with
    | mk a b => cases b <;> simp

private theorem project_scalar (g : NativeSL) (a : NativeF) (ha : a^3=1)
    (hg : scalar (Fin 3) a = g.val) : project g = 1 := by
  apply (QuotientGroup.eq_one_iff (fieldMap g)).mpr
  apply SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨Representation.SL2FourNatural.fieldEquiv a,?_,?_⟩
  · simp only [Fintype.card_fin,←map_pow,ha,map_one]
  · change scalar (Fin 3) _ = g.val.map Representation.SL2FourNatural.fieldEquiv.toRingHom
    rw [←hg]
    ext i j
    by_cases he : i=j <;> simp [Matrix.scalar,Matrix.diagonal,he]

/-- The exact first thirteen recorded words hold for this concrete canonical triple. -/
theorem first_relators (i : Fin 13) :
    eval generator (Theory.SpecificGroups.MathieuAmalgamCompletion.relator
      ⟨i.val,by omega⟩) = 1 := by
  change eval (fun k => project (nativeGenerator k)) _ = 1
  rw [←map_eval project nativeGenerator]
  obtain ⟨a,ha,hg⟩ := native_relators i
  exact project_scalar _ a ha hg

/-- The torus is retained as a literal word in the same two point generators. -/
def torusWord : Word (Fin 2) :=
  [3,1,3,0,3,3,3,1,3,1,1,3,3,3,1,3,1,2,0].map
    (fun a => (⟨(a/2)%2,Nat.mod_lt _ (by decide)⟩,a%2==0))

/-- The point reflection is retained as a literal word in the same pair. -/
def reflectionWord : Word (Fin 2) :=
  [0,3,3,0,3,0,3,1,3,1,1,3,1].map
    (fun a => (⟨(a/2)%2,Nat.mod_lt _ (by decide)⟩,a%2==0))

theorem torus_word : eval pair torusWord = torus := by
  have hh : ∃ a : NativeF, a^3=1 ∧ scalar (Fin 3) a =
      (eval nativePair torusWord * nativeTorus⁻¹).val := by decide +kernel
  obtain ⟨a,ha,hg⟩ := hh
  have he := project_scalar _ a ha hg
  rw [map_mul,map_inv,map_eval] at he
  exact mul_inv_eq_one.mp he

theorem reflection_word : eval pair reflectionWord = reflection := by
  have he : eval nativePair reflectionWord = nativeReflection := by decide +kernel
  exact (map_eval project nativePair reflectionWord).symm.trans (congrArg project he)

/-- The actual canonical matrix markings retain the Weyl reflections. -/
theorem cycle_eq_reflections : cycle =
    Matrix.PSL3.SmallCompletion.reflection F false * Matrix.PSL3.SmallCompletion.reflection F true := by
  rw [Matrix.PSL3.SmallCompletion.reflection,Matrix.PSL3.SmallCompletion.reflection,←map_mul]
  apply congrArg (Matrix.PSL3.projection F)
  apply Subtype.ext
  change nativeCycle.val.map Representation.SL2FourNatural.fieldEquiv.toRingHom =
    (Matrix.PSL3.SmallCompletion.reflectionSL F false).val *
      (Matrix.PSL3.SmallCompletion.reflectionSL F true).val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nativeCycle,Matrix.PSL3.SmallCompletion.reflectionSL,Matrix.mul_apply,Fin.sum_univ_three]

end Matrix.PSL3Four.MathieuAmalgamMarking
