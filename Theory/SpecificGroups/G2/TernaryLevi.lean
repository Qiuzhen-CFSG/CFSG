module
public import Theory.SpecificGroups.G2.TernaryCoreRepresentation
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The root matrices use the licensed split-octonion model from
Atlas/LinearGroups/G2, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS-CITATION.cff. Changes: explicit ternary GL₂ actors,
faithful embeddings, and whole-parabolic semidirect decompositions.
-/

/-!
# The two full ternary G₂ Levi actors

Two explicit two-by-two matrices generate GL₂(3). A private word table
certifies generation on its 48 elements; polynomial generator identities
prove multiplicativity of the two eight-dimensional octonion actions.
Their words in the literal root and Weyl elements give injective embeddings.
The scalar involution, full split torus, and positive simple root are retained.

In each parabolic the actor intersects the five-root radical trivially,
and together they generate the whole endpoint. This constructs both full
semidirect equivalences and quotient actions, with no splitting premise.
The original-group application is AtlasEndpointActions in the I.4.5 proof.
Identifying the original quotient actions and agreeing on the whole middle
remain separate obligations. Source: Aschbacher–Smith I.4.5, p.417, and
F.4.26, p.288; the concrete conventions are those of the licensed ATLAS port.
-/

public section
open Subgroup Matrix Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
namespace Atlas.G2.TernaryLevi
abbrev GL23 := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)
private abbrev M2 := Matrix (Fin 2) (Fin 2) (ZMod 3)
private abbrev M8 := Matrix (Fin 8) (Fin 8) (ZMod 3)

/-- The fixed upper cubic and Weyl generators of the actor. -/
@[expose] def generator (b : Bool) : GL23 := if b then
  GeneralLinearGroup.mkOfDetNeZero !![0,-1;-1,0] (by decide) else
  GeneralLinearGroup.mkOfDetNeZero !![1,-1;0,1] (by decide)
private def codeWord : Nat → List Bool
  | 12 => [false,true,false,true,false,true,false]
  | 13 => [true,false,true,false,true,false]
  | 14 => [false,false,true,false,true,false,true,false]
  | 15 => [false,true,false,false,true,false]
  | 16 => [true,false,false,true,false]
  | 17 => [false,false,true,false,false,true,false]
  | 21 => [false,false,true,false,true,false,false]
  | 22 => [true,false,true,false,false]
  | 23 => [false,true,false,true,false,false]
  | 24 => [true]
  | 25 => [false,true]
  | 26 => [false,false,true]
  | 28 => []
  | 29 => [true,false,true,false,false,true,false]
  | 31 => [false,false]
  | 32 => [false,true,false,true,false,false,true]
  | 34 => [false]
  | 35 => [true,false,true,false,false,true]
  | 37 => [true,false,false,true]
  | 38 => [false,false,true,false,true,false,true]
  | 39 => [false,true,false,true,false,true]
  | 41 => [false,false,true,false,false,true]
  | 42 => [false,true,false,false,true]
  | 43 => [true,false,true,false,true]
  | 46 => [true,false,true]
  | 47 => [false,false,true,false]
  | 48 => [false,false,true,false,true]
  | 49 => [false,true,false]
  | 51 => [true,false]
  | 53 => [false,true,false,true]
  | 55 => [false,true,false,false,true,false,true]
  | 56 => [false,true,false,true,false,true,false,true]
  | 58 => [true,false,false,true,false,true,false]
  | 59 => [false,false,true,false,true,false,true,false,true]
  | 61 => [true,false,false,true,false,true]
  | 62 => [true,false,true,false,true,false,true]
  | 64 => [true,false,true,false,true,false,false]
  | 65 => [false,false,true,false,false,true,false,false]
  | 66 => [false,true,false,true,false,true,false,false]
  | 67 => [true,false,false,true,false,false]
  | 69 => [false,true,false,false,true,false,false]
  | 71 => [true,false,false,true,false,false,true]
  | 73 => [false,true,false,false]
  | 74 => [false,true,false,true,false]
  | 75 => [false,false,true,false,true,false]
  | 77 => [false,false,true,false,false]
  | 78 => [true,false,false]
  | 79 => [true,false,true,false]
  | _ => []
private def word (a : M2) : List Bool :=
  codeWord ((a 0 0).val+3*(a 0 1).val+9*(a 1 0).val+27*(a 1 1).val)

private theorem word_matrix : ∀ a : M2, a.det≠0 →
    ((word a).map (fun b => (generator b).val)).prod=a := by decide +kernel

private theorem word_gl (a : GL23) : ((word a.val).map generator).prod=a := by
  apply Units.ext
  change (Units.coeHom M2) ((List.map generator (word a.val)).prod)=a.val
  rw [map_list_prod,List.map_map]
  exact word_matrix a.val (Units.ne_zero (GeneralLinearGroup.det a))

/-- Two explicit matrices suffice to check equivariance for the whole actor. -/
theorem equivariant_of_generators {A B : Type*} [Group A] [Group B]
    (ρ : GL23 →* MulAut A) (σ : GL23 →* MulAut B) (f : A → B)
    (h : ∀ b v,f (ρ (generator b) v)=σ (generator b) (f v)) :
    ∀ a v,f (ρ a v)=σ a (f v) := by
  have hw (w : List Bool) : ∀ v,
      f (ρ ((w.map generator).prod) v)=σ ((w.map generator).prod) (f v) := by
    induction w with
    | nil => intro v; simp
    | cons b w ih =>
      intro v
      simp only [List.map_cons,List.prod_cons,map_mul,MulAut.mul_apply]
      rw [h,ih]
  intro a v
  rw [←word_gl a]
  exact hw _ v

private theorem multiplicative_of_generators {A B : Type*} [Monoid A] [Monoid B]
    (s : Bool → A) (hs : ∀ a,∃ w : List Bool,(w.map s).prod=a)
    (f : A → B) (hf : f 1=1) (hstep : ∀ a b,f (a*s b)=f a*f (s b)) :
    ∀ a b,f (a*b)=f a*f b := by
  have hwords (w : List Bool) : ∀ a,f (a*(w.map s).prod)=f a*(w.map (fun b=>f (s b))).prod := by
    induction w with
    | nil => intro a; simp
    | cons b w ih =>
      intro a
      simp only [List.map_cons,List.prod_cons,←mul_assoc]
      rw [ih,hstep,mul_assoc]
  intro a b
  obtain ⟨w,rfl⟩ := hs b
  have h := hwords w 1
  simp only [one_mul,hf] at h
  rw [hwords,h]

/-- Coordinate matrices of the two actual GL₂(3) actions on octonions. -/
@[expose] def actionMatrix (longSide : Bool)
    (m : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  let a:=m 0 0; let b:=m 0 1; let c:=m 1 0; let d:=m 1 1
  let δ:=a*d-b*c
  if longSide then !![
    δ,0,0,0,0,0,0,0;
    0,a,b,0,0,0,0,0;
    0,c,d,0,0,0,0,0;
    0,0,0,1,0,0,0,0;
    0,0,0,0,1,0,0,0;
    0,0,0,0,0,δ*a,-δ*b,0;
    0,0,0,0,0,-δ*c,δ*d,0;
    0,0,0,0,0,0,0,δ] else !![
    a,b,0,0,0,0,0,0;
    c,d,0,0,0,0,0,0;
    0,0,δ*a*a,-δ*a*b,δ*a*b,δ*b*b,0,0;
    0,0,-δ*a*c,δ*a*d,-δ*b*c,-δ*b*d,0,0;
    0,0,δ*a*c,-δ*b*c,δ*a*d,δ*b*d,0,0;
    0,0,δ*c*c,-δ*c*d,δ*c*d,δ*d*d,0,0;
    0,0,0,0,0,0,δ*a,-δ*b;
    0,0,0,0,0,0,-δ*c,δ*d]

private theorem matrix_step_false_false (a : M2) :
    actionMatrix false (a*(generator false).val)=actionMatrix false a*actionMatrix false (generator false).val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [actionMatrix,generator,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring_nf <;> simp

private theorem matrix_step_false_true (a : M2) :
    actionMatrix false (a*(generator true).val)=actionMatrix false a*actionMatrix false (generator true).val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [actionMatrix,generator,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring_nf

private theorem matrix_step_true_false (a : M2) :
    actionMatrix true (a*(generator false).val)=actionMatrix true a*actionMatrix true (generator false).val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [actionMatrix,generator,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring_nf <;> simp

private theorem matrix_step_true_true (a : M2) :
    actionMatrix true (a*(generator true).val)=actionMatrix true a*actionMatrix true (generator true).val := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [actionMatrix,generator,Matrix.mul_apply,Fin.sum_univ_succ]

private theorem matrix_step (side : Bool) (a : M2) (b : Bool) :
    actionMatrix side (a*(generator b).val)=actionMatrix side a*actionMatrix side (generator b).val := by
  cases side <;> cases b
  · exact matrix_step_false_false a
  · exact matrix_step_false_true a
  · exact matrix_step_true_false a
  · exact matrix_step_true_true a

private def matrixAction (side : Bool) : GL23 →* M8 where
  toFun a := actionMatrix side a.val
  map_one' := by cases side <;> decide
  map_mul' := multiplicative_of_generators generator (fun a=>⟨word a.val,word_gl a⟩)
    (fun a=>actionMatrix side a.val) (by cases side <;> decide)
    (fun a b=>matrix_step side a.val b)

/-- The actual positive root and Weyl element, in each of the two endpoints. -/
@[expose] def rootGenerator (longSide b : Bool) : Model (ZMod 3) :=
  if longSide then (if b then weylR else rootE 1) else (if b then weylS else rootF 1)

private def matrixHom : Model (ZMod 3) →* M8 where
  toFun a := LinearMap.toMatrix' a.val.toLinearMap
  map_one' := LinearMap.toMatrix'_one
  map_mul' a b := LinearMap.toMatrix'_mul a.val.toLinearMap b.val.toLinearMap

private theorem matrixHom_injective : Function.Injective matrixHom := by
  intro a b h
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact LinearMap.toMatrix'.injective h

private theorem matrixHom_generator (side b : Bool) :
    matrixHom (rootGenerator side b)=actionMatrix side (generator b).val := by
  cases side <;> cases b <;> decide +kernel

private def liftWord (side : Bool) (a : GL23) : Model (ZMod 3) :=
  ((word a.val).map (rootGenerator side)).prod

private theorem matrixHom_liftWord (side : Bool) (a : GL23) :
    matrixHom (liftWord side a)=matrixAction side a := by
  rw [liftWord,map_list_prod,List.map_map]
  simp only [Function.comp_def,matrixHom_generator]
  change ((word a.val).map (fun b=>matrixAction side (generator b))).prod=_
  have h := (matrixAction side).map_list_prod ((word a.val).map generator)
  rw [word_gl,List.map_map] at h
  exact h.symm

/-- The actual GL₂(3) embedding into the short or long Atlas endpoint. -/
def embedding (side : Bool) : GL23 →* Model (ZMod 3) where
  toFun := liftWord side
  map_one' := matrixHom_injective (by rw [matrixHom_liftWord,map_one,map_one])
  map_mul' a b := matrixHom_injective (by rw [matrixHom_liftWord,map_mul,map_mul,
    matrixHom_liftWord,matrixHom_liftWord])

theorem embedding_matrix (side : Bool) (a : GL23) :
    LinearMap.toMatrix' (embedding side a).val.toLinearMap=actionMatrix side a.val :=
  matrixHom_liftWord side a

@[simp] theorem embedding_generator (side b : Bool) :
    embedding side (generator b)=rootGenerator side b := by
  apply matrixHom_injective
  rw [show matrixHom (embedding side (generator b))=matrixAction side (generator b) from
    matrixHom_liftWord side (generator b),matrixHom_generator]
  rfl

theorem embedding_injective (side : Bool) : Function.Injective (embedding side) := by
  intro a b h
  have hm := congrArg matrixHom h
  change matrixHom (liftWord side a)=matrixHom (liftWord side b) at hm
  rw [matrixHom_liftWord,matrixHom_liftWord] at hm
  apply Units.ext
  ext i j
  cases side
  · have hh := congrArg (fun m : M8 => m (i.castLE (by decide)) (j.castLE (by decide))) hm
    fin_cases i <;> fin_cases j <;> exact hh
  · have hh := congrArg (fun m : M8 => m ⟨i.val+1,by omega⟩ ⟨j.val+1,by omega⟩) hm
    fin_cases i <;> fin_cases j <;> exact hh

/-- Both embeddings use the scalar involution of the same GL₂(3). -/
theorem embedding_central (side : Bool) :
    embedding side (-1)=(if side then torus 1 (-1) else torus (-1) (-1)) := by
  apply matrixHom_injective
  rw [show matrixHom (embedding side (-1))=matrixAction side (-1) from matrixHom_liftWord side (-1)]
  cases side <;> decide +kernel

/-- The whole actual actor commutes with its distinguished torus involution. -/
theorem embedding_commutes (side : Bool) (a : GL23) :
    Commute (embedding side a) (if side then torus 1 (-1) else torus (-1) (-1)) := by
  rw [←embedding_central]
  apply Commute.map
  change a*(-1)=(-1)*a
  simp

/-- Every split torus element is in each actor image, with explicit diagonal coordinates. -/
theorem torus_mem_range (side : Bool) (l m : (ZMod 3)ˣ) :
    torus l m ∈ (embedding side).range := by
  let a : GL23 := GeneralLinearGroup.mkOfDetNeZero
    (if side then !![(m:ZMod 3),0;0,(l:ZMod 3)*(m:ZMod 3)⁻¹] else
      !![(l:ZMod 3),0;0,(m:ZMod 3)]) (by
        cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true,Matrix.det_fin_two]
        · change (l:ZMod 3)*(m:ZMod 3)-0*0≠0
          simpa only [mul_zero,sub_zero] using mul_ne_zero l.ne_zero m.ne_zero
        · change (m:ZMod 3)*((l:ZMod 3)*(m:ZMod 3)⁻¹)-0*0≠0
          simpa only [mul_zero,sub_zero] using mul_ne_zero m.ne_zero (mul_ne_zero l.ne_zero (inv_ne_zero m.ne_zero)))
  refine ⟨a,?_⟩
  apply matrixHom_injective
  rw [show matrixHom (embedding side a)=matrixAction side a from matrixHom_liftWord side a]
  have h : ∀ (side : Bool) (l m : (ZMod 3)ˣ),
      actionMatrix side (if side then !![(m:ZMod 3),0;0,(l:ZMod 3)*(m:ZMod 3)⁻¹] else
        !![(l:ZMod 3),0;0,(m:ZMod 3)])=matrixHom (torus l m) := by decide +kernel
  exact h side l m

/-- Uniform names for the two actual Atlas parabolics and their radicals. -/
@[expose] def endpoint (side : Bool) : Subgroup (Model (ZMod 3)) :=
  if side then LieParabolicSetup.parabolic₂ else LieParabolicSetup.parabolic₁
@[expose] def radical (side : Bool) : Subgroup (Model (ZMod 3)) :=
  if side then LieParabolicSetup.radical₂ else LieParabolicSetup.radical₁

private theorem rootGenerator_mem (side b : Bool) : rootGenerator side b ∈ endpoint side := by
  cases side <;> cases b
  · exact mem_sup_left (mem_sup_left (subset_closure (by simp [rootGenerator])))
  · exact mem_sup_right (subset_closure (by simp [rootGenerator]))
  · exact mem_sup_left (mem_sup_left (subset_closure (by simp [rootGenerator])))
  · exact mem_sup_right (subset_closure (by simp [rootGenerator]))

/-- The embeddings land in the whole specified endpoints. -/
theorem embedding_mem (side : Bool) (a : GL23) : embedding side a ∈ endpoint side := by
  change ((word a.val).map (rootGenerator side)).prod∈endpoint side
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hg
  exact rootGenerator_mem side b

theorem radical_le_endpoint (side : Bool) : radical side≤endpoint side := by
  cases side
  · exact LieParabolicSetup.radical₁_le_local₁.trans
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
  · exact LieParabolicSetup.radical₂_le_local₂.trans
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)

theorem endpoint_normalizes (side : Bool) : endpoint side≤normalizer (radical side:Set (Model (ZMod 3))) := by
  cases side
  · exact TernaryCore.short_parabolic_normalizes
  · exact TernaryCore.long_parabolic_normalizes

private theorem simple_root_mem_range (side : Bool) (a : ZMod 3) :
    (if side then rootE a else rootF a) ∈ (embedding side).range := by
  have h : ∀ (side : Bool) (a : ZMod 3),
      matrixHom (if side then rootE a else rootF a)=matrixHom (rootGenerator side false ^ a.val) := by
    decide +kernel
  have he := matrixHom_injective (h side a)
  rw [he,←embedding_generator]
  exact (embedding side).range.pow_mem ⟨generator false,rfl⟩ a.val

/-- The full endpoint is generated by its actual five-root core and the constructed actor. -/
theorem radical_sup_range (side : Bool) : radical side ⊔ (embedding side).range=endpoint side := by
  apply le_antisymm (sup_le (radical_le_endpoint side) (by rintro _ ⟨a,rfl⟩; exact embedding_mem side a))
  have hu : unipotent (K:=ZMod 3) ≤ radical side ⊔ (embedding side).range := by
    apply (closure_le _).mpr
    intro g hg
    rcases hg with (((((hg|hg)|hg)|hg)|hg)|hg)
    all_goals obtain ⟨a,rfl⟩ := hg
    · apply mem_sup_left
      cases side <;> exact ⟨![a,0,0,0,0,0],rfl,by simp [unipotentProduct]⟩
    · apply mem_sup_left
      cases side <;> exact ⟨![0,a,0,0,0,0],rfl,by simp [unipotentProduct]⟩
    · apply mem_sup_left
      cases side <;> exact ⟨![0,0,a,0,0,0],rfl,by simp [unipotentProduct]⟩
    · apply mem_sup_left
      cases side <;> exact ⟨![0,0,0,a,0,0],rfl,by simp [unipotentProduct]⟩
    · cases side
      · exact mem_sup_left ⟨![0,0,0,0,a,0],rfl,by simp [unipotentProduct]⟩
      · exact mem_sup_right (simple_root_mem_range true a)
    · cases side
      · exact mem_sup_right (simple_root_mem_range false a)
      · exact mem_sup_left ⟨![0,0,0,0,0,a],rfl,by simp [unipotentProduct]⟩
  have ht : splitTorus (K:=ZMod 3) ≤ radical side ⊔ (embedding side).range := by
    rintro _ ⟨⟨l,m⟩,rfl⟩
    exact mem_sup_right (torus_mem_range side l m)
  have hw : rootGenerator side true∈radical side ⊔ (embedding side).range :=
    mem_sup_right ⟨generator true,embedding_generator side true⟩
  cases side <;> exact sup_le (sup_le hu ht) ((closure_le _).mpr (by simpa [rootGenerator] using hw))

private def block (side : Bool) (a : M8) : M2 :=
  if side then fun i j=>a ⟨i.val+1,by omega⟩ ⟨j.val+1,by omega⟩ else
    fun i j=>a (i.castLE (by decide)) (j.castLE (by decide))

private theorem block_actionMatrix (side : Bool) (a : M2) : block side (actionMatrix side a)=a := by
  ext i j
  cases side <;> fin_cases i <;> fin_cases j <;> rfl

private theorem block_false_apply (a : M8) (i j : Fin 2) :
    block false a i j=a (i.castLE (by decide)) (j.castLE (by decide)) := rfl
private theorem block_true_apply (a : M8) (i j : Fin 2) :
    block true a i j=a ⟨i.val+1,by omega⟩ ⟨j.val+1,by omega⟩ := rfl
private theorem matrixHom_apply (g : Model (ZMod 3)) (i j : Fin 8) :
    matrixHom g i j=g.val (Pi.single j 1) i := rfl

private theorem block_short (k : ZMod 3) (v : TernaryCore.V) :
    block false (matrixHom (TernaryCore.short k v))=1 := by
  ext i j
  rw [block_false_apply,matrixHom_apply]
  fin_cases i <;> fin_cases j <;>
    simp [TernaryCore.short,unipotentProduct,
      rootA,rootB,rootC,rootD,rootE,rootF,rootAEquiv,rootBEquiv,rootCEquiv,rootDEquiv,rootEEquiv,rootFEquiv,
      rootALinear,rootBLinear,rootCLinear,rootDLinear,rootELinear,rootFLinear,
      rootAApply,rootBApply,rootCApply,rootDApply,rootEApply,rootFApply]

private theorem block_long (k : ZMod 3) (v : TernaryCore.V) :
    block true (matrixHom (TernaryCore.long k v))=1 := by
  ext i j
  rw [block_true_apply,matrixHom_apply]
  fin_cases i <;> fin_cases j <;>
    simp [TernaryCore.long,unipotentProduct,
      rootA,rootB,rootC,rootD,rootE,rootF,rootAEquiv,rootBEquiv,rootCEquiv,rootDEquiv,rootEEquiv,rootFEquiv,
      rootALinear,rootBLinear,rootCLinear,rootDLinear,rootELinear,rootFLinear,
      rootAApply,rootBApply,rootCApply,rootDApply,rootEApply,rootFApply]

/-- Faithfulness retains the literal two-dimensional coordinate blocks. -/
theorem embedding_mem_radical_iff (side : Bool) (a : GL23) :
    embedding side a∈radical side ↔ a=1 := by
  constructor
  · intro ha
    apply Units.ext
    cases side
    · obtain ⟨k,v,h⟩ := TernaryCore.short_surjective ⟨embedding false a,ha⟩
      have he := congrArg (fun x : LieParabolicSetup.radical₁ (F:=ZMod 3) => matrixHom x.val) h
      change matrixHom (TernaryCore.short k v)=matrixHom (embedding false a) at he
      rw [show matrixHom (embedding false a)=actionMatrix false a.val from matrixHom_liftWord false a] at he
      have hh := congrArg (block false) he
      rw [block_short,block_actionMatrix] at hh
      exact hh.symm
    · obtain ⟨k,v,h⟩ := TernaryCore.long_surjective ⟨embedding true a,ha⟩
      have he := congrArg (fun x : LieParabolicSetup.radical₂ (F:=ZMod 3) => matrixHom x.val) h
      change matrixHom (TernaryCore.long k v)=matrixHom (embedding true a) at he
      rw [show matrixHom (embedding true a)=actionMatrix true a.val from matrixHom_liftWord true a] at he
      have hh := congrArg (block true) he
      rw [block_long,block_actionMatrix] at hh
      exact hh.symm
  · rintro rfl
    rw [map_one]
    exact one_mem _

theorem radical_disjoint_range (side : Bool) : Disjoint (radical side) (embedding side).range := by
  apply disjoint_iff.mpr
  apply bot_unique
  rintro g ⟨hg,⟨a,rfl⟩⟩
  rw [(embedding_mem_radical_iff side a).mp hg,map_one]
  exact one_mem _

/-- Each model actor, with its literal endpoint codomain. -/
@[expose] def endpointEmbedding (side : Bool) : GL23 →* endpoint side :=
  (embedding side).codRestrict _ (embedding_mem side)

/-- The full GL₂(3) action on the actual radical. -/
@[expose] def coreAction (side : Bool) : GL23 →* MulAut (radical side) :=
  (radical side).normalizerMonoidHom.comp
    ((inclusion (endpoint_normalizes side)).comp (endpointEmbedding side))

/-- The multiplication map using the actual model core and actor inclusions. -/
@[expose] def splitHom (side : Bool) : (radical side) ⋊[coreAction side] GL23 →* endpoint side :=
  SemidirectProduct.lift (inclusion (radical_le_endpoint side)) (endpointEmbedding side)
    (by intro a; ext v; rfl)

private theorem splitHom_injective (side : Bool) : Function.Injective (splitHom side) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro v hv
  have h : (v.left:Model (ZMod 3))*embedding side v.right=1 := congrArg Subtype.val hv
  have he : embedding side v.right=(v.left:Model (ZMod 3))⁻¹ := eq_inv_of_mul_eq_one_right h
  have hr : v.right=1 := (embedding_mem_radical_iff side v.right).mp
    (by rw [he]; exact (radical side).inv_mem v.left.property)
  have hl : v.left=1 := by
    apply Subtype.ext
    change (v.left:Model (ZMod 3))=1
    simpa only [hr,map_one,mul_one] using h
  exact SemidirectProduct.ext hl hr

private theorem splitHom_surjective (side : Bool) : Function.Surjective (splitHom side) := by
  intro v
  have hv : (v:Model (ZMod 3))∈radical side ⊔ (embedding side).range :=
    (radical_sup_range side).symm ▸ v.property
  have hn : (embedding side).range≤normalizer (radical side:Set (Model (ZMod 3))) := by
    rintro _ ⟨a,rfl⟩
    exact endpoint_normalizes side (embedding_mem side a)
  change (v:Model (ZMod 3))∈(↑(radical side ⊔ (embedding side).range):Set (Model (ZMod 3))) at hv
  rw [coe_mul_of_right_le_normalizer_left _ _ hn] at hv
  obtain ⟨d,hd,a,⟨b,rfl⟩,h⟩ := hv
  exact ⟨⟨⟨d,hd⟩,b⟩,Subtype.ext h⟩

/-- Both whole Atlas endpoints, with their complete GL₂(3) actions. -/
noncomputable def splitEquiv (side : Bool) : (radical side) ⋊[coreAction side] GL23 ≃* endpoint side :=
  MulEquiv.ofBijective (splitHom side) ⟨splitHom_injective side,splitHom_surjective side⟩

@[simp] theorem splitEquiv_inl (side : Bool) (v : radical side) :
    (splitEquiv side (SemidirectProduct.inl v):Model (ZMod 3))=v := by
  change (splitHom side (SemidirectProduct.inl v):Model (ZMod 3))=v
  rw [splitHom,SemidirectProduct.lift_inl]
  rfl

@[simp] theorem splitEquiv_inr (side : Bool) (a : GL23) :
    (splitEquiv side (SemidirectProduct.inr a):Model (ZMod 3))=embedding side a := by
  change (splitHom side (SemidirectProduct.inr a):Model (ZMod 3))=_
  rw [splitHom,SemidirectProduct.lift_inr]
  rfl

/-- Full model quotient action with the same explicit GL₂(3) actor. -/
@[expose] def shortQuotientAction : GL23 →* MulAut TernaryCore.V :=
  TernaryCore.shortQuotientAction.comp (endpointEmbedding false)
@[expose] def longQuotientAction : GL23 →* MulAut TernaryCore.V :=
  TernaryCore.longQuotientAction.comp (endpointEmbedding true)

theorem shortQuotientAction_quotient (a : GL23) (v : radical false) :
    shortQuotientAction a (TernaryCore.shortQuotient v)=
      TernaryCore.shortQuotient (coreAction false a v) :=
  TernaryCore.shortQuotientAction_quotient (endpointEmbedding false a) v

theorem longQuotientAction_quotient (a : GL23) (v : radical true) :
    longQuotientAction a (TernaryCore.longQuotient v)=
      TernaryCore.longQuotient (coreAction true a v) :=
  TernaryCore.longQuotientAction_quotient (endpointEmbedding true a) v

/-- The chosen cubic generator has the previously computed full short-root action. -/
theorem shortQuotientAction_root (v : TernaryCore.V) :
    shortQuotientAction (generator false) v=TernaryCore.shortRoot v := by
  have he : endpointEmbedding false (generator false)=
      (⟨rootF 1,mem_sup_left (mem_sup_left (subset_closure (by simp)))⟩:
        LieParabolicSetup.parabolic₁ (F:=ZMod 3)) :=
    Subtype.ext (embedding_generator false false)
  change TernaryCore.shortQuotientAction (endpointEmbedding false (generator false)) v=_
  rw [he,TernaryCore.shortQuotientAction_root]

theorem shortQuotientAction_weyl (v : TernaryCore.V) :
    shortQuotientAction (generator true) v=TernaryCore.shortWeyl v := by
  have he : endpointEmbedding false (generator true)=
      (⟨weylS,mem_sup_right (subset_closure (by simp))⟩:
        LieParabolicSetup.parabolic₁ (F:=ZMod 3)) :=
    Subtype.ext (embedding_generator false true)
  change TernaryCore.shortQuotientAction (endpointEmbedding false (generator true)) v=_
  rw [he,TernaryCore.shortQuotientAction_weyl]

/-- The chosen cubic generator has the previously computed full long-root action. -/
theorem longQuotientAction_root (v : TernaryCore.V) :
    longQuotientAction (generator false) v=TernaryCore.longRoot v := by
  have he : endpointEmbedding true (generator false)=
      (⟨rootE 1,mem_sup_left (mem_sup_left (subset_closure (by simp)))⟩:
        LieParabolicSetup.parabolic₂ (F:=ZMod 3)) :=
    Subtype.ext (embedding_generator true false)
  change TernaryCore.longQuotientAction (endpointEmbedding true (generator false)) v=_
  rw [he,TernaryCore.longQuotientAction_root]

theorem longQuotientAction_weyl (v : TernaryCore.V) :
    longQuotientAction (generator true) v=TernaryCore.longWeyl v := by
  have he : endpointEmbedding true (generator true)=
      (⟨weylR,mem_sup_right (subset_closure (by simp))⟩:
        LieParabolicSetup.parabolic₂ (F:=ZMod 3)) :=
    Subtype.ext (embedding_generator true true)
  change TernaryCore.longQuotientAction (endpointEmbedding true (generator true)) v=_
  rw [he,TernaryCore.longQuotientAction_weyl]

end Atlas.G2.TernaryLevi
