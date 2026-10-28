module

public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.G2Three.Hexagon
public import Theory.AtlasPort.LinearGroups.G2.TernaryTorus

/-!
# Canonical Weyl and torus elements in a faithful completion

Compatibility transports the same whole Borel into both endpoints.
The native Weyl reflections remain involutions outside this middle, and
the two diagonal torus involutions satisfy their actual conjugation rules.
Their common fixed-point predicate is therefore invariant under both
canonical reflections, with no global braid relation yet assumed.

Source: Aschbacher–Smith F.4.4 and F.4.26, printed pp.274 and 288.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.Explicit Atlas.SplitOctonion
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
variable {G : Type*} [Group G] (c : Completion G)

def nativeS : parabolic₁ (F := ZMod 3) :=
  ⟨weylS,mem_sup_right (subset_closure (by simp))⟩
def nativeR : parabolic₂ (F := ZMod 3) := ⟨weylR,weylR_mem_parabolic⟩
def S : G := c.left nativeS
def R : G := c.right nativeR

def nativeTorus (l m : (ZMod 3)ˣ) : GreenBook.LieModels.G2.overlap (F := ZMod 3) :=
  ⟨torus l m,GreenBook.LieModels.G2.overlap_eq_borel.ge (mem_sup_right ⟨(l,m),rfl⟩)⟩
def torus (l m : (ZMod 3)ˣ) : G := c.middle (nativeTorus l m)

theorem left_torus (l m : (ZMod 3)ˣ) : c.left
    ⟨Atlas.G2.torus l m,borel_le_parabolic₁ (mem_sup_right ⟨(l,m),rfl⟩)⟩=c.torus l m := rfl
theorem right_torus (l m : (ZMod 3)ˣ) : c.right
    ⟨Atlas.G2.torus l m,borel_le_parabolic₂ (mem_sup_right ⟨(l,m),rfl⟩)⟩=c.torus l m :=
  (DFunLike.congr_fun c.compatible (nativeTorus l m)).symm

theorem left_mem_middle_iff (l : parabolic₁ (F := ZMod 3)) :
    c.left l∈c.middle.range ↔ l.val∈borel := by
  constructor
  · rintro ⟨b,hb⟩
    have he := c.left_injective hb
    exact GreenBook.LieModels.G2.overlap_eq_borel.le (congrArg Subtype.val he ▸ b.property)
  · intro hl
    exact ⟨⟨l.val,GreenBook.LieModels.G2.overlap_eq_borel.ge hl⟩,rfl⟩

theorem S_sq : c.S^2=1 := by
  rw [S,←map_pow]
  have hs : nativeS^2=1 := Subtype.ext weylS_sq
  rw [hs,map_one]
theorem R_sq : c.R^2=1 := by
  rw [R,←map_pow]
  have hr : nativeR^2=1 := Subtype.ext weylR_sq
  rw [hr,map_one]
theorem S_out : c.S∉c.middle.range := by
  rw [S,c.left_mem_middle_iff]
  exact fun h => NativeSeven.first_not_mem false (borel_le_parabolic₂ h)
theorem R_out : c.R∉c.middle.range := by
  rw [R,c.right_mem_middle_iff]
  exact fun h => NativeSeven.first_not_mem true (borel_le_parabolic₁ h)

theorem native_SR_six : ((nativeS.val : Model (ZMod 3))*nativeR.val)^6=1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [nativeS,nativeR,pow_succ,weylS,weylR,weylSEquiv,weylREquiv,
    weylSLinear,weylRLinear,weylSApply,weylRApply]
end CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion

namespace CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (c : Completion G)
local notation "A" => c.torus (-1) 1
local notation "B" => c.torus 1 (-1)
local notation "α" => GreenBook.LieModels.G2.amalgam (F := ZMod 3)

theorem S_A : c.S*A*c.S=B := by
  have he : nativeS * (α).left (nativeTorus (-1) 1) * nativeS = (α).left (nativeTorus 1 (-1)) :=
    Subtype.ext TernaryTorus.weylS_a
  have hh := congrArg c.left he
  simpa only [map_mul,S,torus,Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion.middle,MonoidHom.comp_apply] using hh
theorem S_B : c.S*B*c.S=A := by
  have he : nativeS * (α).left (nativeTorus 1 (-1)) * nativeS = (α).left (nativeTorus (-1) 1) :=
    Subtype.ext TernaryTorus.weylS_b
  have hh := congrArg c.left he
  simpa only [map_mul,S,torus,Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion.middle,MonoidHom.comp_apply] using hh
theorem R_A : c.R*A*c.R=A*B := by
  have he : nativeR * (α).right (nativeTorus (-1) 1) * nativeR =
      (α).right (nativeTorus (-1) 1) * (α).right (nativeTorus 1 (-1)) :=
    Subtype.ext TernaryTorus.weylR_a
  have hh := congrArg c.right he
  simpa only [R,map_mul,show c.right ((α).right (nativeTorus (-1) 1))=A from c.right_torus (-1) 1,
    show c.right ((α).right (nativeTorus 1 (-1)))=B from c.right_torus 1 (-1)] using hh
theorem R_B : c.R*B*c.R=B := by
  have he : nativeR * (α).right (nativeTorus 1 (-1)) * nativeR = (α).right (nativeTorus 1 (-1)) :=
    Subtype.ext TernaryTorus.weylR_b
  have hh := congrArg c.right he
  simpa only [R,map_mul,show c.right ((α).right (nativeTorus 1 (-1)))=B from c.right_torus 1 (-1)] using hh

def TorusFixed (v : c.Vertex) : Prop := A • v=v ∧ B • v=v

theorem torus_fixed_base (i : Bool) : c.TorusFixed (RankTwo.base c.family i) := by
  have hh (l m : (ZMod 3)ˣ) : c.torus l m • RankTwo.base c.family i=RankTwo.base c.family i := by
    change c.torus l m∈stabilizer c.family (RankTwo.base c.family i)
    simp only [stabilizer,RankTwo.base,stabilizer_base]
    cases i
    · exact c.middle_le_left ⟨nativeTorus l m,rfl⟩
    · exact c.middle_le_right ⟨nativeTorus l m,rfl⟩
  exact ⟨hh (-1) 1,hh 1 (-1)⟩

private theorem fixed_under_conjugate {V : Type*} [MulAction G V]
    (u a b : G) (hu : u^2=1) (h : u*a*u=b) {v : V} (hb : b • v=v) :
    a • (u • v)=u • v := by
  have huu : u*u=1 := by simpa only [pow_two] using hu
  have he : a*u=u*b := by simp only [←h,←mul_assoc,huu,one_mul]
  rw [←SemigroupAction.mul_smul,he,SemigroupAction.mul_smul,hb]

theorem torus_fixed_S (v : c.Vertex) : c.TorusFixed (c.S • v) ↔ c.TorusFixed v := by
  have hf (w : c.Vertex) (hw : c.TorusFixed w) : c.TorusFixed (c.S • w) :=
    ⟨fixed_under_conjugate c.S A B c.S_sq c.S_A hw.2,
      fixed_under_conjugate c.S B A c.S_sq c.S_B hw.1⟩
  refine ⟨fun h => ?_,hf v⟩
  simpa only [←SemigroupAction.mul_smul,←pow_two,c.S_sq,one_smul] using hf (c.S • v) h

theorem torus_fixed_R (v : c.Vertex) : c.TorusFixed (c.R • v) ↔ c.TorusFixed v := by
  have hf (w : c.Vertex) (hw : c.TorusFixed w) : c.TorusFixed (c.R • w) :=
    ⟨fixed_under_conjugate c.R A (A*B) c.R_sq c.R_A (by rw [SemigroupAction.mul_smul,hw.2,hw.1]),
      fixed_under_conjugate c.R B B c.R_sq c.R_B hw.2⟩
  refine ⟨fun h => ?_,hf v⟩
  simpa only [←SemigroupAction.mul_smul,←pow_two,c.R_sq,one_smul] using hf (c.R • v) h
end CFSG.Quasithin.ChapterF.SourceCompletion.G2Three.Completion
