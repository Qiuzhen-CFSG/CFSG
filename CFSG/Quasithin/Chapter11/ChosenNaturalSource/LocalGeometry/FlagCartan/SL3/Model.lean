module
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The Sylow flag on a marked three-space

Upper unitriangular matrices have a unique invariant field subspace in each
positive dimension. Root displacements prove uniqueness, while fixed vectors
and second fixed vectors characterize the line and plane intrinsically.
One simultaneous Sylow conjugation transports the flag. These intrinsic
characterizations prove preservation by compatible additive outer actors,
without assuming field-linearity. The source application is in `SL3.Flag`.

Source: Aschbacher--Smith, opening of §11.1, printed pp.760--761.
-/

open Matrix Subgroup Representation
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
@[expose] public noncomputable section
set_option linter.unusedSimpArgs false
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.Model
variable {F : Type*} [Field F]

def point : Submodule F (Fin 3 → F) where
  carrier := {v | v 1 = 0 ∧ v 2 = 0}
  zero_mem' := by simp
  add_mem' := by rintro v w ⟨h1,h2⟩ ⟨k1,k2⟩; simp_all
  smul_mem' := by rintro a v ⟨h1,h2⟩; simp_all

def plane : Submodule F (Fin 3 → F) where
  carrier := {v | v 2 = 0}
  zero_mem' := rfl
  add_mem' := by intros; simp_all
  smul_mem' := by intros; simp_all

@[simp] theorem mem_point (v : Fin 3 → F) : v ∈ point ↔ v 1 = 0 ∧ v 2 = 0 := Iff.rfl
@[simp] theorem mem_plane (v : Fin 3 → F) : v ∈ plane ↔ v 2 = 0 := Iff.rfl

def pointEquiv : (point (F := F)) ≃ₗ[F] F where
  toFun v := v.val 0
  invFun a := ⟨![a,0,0], by simp⟩
  left_inv v := by ext i; fin_cases i <;> simp [v.property.1,v.property.2]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def planeEquiv : (plane (F := F)) ≃ₗ[F] (Fin 2 → F) where
  toFun v i := v.val i.castSucc
  invFun v := ⟨![v 0,v 1,0], by simp⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact v.property.symm
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem point_dim : Module.finrank F (point (F := F)) = 1 := by
  rw [pointEquiv.finrank_eq, Module.finrank_self]
@[simp] theorem plane_dim : Module.finrank F (plane (F := F)) = 2 := by
  rw [planeEquiv.finrank_eq, Module.finrank_fin_fun]

def flag : Fin 3 → Submodule F (Fin 3 → F) := ![point,plane,⊤]

theorem flag_dim (i : Fin 3) : Module.finrank F (flag (F := F) i) = i.val + 1 := by
  fin_cases i
  · exact point_dim
  · exact plane_dim
  · change Module.finrank F (⊤ : Submodule F (Fin 3 → F)) = 3
    rw [finrank_top,Module.finrank_fin_fun]

theorem flag_mono : Monotone (flag (F := F)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [flag]
  exact fun _ h => h.2

private theorem upper_val (u : U F) : (specialLinear F u).val = matrix F u := rfl

private theorem upper_mem (a b c : F) : specialLinear F ⟨a,b,c⟩ ∈ unipotentSL F :=
  (specialLinear_range F).le ⟨⟨a,b,c⟩,rfl⟩

theorem point_fixed (v : Fin 3 → F) : v ∈ point ↔
    ∀ g ∈ unipotentSL F, specialLinearNatural 3 g v = v := by
  constructor
  · rintro ⟨h1,h2⟩ g hg
    rw [specialLinearNatural_apply, (mem_unipotentSL_iff F g).mp hg]
    ext i
    fin_cases i <;> simp [mulVec,dotProduct,Fin.sum_univ_three,h1,h2]
  · intro h
    have h1 := congrFun (h _ (upper_mem 1 0 0)) 0
    have h2 := congrFun (h _ (upper_mem 0 1 0)) 1
    simpa [specialLinearNatural_apply,upper_val,matrix,mulVec,dotProduct,
      Fin.sum_univ_three] using And.intro h1 h2

theorem plane_second_fixed (v : Fin 3 → F) : v ∈ plane ↔
    ∀ g ∈ unipotentSL F, specialLinearNatural 3 g v - v ∈ point := by
  constructor
  · intro hv g hg
    rw [mem_point, specialLinearNatural_apply, (mem_unipotentSL_iff F g).mp hg]
    simp [mulVec,dotProduct,Fin.sum_univ_three,(mem_plane v).mp hv]
  · intro h
    have h1 := (h _ (upper_mem 0 1 0)).1
    simpa [specialLinearNatural_apply,upper_val,matrix,mulVec,dotProduct,
      Fin.sum_univ_three] using h1

private theorem diff01 (v : Fin 3 → F) (h : v 1 ≠ 0) :
    specialLinearNatural 3 (specialLinear F ⟨(v 1)⁻¹,0,0⟩) v - v = ![1,0,0] := by
  ext i
  fin_cases i <;> simp [specialLinearNatural_apply,upper_val,matrix,mulVec,
    dotProduct,Fin.sum_univ_three,h,add_sub_cancel_left]
private theorem diff02 (v : Fin 3 → F) (h : v 2 ≠ 0) :
    specialLinearNatural 3 (specialLinear F ⟨0,0,(v 2)⁻¹⟩) v - v = ![1,0,0] := by
  ext i
  fin_cases i <;> simp [specialLinearNatural_apply,upper_val,matrix,mulVec,
    dotProduct,Fin.sum_univ_three,h,add_sub_cancel_left]
private theorem diff12 (v : Fin 3 → F) (h : v 2 ≠ 0) :
    specialLinearNatural 3 (specialLinear F ⟨0,(v 2)⁻¹,0⟩) v - v = ![0,1,0] := by
  ext i
  fin_cases i <;> simp [specialLinearNatural_apply,upper_val,matrix,mulVec,
    dotProduct,Fin.sum_univ_three,h,add_sub_cancel_left]

private theorem point_le (U : Submodule F (Fin 3 → F))
    (hU : ∀ g ∈ unipotentSL F, ∀ v ∈ U, specialLinearNatural 3 g v ∈ U)
    (hne : U ≠ ⊥) : point ≤ U := by
  have he : (![1,0,0] : Fin 3 → F) ∈ U := by
    obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    by_cases h2 : v 2 = 0
    · by_cases h1 : v 1 = 0
      · have h0 : v 0 ≠ 0 := by
          intro h0
          apply hv0
          ext i; fin_cases i <;> assumption
        have he : (v 0)⁻¹ • v = ![1,0,0] := by
          ext i; fin_cases i <;> simp [h0,h1,h2]
        exact he ▸ U.smul_mem _ hv
      · rw [← diff01 v h1]
        exact U.sub_mem (hU _ (upper_mem _ _ _) v hv) hv
    · rw [← diff02 v h2]
      exact U.sub_mem (hU _ (upper_mem _ _ _) v hv) hv
  intro v hv
  have heq : v = v 0 • (![1,0,0] : Fin 3 → F) := by
    ext i; fin_cases i <;> simp [hv.1,hv.2]
  rw [heq]
  exact U.smul_mem _ he

private theorem eq_top_of_outside (U : Submodule F (Fin 3 → F))
    (hU : ∀ g ∈ unipotentSL F, ∀ v ∈ U, specialLinearNatural 3 g v ∈ U)
    {v : Fin 3 → F} (hv : v ∈ U) (h2 : v 2 ≠ 0) : U = ⊤ := by
  have he0 : (![1,0,0] : Fin 3 → F) ∈ U := by
    rw [← diff02 v h2]
    exact U.sub_mem (hU _ (upper_mem _ _ _) v hv) hv
  have he1 : (![0,1,0] : Fin 3 → F) ∈ U := by
    rw [← diff12 v h2]
    exact U.sub_mem (hU _ (upper_mem _ _ _) v hv) hv
  have he2 : (![0,0,1] : Fin 3 → F) ∈ U := by
    have heq : (v 2)⁻¹ • (v - v 0 • ![1,0,0] - v 1 • ![0,1,0]) = ![0,0,1] := by
      ext i; fin_cases i <;> simp [h2,vecHead,vecTail]
    exact heq ▸ U.smul_mem _ (U.sub_mem (U.sub_mem hv (U.smul_mem _ he0)) (U.smul_mem _ he1))
  apply top_unique
  intro w _
  have heq : w = w 0 • ![1,0,0] + w 1 • ![0,1,0] + w 2 • ![0,0,1] := by
    ext i; fin_cases i <;> simp
  rw [heq]
  exact U.add_mem (U.add_mem (U.smul_mem _ he0) (U.smul_mem _ he1)) (U.smul_mem _ he2)

theorem flag_unique (i : Fin 3) (U : Submodule F (Fin 3 → F))
    (hd : Module.finrank F U = i.val + 1)
    (hU : ∀ g ∈ unipotentSL F, ∀ v ∈ U, specialLinearNatural 3 g v ∈ U) :
    U = flag i := by
  fin_cases i
  · exact (Submodule.eq_of_le_of_finrank_eq (point_le U hU (by
      intro hz; rw [hz, finrank_bot] at hd; omega)) (by simpa using hd.symm)).symm
  · change U = plane
    apply Submodule.eq_of_le_of_finrank_eq
    · intro v hv
      by_contra hz
      have ht := eq_top_of_outside U hU hv hz
      rw [ht,finrank_top,Module.finrank_fin_fun] at hd; norm_num at hd
    · exact hd.trans plane_dim.symm
  · apply Submodule.eq_top_of_finrank_eq
    simpa using hd

/-- Conjugate the entire standard flag by one matrix. -/
def flagFor (g : SL(3,F)) (i : Fin 3) : Submodule F (Fin 3 → F) :=
  (flag (F := F) i).map (specialLinearNatural 3 g)

theorem flagFor_dim (g : SL(3,F)) (i : Fin 3) :
    Module.finrank F (flagFor g i) = i.val + 1 :=
  ((SpecialLinearGroup.toLin' g).finrank_map_eq (flag (F := F) i)).trans (flag_dim i)

theorem flagFor_mono (g : SL(3,F)) : Monotone (flagFor g) :=
  fun _ _ h => Submodule.map_mono (flag_mono h)

private theorem conjugate_apply (g u : SL(3,F)) (v : Fin 3 → F) :
    specialLinearNatural 3 (MulAut.conj g u) (specialLinearNatural 3 g v) =
      specialLinearNatural 3 g (specialLinearNatural 3 u v) := by
  change specialLinearNatural 3 (g * u * g⁻¹) (specialLinearNatural 3 g v) = _
  simp [map_mul]

theorem flagFor_unique (g : SL(3,F)) (P : Subgroup SL(3,F))
    (hP : (unipotentSL F).map (MulAut.conj g).toMonoidHom = P)
    (i : Fin 3) (U : Submodule F (Fin 3 → F))
    (hd : Module.finrank F U = i.val + 1)
    (hU : ∀ p ∈ P, ∀ v ∈ U, specialLinearNatural 3 p v ∈ U) : U = flagFor g i := by
  let W := U.map (specialLinearNatural 3 g⁻¹)
  have hW : W = flag i := by
    apply flag_unique i W
    · exact ((SpecialLinearGroup.toLin' g⁻¹).finrank_map_eq U).trans hd
    · intro u hu w hw
      have hw' : specialLinearNatural 3 g w ∈ U := by
        rcases hw with ⟨v,hv,rfl⟩
        simpa [map_inv] using hv
      have hh := hU _ (hP ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hu) _ hw'
      change specialLinearNatural 3 (MulAut.conj g u) (specialLinearNatural 3 g w) ∈ U at hh
      rw [conjugate_apply] at hh
      exact ⟨specialLinearNatural 3 g (specialLinearNatural 3 u w),hh,by simp [map_inv]⟩
  apply le_antisymm
  · intro v hv
    refine ⟨specialLinearNatural 3 g⁻¹ v, ?_, by simp [map_inv]⟩
    rw [← hW]
    exact ⟨v,hv,rfl⟩
  · rintro v ⟨w,hw,rfl⟩
    rw [← hW] at hw
    obtain ⟨v,hv,rfl⟩ := hw
    simpa [map_inv] using hv

private theorem mem_flagFor (g : SL(3,F)) (i : Fin 3) (v : Fin 3 → F) :
    specialLinearNatural 3 g v ∈ flagFor g i ↔ v ∈ flag i := by
  constructor
  · rintro ⟨w,hw,he⟩
    have h := (SpecialLinearGroup.toLin' g).injective he
    exact h ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

theorem pointFor_fixed (g : SL(3,F)) (P : Subgroup SL(3,F))
    (hP : (unipotentSL F).map (MulAut.conj g).toMonoidHom = P)
    (v : Fin 3 → F) : v ∈ flagFor g 0 ↔
      ∀ p ∈ P, specialLinearNatural 3 p v = v := by
  obtain ⟨w,rfl⟩ := (SpecialLinearGroup.toLin' g).surjective v
  have hmem : specialLinearNatural 3 g w ∈ flagFor g 0 ↔ w ∈ point := by
    exact mem_flagFor g _ _
  change specialLinearNatural 3 g w ∈ flagFor g 0 ↔ _
  rw [hmem,point_fixed]
  constructor
  · intro h p hp
    rw [← hP] at hp
    obtain ⟨u,hu,rfl⟩ := hp
    change specialLinearNatural 3 (MulAut.conj g u) (specialLinearNatural 3 g w) = _
    rw [conjugate_apply,h u hu]
    rfl
  · intro h u hu
    apply (SpecialLinearGroup.toLin' g).injective
    change specialLinearNatural 3 g (specialLinearNatural 3 u w) = specialLinearNatural 3 g w
    rw [← conjugate_apply]
    exact h _ (hP ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hu)

theorem planeFor_second_fixed (g : SL(3,F)) (P : Subgroup SL(3,F))
    (hP : (unipotentSL F).map (MulAut.conj g).toMonoidHom = P)
    (v : Fin 3 → F) : v ∈ flagFor g 1 ↔
      ∀ p ∈ P, specialLinearNatural 3 p v - v ∈ flagFor g 0 := by
  obtain ⟨w,rfl⟩ := (SpecialLinearGroup.toLin' g).surjective v
  have hmem : specialLinearNatural 3 g w ∈ flagFor g 1 ↔ w ∈ plane := by
    exact mem_flagFor g _ _
  have hdiff (u : SL(3,F)) :
      specialLinearNatural 3 (MulAut.conj g u) (specialLinearNatural 3 g w) -
        specialLinearNatural 3 g w ∈ flagFor g 0 ↔ specialLinearNatural 3 u w - w ∈ point := by
    rw [conjugate_apply,← map_sub]
    exact mem_flagFor g _ _
  change specialLinearNatural 3 g w ∈ flagFor g 1 ↔ _
  rw [hmem,plane_second_fixed]
  constructor
  · intro h p hp
    rw [← hP] at hp
    obtain ⟨u,hu,rfl⟩ := hp
    exact (hdiff u).mpr (h u hu)
  · intro h u hu
    exact (hdiff u).mp (h _ (hP ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hu))

/-- The two intrinsic fixed-space descriptions also control additive actors.
No field-linearity assumption is made on the outer action. -/
theorem flagFor_preserved (g : SL(3,F)) (P : Subgroup SL(3,F))
    (hP : (unipotentSL F).map (MulAut.conj g).toMonoidHom = P)
    (b : (Fin 3 → F) →+ (Fin 3 → F))
    (hb : ∀ p ∈ P, ∃ q ∈ P, ∀ v,
      specialLinearNatural 3 p (b v) = b (specialLinearNatural 3 q v)) :
    ∀ i, ∀ v ∈ flagFor g i, b v ∈ flagFor g i := by
  have hpoint : ∀ v ∈ flagFor g 0, b v ∈ flagFor g 0 := by
    intro v hv
    rw [pointFor_fixed g P hP] at hv ⊢
    intro p hp
    obtain ⟨q,hq,he⟩ := hb p hp
    rw [he,hv q hq]
  intro i v hv
  fin_cases i
  · exact hpoint v hv
  · change v ∈ flagFor g 1 at hv
    change b v ∈ flagFor g 1
    rw [planeFor_second_fixed g P hP] at hv ⊢
    intro p hp
    obtain ⟨q,hq,he⟩ := hb p hp
    rw [he,← map_sub]
    exact hpoint _ (hv q hq)
  · change b v ∈ (⊤ : Submodule F (Fin 3 → F)).map (specialLinearNatural 3 g)
    obtain ⟨w,hw⟩ := (SpecialLinearGroup.toLin' g).surjective (b v)
    exact ⟨w, trivial, hw⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3.Model
