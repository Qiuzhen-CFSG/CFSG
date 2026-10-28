module
public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Perfect
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Transport
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.AtlasPort.LinearGroups.SL2Order
/-!
# Full root-plane normalizers in central PSL₃(4) covers

An elementary subgroup whose image has order16 is aligned with an actual
root plane by Sylow conjugacy. Its entire normalizer is consequently the
original lifted point or line parabolic. The affine quotient computes its
order and center; central Sylow transfer proves perfectness.
Source: Aschbacher–Smith I.2.2 and 2.4.11, printed pp.410, 532.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Four.FullPlaneNormalizer
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3Four.ElementaryParabolic
lemma affine_center : center (Matrix.SL2.Affine F) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have ht := (center_le_centralizer (Matrix.SL2.translations F : Set (Matrix.SL2.Affine F))) hx
  rw [Matrix.SL2.centralizer_translations_eq, ← Matrix.SL2.range_inl_eq_translations] at ht
  obtain ⟨v,rfl⟩ := ht
  have hv : v = 1 := fixed_natural_eq_one F v (by
    intro g
    have he := congrArg SemidirectProduct.left (mem_center_iff.mp hx (SemidirectProduct.inr g))
    simpa only [SemidirectProduct.mul_left,SemidirectProduct.left_inl,
      SemidirectProduct.right_inl,SemidirectProduct.left_inr,
      SemidirectProduct.right_inr,map_one,MulAut.one_apply,mul_one,one_mul] using he)
  simp [hv]

lemma rootPlane_card (b : Bool) : Nat.card (rootPlane F b) = 16 := by
  have he : rootPlane F b = (if b then V₁ F else V₂ F).map (projective F) := by
    rw [rootPlane,rootPlaneSL,Subgroup.map_map]
    rfl
  rw [he,card_map_of_injective (projective_injective F)]
  cases b
  · norm_num only [Bool.false_eq_true,if_false,card_V₂,card_F]
  · norm_num only [if_true,card_V₁,card_F]

lemma elementary_plane (A : Subgroup PSL) [IsElementaryAbelian 2 A]
    (hA : A ≤ unipotent F) (hc : Nat.card A = 16) :
    ∃ b : Bool, A = rootPlane F b := by
  let B : Subgroup (U F) :=
    (A.subgroupOf (unipotent F)).map (unipotentEquiv F).symm.toMonoidHom
  let : IsElementaryAbelian 2 (A.subgroupOf (unipotent F)) := IsElementaryAbelian.subgroupOf hA
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have he (b : Bool) : rootPlane F b = (if b then V₁ F else V₂ F).map (projective F) := by
    rw [rootPlane,rootPlaneSL,Subgroup.map_map]
    rfl
  have hle (V : Subgroup (U F)) (hB : B ≤ V) : A ≤ V.map (projective F) := by
    intro a ha
    let u : unipotent F := ⟨a,hA ha⟩
    refine ⟨(unipotentEquiv F).symm u,hB (mem_map_of_mem _ (show u ∈ A.subgroupOf (unipotent F) from ha)),?_⟩
    change ((unipotentEquiv F) ((unipotentEquiv F).symm u) : PSL) = a
    rw [MulEquiv.apply_symm_apply]
  rcases elementary_le_plane F B with h | h
  · refine ⟨true,eq_of_le_of_card_ge ?_ (by rw [rootPlane_card,hc])⟩
    simpa only [he,if_true] using hle (V₁ F) h
  · refine ⟨false,eq_of_le_of_card_ge ?_ (by rw [rootPlane_card,hc])⟩
    simpa only [he,Bool.false_eq_true,if_false] using hle (V₂ F) h

variable {E : Type*} [Group E] [Finite E]
lemma full_plane_normalizer_alignment (f : E →* PSL) (hf : Function.Surjective f)
    (Q : Subgroup E) [IsElementaryAbelian 2 Q]
    (hk : f.ker ≤ Q) (hc : Nat.card Q = Nat.card f.ker * 16) :
    ∃ g : PSL, ∃ b : Bool,
      normalizer (Q : Set E) = liftedParabolic ((MulAut.conj g).toMonoidHom.comp f) b := by
  let A := Q.map f
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hAc : Nat.card A = 16 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map Q f
    rw [inf_eq_right.mpr hk,hc] at hh
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := f.ker)) hh
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL P (unipotentSylow F (n := 2) (by decide) (by simpa using card_F))
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have hAU : Q.map f' ≤ unipotent F := by
    have hP' := congrArg Sylow.toSubgroup hg
    change (P : Subgroup PSL).map (MulAut.conj g).toMonoidHom = unipotent F at hP'
    rw [←hP',show f' = (MulAut.conj g).toMonoidHom.comp f from rfl,←Subgroup.map_map]
    exact map_mono hP
  let : IsElementaryAbelian 2 (Q.map f') := IsElementaryAbelian.map f'
  have hAc' : Nat.card (Q.map f') = 16 := by
    rw [show f' = (MulAut.conj g).toMonoidHom.comp f from rfl,←Subgroup.map_map,card_map_of_injective (MulAut.conj g).injective]
    exact hAc
  obtain ⟨b,hb⟩ := elementary_plane (Q.map f') hAU hAc'
  have hQ : Q = (rootPlane F b).comap f' := by
    rw [←hb,comap_map_eq_self (hker ▸ hk)]
  refine ⟨g,b,?_⟩
  rw [hQ,←comap_normalizer_eq_of_surjective _ hf',normalizer_rootPlane]
end Matrix.PSL3Four.FullPlaneNormalizer
namespace Matrix.PSL3Four.FullPlaneNormalizer
open Matrix.PSL3Four.ElementaryParabolic
variable {E : Type*} [Group E] [Finite E]
omit [Finite E] in
lemma parabolic_center (f : E →* PSL) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (b : Bool) :
    (center (liftedParabolic f b)).map (liftedParabolic f b).subtype = f.ker := by
  let P := liftedParabolic f b
  let a := parabolicAffine f b
  have ha := parabolicAffine_surjective f hf b
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    have hya : a y ∈ center (Matrix.SL2.Affine F) := by
      apply mem_center_iff.mpr
      intro z
      obtain ⟨w,rfl⟩ := ha z
      simpa only [a,map_mul] using congrArg a (mem_center_iff.mp hy w)
    have hy1 : a y = 1 := by simpa only [affine_center,mem_bot] using hya
    have hyk : y ∈ a.ker := hy1
    rw [show a.ker = f.ker.comap P.subtype from parabolicAffine_ker f b] at hyk
    exact hyk
  · intro x hx
    have hP : x ∈ P := (Matrix.PSL3.RootPlaneGeometry.parabolic F b).ker_le_comap f hx
    refine ⟨⟨x,hP⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext (mem_center_iff.mp (hk hx) y)

omit [Finite E] in
lemma parabolic_card (f : E →* PSL) (hf : Function.Surjective f) (b : Bool) :
    Nat.card (liftedParabolic f b) = 960 * Nat.card f.ker := by
  let P := liftedParabolic f b
  let a := parabolicAffine f b
  have ha := parabolicAffine_surjective f hf b
  have hk : Nat.card a.ker = Nat.card f.ker := by
    rw [show a.ker = f.ker.subgroupOf P from parabolicAffine_ker f b]
    exact Nat.card_congr (subgroupOfEquivOfLe ((Matrix.PSL3.RootPlaneGeometry.parabolic F b).ker_le_comap f)).toEquiv
  have hc : Nat.card (Matrix.SL2.Affine F) = 960 := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
      show Nat.card (Multiplicative (Fin 2 → F)) = Nat.card (Fin 2 → F) from rfl,
      Nat.card_fun,Nat.card_fin,Atlas.card_sl_two,card_F]
    norm_num
  have hh := a.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr ha,card_top,hk,hc] at hh
  exact hh.symm.trans (Nat.mul_comm _ _)

lemma full_plane_normalizer [Group.IsPerfect E]
    (f : E →* PSL) (hf : Function.Surjective f) (hcentral : f.ker ≤ center E)
    (Q : Subgroup E) [IsElementaryAbelian 2 Q]
    (hk : f.ker ≤ Q) (hc : Nat.card Q = Nat.card f.ker * 16) :
    Group.IsPerfect (normalizer (Q : Set E)) ∧
      Nat.card (normalizer (Q : Set E)) = 960 * Nat.card f.ker ∧
      (center (normalizer (Q : Set E))).map (normalizer (Q : Set E)).subtype = f.ker := by
  obtain ⟨g,b,hN⟩ := full_plane_normalizer_alignment f hf Q hk hc
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker = f.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have hcentral' : f'.ker ≤ center E := hker ▸ hcentral
  have hp : IsPGroup 2 f'.ker := by
    rw [hker]
    exact (IsElementaryAbelian.isPGroup 2 Q).of_injective (inclusion hk) (inclusion_injective hk)
  rw [hN]
  exact ⟨parabolic_isPerfect f' hf' hcentral' hp b,
    (parabolic_card f' hf' b).trans (by rw [hker]),
    (parabolic_center f' hf' hcentral' b).trans hker⟩
end Matrix.PSL3Four.FullPlaneNormalizer
