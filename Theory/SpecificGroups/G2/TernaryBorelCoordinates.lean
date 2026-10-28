module
public import Theory.SpecificGroups.G2.TernaryBorelRadicals

/-!
# Whole-Borel automorphisms in ternary root coordinates

For a radical-preserving automorphism normalizing the split torus, torus
fixation confines the six root images to three two-dimensional weight
spaces. Commuting root pairs eliminate the unwanted coordinates, and the
mixed simple-root relation determines four of the remaining scalars.
The entire Borel action has two nonzero root scalars and two central shifts.
An explicit torus conjugation removes both root scalars simultaneously.

MaximalMiddleRigidity applies these formulas to the original I.4.5
middle restrictions and performs that actual endpoint-inner correction.
Extending the remaining central shifts is a separate obligation.
Source: Aschbacher–Smith I.4.5, p.417, via F.4.26, p.288. The imported
root conventions retain the ATLAS attribution and license in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
namespace Atlas.G2.TernaryBorel
@[simp] private theorem three_eq_zero : (3:ZMod 3)=0 := by decide
@[simp] private theorem six_eq_zero : (6:ZMod 3)=0 := by decide

def axis (i : Fin 6) (a : ZMod 3) : Fin 6 → ZMod 3 := ![if i=0 then a else 0,if i=1 then a else 0,if i=2 then a else 0,
    if i=3 then a else 0,if i=4 then a else 0,if i=5 then a else 0]

def root (i : Fin 6) (a : ZMod 3) : B := positive (axis i a)

@[simp] theorem root_zero (i : Fin 6) : root i 0=1 := by
  apply Subtype.ext
  simp [root,positive,axis,unipotentProduct]

theorem root_add (i : Fin 6) (a b : ZMod 3) : root i (a+b)=root i a*root i b := by
  apply Subtype.ext
  fin_cases i <;> simp [root,positive,axis,unipotentProduct,
    rootA_add,rootB_add,rootC_add,rootD_add,rootE_add,rootF_add]

theorem root_pow (i : Fin 6) (a : ZMod 3) (n : ℕ) : root i a^n=root i (n*a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,ih,←root_add]; congr 1; push_cast; ring

theorem positive_roots (v : Fin 6 → ZMod 3) : positive v=
    root 0 (v 0)*root 1 (v 1)*root 2 (v 2)*root 3 (v 3)*root 4 (v 4)*root 5 (v 5) := by
  apply Subtype.ext
  simp [root,positive,axis,unipotentProduct]

private theorem fixed_AF (v : Fin 6 → ZMod 3)
    (h : diagonal (-1) (-1)*positive v*(diagonal (-1) (-1))⁻¹=positive v) :
    v= ![v 0,0,0,0,0,v 5] := by
  rw [diagonal_positive] at h
  have he := positive_injective h
  have hz (i : Fin 6) (hi : i=1 ∨ i=2 ∨ i=3 ∨ i=4) : v i=0 := by
    have hh := congrFun he i
    rcases hi with rfl | rfl | rfl | rfl <;>
      norm_num [torusUnipotentParameters] at hh <;>
      exact (by decide : ∀ z : ZMod 3,-z=z → z=0) _ hh
  ext i
  fin_cases i <;> simp [hz]

private theorem fixed_BD (v : Fin 6 → ZMod 3)
    (h : diagonal (-1) 1*positive v*(diagonal (-1) 1)⁻¹=positive v) :
    v= ![0,v 1,0,v 3,0,0] := by
  rw [diagonal_positive] at h
  have he := positive_injective h
  have hz (i : Fin 6) (hi : i=0 ∨ i=2 ∨ i=4 ∨ i=5) : v i=0 := by
    have hh := congrFun he i
    rcases hi with rfl | rfl | rfl | rfl <;>
      norm_num [torusUnipotentParameters] at hh <;>
      exact (by decide : ∀ z : ZMod 3,-z=z → z=0) _ hh
  ext i
  fin_cases i <;> simp [hz]

private theorem fixed_CE (v : Fin 6 → ZMod 3)
    (h : diagonal 1 (-1)*positive v*(diagonal 1 (-1))⁻¹=positive v) :
    v= ![0,0,v 2,0,v 4,0] := by
  rw [diagonal_positive] at h
  have he := positive_injective h
  have hz (i : Fin 6) (hi : i=0 ∨ i=1 ∨ i=3 ∨ i=5) : v i=0 := by
    have hh := congrFun he i
    rcases hi with rfl | rfl | rfl | rfl <;>
      norm_num [torusUnipotentParameters] at hh <;>
      exact (by decide : ∀ z : ZMod 3,-z=z → z=0) _ hh
  ext i
  fin_cases i <;> simp [hz]

private theorem mapped_fixed (δ : MulAut B)
    (hfix : ∀ x∈A.subgroupOf B,δ x=x)
    (l m : (ZMod 3)ˣ) (i : Fin 6) (v : Fin 6 → ZMod 3)
    (hv : δ (root i 1)=positive v)
    (h : diagonal l m*root i 1*(diagonal l m)⁻¹=root i 1) :
    diagonal l m*positive v*(diagonal l m)⁻¹=positive v := by
  have ht := hfix (diagonal l m) ⟨(l,m),rfl⟩
  have he := congrArg δ h
  simpa only [map_mul,map_inv,ht,hv] using he

private theorem root_fixed_AF (i : Fin 6) (hi : i=0 ∨ i=5) :
    diagonal (-1) (-1)*root i 1*(diagonal (-1) (-1))⁻¹=root i 1 := by
  rcases hi with rfl | rfl <;> change _*positive _*_=positive _ <;> rw [diagonal_positive]
  all_goals apply congrArg positive; decide +kernel
private theorem root_fixed_BD (i : Fin 6) (hi : i=1 ∨ i=3) :
    diagonal (-1) 1*root i 1*(diagonal (-1) 1)⁻¹=root i 1 := by
  rcases hi with rfl | rfl <;> change _*positive _*_=positive _ <;> rw [diagonal_positive]
  all_goals apply congrArg positive; decide +kernel
private theorem root_fixed_CE (i : Fin 6) (hi : i=2 ∨ i=4) :
    diagonal 1 (-1)*root i 1*(diagonal 1 (-1))⁻¹=root i 1 := by
  rcases hi with rfl | rfl <;> change _*positive _*_=positive _ <;> rw [diagonal_positive]
  all_goals apply congrArg positive; decide +kernel

private theorem root_images_AF (δ : MulAut B)
    (hfix : ∀ x∈A.subgroupOf B,δ x=x) (i : Fin 6) (hi : i=0 ∨ i=5) :
    ∃ a b,δ (root i 1)=positive ![a,0,0,0,0,b] := by
  obtain ⟨v,hv⟩ := exists_positive_image δ (axis i 1)
  have he := fixed_AF v (mapped_fixed δ hfix (-1) (-1) i v hv (root_fixed_AF i hi))
  exact ⟨v 0,v 5,hv.trans (congrArg positive he)⟩
private theorem root_images_BD (δ : MulAut B)
    (hfix : ∀ x∈A.subgroupOf B,δ x=x) (i : Fin 6) (hi : i=1 ∨ i=3) :
    ∃ a b,δ (root i 1)=positive ![0,a,0,b,0,0] := by
  obtain ⟨v,hv⟩ := exists_positive_image δ (axis i 1)
  have he := fixed_BD v (mapped_fixed δ hfix (-1) 1 i v hv (root_fixed_BD i hi))
  exact ⟨v 1,v 3,hv.trans (congrArg positive he)⟩
private theorem root_images_CE (δ : MulAut B)
    (hfix : ∀ x∈A.subgroupOf B,δ x=x) (i : Fin 6) (hi : i=2 ∨ i=4) :
    ∃ a b,δ (root i 1)=positive ![0,0,a,0,b,0] := by
  obtain ⟨v,hv⟩ := exists_positive_image δ (axis i 1)
  have he := fixed_CE v (mapped_fixed δ hfix 1 (-1) i v hv (root_fixed_CE i hi))
  exact ⟨v 2,v 4,hv.trans (congrArg positive he)⟩

end Atlas.G2.TernaryBorel

namespace Atlas.G2.TernaryBorel
private theorem root_commuting (i j : Fin 6)
    (h : (i=4 ∧ (j=0 ∨ j=3)) ∨ (i=5 ∧ (j=1 ∨ j=2))) :
    root i 1*root j 1=root j 1*root i 1 := by
  rcases h with ⟨rfl,rfl | rfl⟩ | ⟨rfl,rfl | rfl⟩
  all_goals change positive _*positive _=positive _*positive _
  all_goals rw [positive_mul,positive_mul]; apply congrArg positive; decide +kernel

private theorem FE_relation : root 5 1*root 4 1=
    (root 0 1)⁻¹*(root 1 1)⁻¹*root 2 1*(root 3 1)⁻¹*root 4 1*root 5 1 := by
  change positive _*positive _=(positive _)⁻¹*(positive _)⁻¹*positive _*(positive _)⁻¹*positive _*positive _
  simp only [positive_inv,positive_mul]
  apply congrArg positive; decide +kernel

/-- A torus-normalizing Borel automorphism that fixes the radicals has only
 two nonzero root scalars and two central simple-root shifts. -/
theorem automorphism_root_coordinates (δ : MulAut B)
    (hA : (A.subgroupOf B).map δ.toMonoidHom=A.subgroupOf B)
    (hfixed : ∀ side,(middleRadical side).map δ.toMonoidHom=middleRadical side) :
    ∃ (e f j k : ZMod 3),e≠0 ∧ f≠0 ∧
      δ (root 0 1)=root 0 f ∧ δ (root 1 1)=root 1 (e*f) ∧
      δ (root 2 1)=root 2 e ∧ δ (root 3 1)=root 3 (e*f) ∧
      δ (root 4 1)=positive ![0,0,k,0,e,0] ∧
      δ (root 5 1)=positive ![j,0,0,0,0,f] := by
  have hfix := automorphism_torus_pointwise δ hA hfixed
  obtain ⟨a,a',ha⟩ := root_images_AF δ hfix 0 (Or.inl rfl)
  obtain ⟨b,b',hb⟩ := root_images_BD δ hfix 1 (Or.inl rfl)
  obtain ⟨c,c',hc⟩ := root_images_CE δ hfix 2 (Or.inl rfl)
  obtain ⟨d',d,hd⟩ := root_images_BD δ hfix 3 (Or.inr rfl)
  obtain ⟨k,e,he⟩ := root_images_CE δ hfix 4 (Or.inr rfl)
  obtain ⟨j,f,hf⟩ := root_images_AF δ hfix 5 (Or.inr rfl)
  have hiff (x : B) (side : Bool) : δ x∈middleRadical side ↔ x∈middleRadical side := by
    nth_rw 1 [←hfixed side]
    exact mem_map_iff_mem (f:=δ.toMonoidHom) δ.injective
  have henz : e≠0 := by
    intro hz
    have hm : δ (root 4 1)∈middleRadical true := by rw [he,positive_mem_radical]; exact hz
    have hh := (positive_mem_radical (axis 4 1) true).mp ((hiff _ _).mp hm)
    exact one_ne_zero hh
  have hfnz : f≠0 := by
    intro hz
    have hm : δ (root 5 1)∈middleRadical false := by rw [hf,positive_mem_radical]; exact hz
    have hh := (positive_mem_radical (axis 5 1) false).mp ((hiff _ _).mp hm)
    exact one_ne_zero hh
  have ha' : a'=0 := by
    have h := congrArg δ (root_commuting 4 0 (Or.inl ⟨rfl,Or.inl rfl⟩))
    simp only [map_mul,he,ha,positive_mul] at h
    have hh := congrFun (positive_injective h) 3
    have hz : e*a'=0 := by simpa [unipotentProductParameters] using hh.symm
    exact (mul_eq_zero.mp hz).resolve_left henz
  have hb' : b'=0 := by
    have h := congrArg δ (root_commuting 5 1 (Or.inr ⟨rfl,Or.inl rfl⟩))
    simp only [map_mul,hf,hb,positive_mul] at h
    have hh := congrFun (positive_injective h) 2
    dsimp [unipotentProductParameters] at hh
    simp at hh
    have hz : b'*f=0 := by
      simpa [mul_eq_zero,show (2:ZMod 3)≠0 from by decide] using hh
    exact (mul_eq_zero.mp hz).resolve_right hfnz
  have hc' : c'=0 := by
    have h := congrArg δ (root_commuting 5 2 (Or.inr ⟨rfl,Or.inr rfl⟩))
    simp only [map_mul,hf,hc,positive_mul] at h
    have hh := congrFun (positive_injective h) 3
    have hz : c'*f=0 := by simpa [unipotentProductParameters] using hh
    exact (mul_eq_zero.mp hz).resolve_right hfnz
  have hd' : d'=0 := by
    have h := congrArg δ (root_commuting 4 3 (Or.inl ⟨rfl,Or.inr rfl⟩))
    simp only [map_mul,he,hd,positive_mul] at h
    have hh := congrFun (positive_injective h) 0
    dsimp [unipotentProductParameters] at hh
    simp at hh
    exact hh.resolve_right henz
  subst a'; subst b'; subst c'; subst d'
  have hrel := congrArg δ FE_relation
  simp only [map_mul,map_inv,ha,hb,hc,hd,he,hf] at hrel
  simp only [positive_inv,positive_mul] at hrel
  have hcoord := positive_injective hrel
  have hesq : e^2=1 := (by decide : ∀ x : ZMod 3,x≠0 → x^2=1) e henz
  have hfsq : f^2=1 := (by decide : ∀ x : ZMod 3,x≠0 → x^2=1) f hfnz
  have haeq : a=f := by
    have hh := congrFun hcoord 0
    dsimp [unipotentProductParameters,unipotentInverseParameters] at hh
    simp [hesq,ZMod.pow_card] at hh
    linear_combination hh
  have hbeq : b=e*f := by
    have hh := congrFun hcoord 1
    dsimp [unipotentProductParameters,unipotentInverseParameters] at hh
    simp [ZMod.pow_card] at hh
    exact hh.symm
  have hceq : c=e := by
    have hh := congrFun hcoord 2
    dsimp [unipotentProductParameters,unipotentInverseParameters] at hh
    norm_num [hfsq] at hh
    linear_combination -hh
  have hdeq : d=e*f := by
    have hh := congrFun hcoord 3
    dsimp [unipotentProductParameters,unipotentInverseParameters] at hh
    norm_num [] at hh
    exact hh.symm
  subst a; subst b; subst c; subst d
  exact ⟨e,f,j,k,henz,hfnz,ha,hb,hc,hd,he,hf⟩
end Atlas.G2.TernaryBorel

namespace Atlas.G2.TernaryBorel
/-- The four parameters determine the action on all six unipotent coordinates. -/
def twistCoordinates (e f j k : ZMod 3) (v : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  ![f*v 0+j*v 5,e*f*v 1,e*v 2+k*v 4,e*f*v 3,e*v 4,f*v 5]

private theorem positive_AF_pow (a b : ZMod 3) (n : ℕ) :
    positive ![a,0,0,0,0,b]^n=positive ![n*a,0,0,0,0,n*b] := by
  induction n with
  | zero => apply Subtype.ext; simp [positive,unipotentProduct]
  | succ n ih =>
    rw [pow_succ,ih,positive_mul]
    apply congrArg positive
    ext i
    fin_cases i <;> dsimp [unipotentProductParameters] <;> push_cast <;> ring
private theorem positive_CE_pow (a b : ZMod 3) (n : ℕ) :
    positive ![0,0,a,0,b,0]^n=positive ![0,0,n*a,0,n*b,0] := by
  induction n with
  | zero => apply Subtype.ext; simp [positive,unipotentProduct]
  | succ n ih =>
    rw [pow_succ,ih,positive_mul]
    apply congrArg positive
    ext i
    fin_cases i <;> dsimp [unipotentProductParameters] <;> push_cast <;> ring

private theorem hom_root_parameter {H : Type*} [Group H] (δ : B →* H)
    (i : Fin 6) (a : ZMod 3) : δ (root i a)=δ (root i 1)^a.val := by
  rw [←map_pow,root_pow]
  simp

/-- Explicit action on every element of the entire order-729 root group. -/
theorem automorphism_positive_coordinates (δ : MulAut B)
    (hA : (A.subgroupOf B).map δ.toMonoidHom=A.subgroupOf B)
    (hfixed : ∀ side,(middleRadical side).map δ.toMonoidHom=middleRadical side) :
    ∃ (e f j k : ZMod 3),e≠0 ∧ f≠0 ∧
      ∀ v,δ (positive v)=positive (twistCoordinates e f j k v) := by
  obtain ⟨e,f,j,k,henz,hfnz,ha,hb,hc,hd,he,hf⟩ :=
    automorphism_root_coordinates δ hA hfixed
  refine ⟨e,f,j,k,henz,hfnz,?_⟩
  intro v
  rw [positive_roots]
  simp only [δ.map_mul]
  have hp (i : Fin 6) (x : ZMod 3) : δ (root i x)=δ (root i 1)^x.val :=
    hom_root_parameter δ.toMonoidHom i x
  simp only [hp 0 (v 0),hp 1 (v 1),hp 2 (v 2),hp 3 (v 3),hp 4 (v 4),hp 5 (v 5)]
  simp only [ha,hb,hc,hd,he,hf]
  simp only [root_pow,positive_CE_pow,positive_AF_pow]
  simp only [ZMod.natCast_zmod_val,root,axis,if_true,if_false,Fin.reduceEq]
  simp only [positive_mul]
  apply congrArg positive
  ext i
  fin_cases i <;> dsimp [twistCoordinates,unipotentProductParameters] <;> ring_nf
  all_goals reduce_mod_char

/-- Every whole-middle element has one unipotent part and one split-torus part. -/
theorem exists_positive_diagonal (x : B) :
    ∃ (v : Fin 6 → ZMod 3) (l m : (ZMod 3)ˣ),x=positive v*diagonal l m := by
  obtain ⟨⟨u,a⟩,he⟩ := borelProductEquiv.surjective x
  obtain ⟨u,hu⟩ := u
  rw [unipotent_eq_range] at hu
  obtain ⟨v,rfl⟩ := hu
  obtain ⟨a,⟨⟨l,m⟩,rfl⟩⟩ := a
  exact ⟨v,l,m,he.symm⟩

/-- The formula includes the entire Borel, with its literal torus factor. -/
theorem automorphism_whole_coordinates (δ : MulAut B)
    (hA : (A.subgroupOf B).map δ.toMonoidHom=A.subgroupOf B)
    (hfixed : ∀ side,(middleRadical side).map δ.toMonoidHom=middleRadical side) :
    ∃ (e f j k : ZMod 3),e≠0 ∧ f≠0 ∧
      ∀ (v : Fin 6 → ZMod 3) (l m : (ZMod 3)ˣ),
        δ (positive v*diagonal l m)=positive (twistCoordinates e f j k v)*diagonal l m := by
  obtain ⟨e,f,j,k,he,hf,h⟩ := automorphism_positive_coordinates δ hA hfixed
  refine ⟨e,f,j,k,he,hf,?_⟩
  intro v l m
  rw [map_mul,h,automorphism_torus_pointwise δ hA hfixed (diagonal l m) ⟨(l,m),rfl⟩]
end Atlas.G2.TernaryBorel

namespace Atlas.G2.TernaryBorel
/-- A simultaneous endpoint-inner correction removes the two root scalars. -/
theorem exists_diagonal_normalization (δ : MulAut B)
    (hA : (A.subgroupOf B).map δ.toMonoidHom=A.subgroupOf B)
    (hfixed : ∀ side,(middleRadical side).map δ.toMonoidHom=middleRadical side) :
    ∃ (a : B) (j k : ZMod 3),a∈A.subgroupOf B ∧
      ∀ (v : Fin 6 → ZMod 3) (l m : (ZMod 3)ˣ),
        MulAut.conj a (δ (positive v*diagonal l m))=
          positive (twistCoordinates 1 1 j k v)*diagonal l m := by
  obtain ⟨e,f,j,k,he,hf,h⟩ := automorphism_whole_coordinates δ hA hfixed
  let eu : (ZMod 3)ˣ := Units.mk0 e he
  let fu : (ZMod 3)ˣ := Units.mk0 f hf
  refine ⟨diagonal eu (eu*fu),f*j,e*k,⟨(eu,eu*fu),rfl⟩,?_⟩
  intro v l m
  rw [h,map_mul]
  have hdiag : MulAut.conj (diagonal eu (eu*fu)) (diagonal l m)=diagonal l m := by
    apply Subtype.ext
    change (MulAut.conj (torus eu (eu*fu))) (torus l m)=torus l m
    change torus eu (eu*fu)*torus l m*(torus eu (eu*fu))⁻¹=torus l m
    have hc : torus eu (eu*fu)*torus l m=torus l m*torus eu (eu*fu) :=
      ((Commute.all (eu,eu*fu) (l,m)).map torusHom).eq
    rw [hc,mul_inv_cancel_right]
  rw [hdiag]
  congr 1
  change diagonal eu (eu*fu)*positive _*(diagonal eu (eu*fu))⁻¹=positive _
  rw [diagonal_positive]
  apply congrArg positive
  rcases (by decide : ∀ a : ZMod 3,a≠0 → a=1 ∨ a= -1) e he with rfl | rfl <;>
    rcases (by decide : ∀ a : ZMod 3,a≠0 → a=1 ∨ a= -1) f hf with rfl | rfl
  all_goals ext i; fin_cases i <;> dsimp [torusUnipotentParameters,twistCoordinates,eu,fu] <;>
    norm_num <;> ring

end Atlas.G2.TernaryBorel
