module

public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots.Coordinates
public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots.Transport
public import Theory.SpecificGroups.SU3.ExtensionBorel.Matrix
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SU3.SylowOmega

/-!
# Isotropic-line transitivity forces generation in SU₃

A special unitary matrix stabilizing the first coordinate line is upper
triangular and normalizes the full upper root group, hence its center.
A subgroup transitive on isotropic lines and containing that center thus
contains every conjugate center. Quasisimplicity makes their noncentral
normal closure the whole SU₃, retaining its possible scalar center.

The marked central transvections have square one. A Sylow subgroup containing
them therefore contains them in its center by the existing binary Sylow omega
calculation. This connects the matrix generation statement to three literal
conjugates of every Sylow center.

Source: Huppert II.10.12, with the SU₃ Sylow geometry used in
Aschbacher--Smith K.3.3, printed p.456.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open HermitianForm.BorelTorus HermitianForm.BorelTorus.EvenCenterAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2] (J : HermitianForm 3 F)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
  (hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ s)

omit [Finite F] [CharP F 2] in
private theorem special_root_injective : Function.Injective (hermitianUnipotentSU J hJ) := by
  intro z w h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun x : J.specialSubgroup => x.val.val 0 1) h)
    (congrArg (fun x : J.specialSubgroup => x.val.val 0 2) h)

include hs hcard hfixed in
theorem central_eq_embedded_center : central J hJ =
    (center (specialRoot J hJ)).map (specialRoot J hJ).subtype := by
  let e := MonoidHom.ofInjective (special_root_injective J hJ)
  have he : ((hermitianUnipotentSU J hJ).range).subtype.comp e.toMonoidHom =
      hermitianUnipotentSU J hJ := rfl
  have hz : (center (hermitianUnipotentCoord J)).map e.toMonoidHom =
      center (specialRoot J hJ) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (centerCongr e ⟨z, hz⟩).property
    · intro hx
      exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
  change central J hJ = (center (hermitianUnipotentSU J hJ).range).map
    (hermitianUnipotentSU J hJ).range.subtype
  change (center (hermitianUnipotentCoord J)).map e.toMonoidHom =
    center (hermitianUnipotentSU J hJ).range at hz
  rw [← hz, Subgroup.map_map, he,
    HermitianForm.NormalizedRootCentralizers.coord_center J (by omega) hcard hfixed]
  exact MonoidHom.range_comp (hermitianUnipotentSU J hJ) (centralCoord J)

omit [Finite F] in
theorem central_not_le_center : ¬ central J hJ ≤ center J.specialSubgroup := by
  intro h
  let z := hermitianUnipotentSU J hJ (centralCoord J (Multiplicative.ofAdd 1))
  have hz : z ∈ central J hJ := ⟨Multiplicative.ofAdd 1, rfl⟩
  have he := mem_center_iff.mp (h hz) (hermitianWeylSU J hJ)
  have hm := congrArg (fun x : J.specialSubgroup => x.val.val 0 0) he
  have hzval : z.val.val = !![1,0,1;0,1,0;0,0,1] := by
    change (!![1,0,1;0,1,-J.conj 0;0,0,1] : Matrix (Fin 3) (Fin 3) F) = _
    simp
  have hwval : (hermitianWeylSU J hJ).val.val = !![0,0,1;0,-1,0;1,0,0] := rfl
  change ((hermitianWeylSU J hJ).val.val * z.val.val) 0 0 =
    (z.val.val * (hermitianWeylSU J hJ).val.val) 0 0 at hm
  rw [hzval, hwval] at hm
  simp [Matrix.mul_apply, Fin.sum_univ_three] at hm

include hJ in
omit [Finite F] [CharP F 2] in
private theorem upper_of_first_column (g : J.specialSubgroup)
    (h10 : g.val.val 1 0 = 0) (h20 : g.val.val 2 0 = 0) :
    g.val.val.IsUpperTriangular := by
  have hu := (J.mem_specialSubgroup_iff _).mp g.property |>.1
  rw [hJ] at hu
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) hu
  have h02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 2) hu
  have hn : J.conj (g.val.val 0 0) ≠ 0 := by
    apply left_ne_zero_of_mul_eq_one (b := g.val.val 2 2)
    simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
      h10, h20] using h02
  have h21 : g.val.val 2 1 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hn
    simpa [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
      h10, h20] using h01
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

include hs hcard hfixed in
theorem central_conjugate_of_first_column (g : J.specialSubgroup)
    (h10 : g.val.val 1 0 = 0) (h20 : g.val.val 2 0 = 0) :
    (central J hJ).map (MulAut.conj g).toMonoidHom = central J hJ := by
  have hr : (specialRoot J hJ).map (MulAut.conj g).toMonoidHom = specialRoot J hJ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
      obtain ⟨w, hw⟩ := HermitianForm.ExtensionBorel.upper_conjugates_root J hJ
        ⟨g.val, J.specialSubgroup_le_unitarySubgroup g.property⟩
        (upper_of_first_column J hJ g h10 h20) z
      exact ⟨w, Subtype.ext hw.symm⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [central_eq_embedded_center J hJ hs hcard hfixed,
    map_embeddedCenter _ _ (MulAut.conj g).injective, hr]

include hs hcard hfixed in
theorem eq_top_of_isotropicLineTransitive (H : Subgroup J.specialSubgroup)
    (hU : central J hJ ≤ H) (htrans : IsotropicLineTransitive J H) : H = ⊤ := by
  have hconj (g : J.specialSubgroup) :
      (central J hJ).map (MulAut.conj g).toMonoidHom ≤ H := by
    let v : Fin 3 → F := fun i => g.val.val i 0
    have hv : v ≠ 0 := by
      intro hzero
      have he := congrArg (fun x : J.specialSubgroup => x.val.val 0 0) (inv_mul_cancel g)
      have hz (i) : g.val.val i 0 = 0 := congrFun hzero i
      change (g.val⁻¹.val * g.val.val) 0 0 = 1 at he
      apply zero_ne_one (α := F)
      simpa only [Matrix.mul_apply, hz, mul_zero, Finset.sum_const_zero] using he
    have hi : dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0 := by
      have hu := (J.mem_specialSubgroup_iff _).mp g.property |>.1
      have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hu
      simpa [v, hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using he
    obtain ⟨k, hk, a, _, ha⟩ := htrans v hv hi
    have he (i : Fin 3) : (g⁻¹ * k).val.val i 0 = a * (g⁻¹ * g).val.val i 0 := by
      change (g.val⁻¹.val * k.val.val) i 0 = a * (g.val⁻¹.val * g.val.val) i 0
      simp only [Matrix.mul_apply, ha, v, Finset.mul_sum]
      congr 1
      funext j
      ring
    have h10 : (g⁻¹ * k).val.val 1 0 = 0 := by simpa using he 1
    have h20 : (g⁻¹ * k).val.val 2 0 = 0 := by simpa using he 2
    have hn := central_conjugate_of_first_column J hJ hs hcard hfixed
      (g⁻¹ * k) h10 h20
    have hm : (central J hJ).map (MulAut.conj k).toMonoidHom =
        (central J hJ).map (MulAut.conj g).toMonoidHom := by
      have hh := congrArg (fun U : Subgroup J.specialSubgroup =>
        U.map (MulAut.conj g).toMonoidHom) hn
      simpa only [map_conjugate_mul, mul_inv_cancel_left] using hh
    rw [← hm]
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hk (hU hx)) (H.inv_mem hk)
  have hclosure : normalClosure (central J hJ : Set J.specialSubgroup) ≤ H := by
    rw [normalClosure, closure_le]
    intro x hx
    obtain ⟨u, hu, hg⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hg
    exact hconj g ⟨u, hu, rfl⟩
  have hq : 2 < 2 ^ s := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hs)
  let : Theory.GroupTheory.IsQuasisimple J.specialSubgroup :=
    J.special_isQuasisimple_of_fixed_card hq hcard hfixed
  rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top
      (normalClosure (central J hJ : Set J.specialSubgroup)) with hz | ht
  · exact (central_not_le_center J hJ (le_normalClosure.trans hz)).elim
  · exact top_le_iff.mp (ht ▸ hclosure)

omit [Finite F] in
theorem central_square_one (x : J.specialSubgroup) (hx : x ∈ central J hJ) : x ^ 2 = 1 := by
  obtain ⟨b, rfl⟩ := hx
  have hb : b ^ 2 = 1 := by
    rw [pow_two]
    change b.toAdd + b.toAdd = 0
    exact CharTwo.add_self_eq_zero _
  change (((hermitianUnipotentSU J hJ).comp (centralCoord J)) b) ^ 2 = 1
  rw [← map_pow, hb, map_one]

include hs hcard hfixed in
theorem exists_sylowCenter_containing_central :
    ∃ P : Sylow 2 J.specialSubgroup, central J hJ ≤ sylowCenter P := by
  have hU : IsPGroup 2 (central J hJ) := by
    intro x
    exact ⟨1, Subtype.ext (central_square_one J hJ x.val x.property)⟩
  obtain ⟨P, hP⟩ := hU.exists_le_sylow
  refine ⟨P, ?_⟩
  change central J hJ ≤ (center P).map (P : Subgroup J.specialSubgroup).subtype
  rw [← (HermitianForm.SylowOmega.special_sylow_omega J hs hcard hfixed hJ P).1]
  intro x hx
  exact (omegaOneAmbient_le_iff _ _).mp le_rfl x (hP hx)
    (central_square_one J hJ x hx)

include hs hcard hfixed in
theorem generation_of_triple (b : F) (hb : b + J.conj b = 1)
    (hg : triple J hJ b hb = ⊤) : ThreeRootGeneration J.specialSubgroup := by
  obtain ⟨P, hP⟩ := exists_sylowCenter_containing_central J hJ hs hcard hfixed
  let c : Fin 3 → J.specialSubgroup := ![1, hermitianWeylSU J hJ, thirdConjugator J hJ b hb]
  apply of_one_sylow P c
  apply top_unique
  rw [← hg]
  refine sup_le (sup_le ?_ ?_) ?_
  · apply le_iSup_of_le (0 : Fin 3)
    have he : (MulAut.conj (c 0)).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [c]
    rw [he, Subgroup.map_id]
    exact hP
  · apply le_iSup_of_le (1 : Fin 3)
    exact Subgroup.map_mono hP
  · apply le_iSup_of_le (2 : Fin 3)
    exact Subgroup.map_mono hP

end Representation.SU3.CubicDegree.InnerActors.ThreeRoots
