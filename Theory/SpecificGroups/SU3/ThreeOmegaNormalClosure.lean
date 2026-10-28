module
public import Theory.SpecificGroups.SU3.ThreeOmegaGeneration
public import Theory.SpecificGroups.SU3.SylowOmegaIndex

/-!
# Three omega-centers generate their unitary normal closure

For every positive fixed-field degree, three conjugate Sylow omega-centers
contain every conjugate omega-center. The existing fixed-field block and
connector are transitive on isotropic lines. An element fixing the first
line normalizes the root group, hence its omega-center; transitivity then
puts every conjugate in the three-center span. Sylow conjugacy and a
Hermitian basis change retain the original form, and the literal scalar
projection supplies the projective version.

This includes SU₃(2), where the span need not be the full group. The DGS
Chapter 11 all-field core bound uses normal-closure transitivity instead of
full-group generation, preserving this small parameter.
Source: DGS85, Groups and Graphs (1985), (5.4) and (11.8), pp.106,176;
Huppert II.10.12, using the checked ThreeRoots block-orbit calculation.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
open Representation.SU3.CubicDegree.InnerActors
namespace BenderSuzuki.MatrixGroups.HermitianForm.ThreeOmegaNormalClosure
open ThreeRoots BorelTorus BorelTorus.EvenCenterAction OddPrimeSylow.NormalizedOuter.FormTransport
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
private instance (J : HermitianForm 3 F) : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

omit [Finite F] [CharP F 2] in
private theorem root_injective (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    Function.Injective (hermitianUnipotentSU J hJ) := by
  intro z w he
  apply Subtype.ext
  exact Prod.ext (congrArg (fun x : J.specialSubgroup => x.val.val 0 1) he)
    (congrArg (fun x : J.specialSubgroup => x.val.val 0 2) he)

omit [Finite F] in
private theorem central_eq_omega (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) :
    central J hJ = omegaCenterIn (specialRoot J hJ) := by
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨⟨centralCoord J z,rfl⟩,?_,central_square_one J hJ _ ⟨z,rfl⟩⟩
    rintro y ⟨w,rfl⟩
    exact (map_mul (hermitianUnipotentSU J hJ) w _).symm.trans
      ((congrArg (hermitianUnipotentSU J hJ)
        (mem_center_iff.mp (centralCoord_mem_center J z) w)).trans
          (map_mul (hermitianUnipotentSU J hJ) _ w))
  · intro x hx
    obtain ⟨⟨z,rfl⟩,_,hs⟩ := (mem_omegaCenterIn_iff _ _).mp hx
    have hs' : z^2=1 := root_injective J hJ (by simpa only [map_pow,map_one] using hs)
    have hz := (BinaryRootFrattini.square_one_iff J z).mp hs'
    have hf : J.conj z.val.2 = z.val.2 := by
      have hh := z.property
      rw [hz,zero_mul,add_zero] at hh
      exact (eq_neg_of_add_eq_zero_right hh).trans (CharTwo.neg_eq _)
    refine ⟨Multiplicative.ofAdd ⟨z.val.2,hf⟩,?_⟩
    apply congrArg (hermitianUnipotentSU J hJ)
    exact Subtype.ext (Prod.ext hz.symm rfl)

variable (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
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


private theorem central_conjugate_of_first_column (g : J.specialSubgroup)
    (h10 : g.val.val 1 0 = 0) (h20 : g.val.val 2 0 = 0) :
    (central J hJ).map (MulAut.conj g).toMonoidHom = central J hJ := by
  have hr : (specialRoot J hJ).map (MulAut.conj g).toMonoidHom = specialRoot J hJ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨_,⟨z,rfl⟩,rfl⟩
      obtain ⟨w,hw⟩ := ExtensionBorel.upper_conjugates_root J hJ
        ⟨g.val,J.specialSubgroup_le_unitarySubgroup g.property⟩
        (upper_of_first_column J hJ g h10 h20) z
      exact ⟨w,Subtype.ext hw.symm⟩
    · rw [card_map_of_injective (MulAut.conj g).injective]
  rw [central_eq_omega J hJ,
    NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective,hr]

private theorem conjugates_le_of_isotropicLineTransitive (H : Subgroup J.specialSubgroup)
    (hU : central J hJ ≤ H) (htrans : IsotropicLineTransitive J H) :
    ∀ g : J.specialSubgroup, (central J hJ).map (MulAut.conj g).toMonoidHom ≤ H := by
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
    have hn := central_conjugate_of_first_column J hJ
      (g⁻¹ * k) h10 h20
    have hm : (central J hJ).map (MulAut.conj k).toMonoidHom =
        (central J hJ).map (MulAut.conj g).toMonoidHom := by
      have hh := congrArg (fun U : Subgroup J.specialSubgroup =>
        U.map (MulAut.conj g).toMonoidHom) hn
      simpa only [map_conjugate_mul, mul_inv_cancel_left] using hh
    rw [← hm]
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem hk (hU hx)) (H.inv_mem hk)
  exact hconj

private theorem special_root_sylow {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = (2^n)^2)
    (hf : Nat.card {x : F // J.conj x = x} = 2^n) :
    ∃ S : Sylow 2 J.specialSubgroup, (S : Subgroup J.specialSubgroup) = specialRoot J hJ := by
  let R := EvenTwoRank.rootSylow J hJ hn hc hf
  let er : hermitianUnipotentCoord J ≃* R :=
    MonoidHom.ofInjective (EvenInner.root_injective J hJ)
  let es : hermitianUnipotentCoord J ≃* specialRoot J hJ :=
    MonoidHom.ofInjective (root_injective J hJ)
  have hp : IsPGroup 2 (specialRoot J hJ) := (BinaryRootFrattini.isTwoGroup J).of_equiv es
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have he : Nat.card S = Nat.card (specialRoot J hJ) := Nat.card_congr
    (((SylowOmega.specialSylowEquivProjective J S).trans
      ((S.mapSurjective J.specialToProjective_surjective).equiv R)).trans
        (er.symm.trans es)).toEquiv
  exact ⟨S,(eq_of_le_of_card_ge hS he.le).symm⟩

include hJ in
private theorem standard {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 J.specialSubgroup) :
    ∃ c : Fin 3 → J.specialSubgroup, ∀ g : J.specialSubgroup,
      (omegaCenterIn (P : Subgroup J.specialSubgroup)).map (MulAut.conj g).toMonoidHom ≤
        ⨆ i, (omegaCenterIn (P : Subgroup J.specialSubgroup)).map
          (MulAut.conj (c i)).toMonoidHom := by
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hc hconj
  obtain ⟨S,hS⟩ := special_root_sylow J hJ hn hc hf
  obtain ⟨a,rfl⟩ := MulAction.exists_smul_eq J.specialSubgroup S P
  have hw : omegaCenterIn ((a • S : Sylow 2 J.specialSubgroup) : Subgroup J.specialSubgroup) =
      (central J hJ).map (MulAut.conj a).toMonoidHom := by
    rw [central_eq_omega J hJ,←hS,
      NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj a).injective]
    rfl
  obtain ⟨b,hb⟩ := huppert_II_10_4_trace_surjective J (2^n) hc hf 1 (by simp)
  let c : Fin 3 → J.specialSubgroup := ![1,hermitianWeylSU J hJ,thirdConjugator J hJ b hb]
  refine ⟨fun i => c i * a⁻¹,?_⟩
  intro g
  simp only [hw,map_conjugate_mul,inv_mul_cancel_right]
  have ht := triple_transitive_of_block_orbits J hJ b hb (blockOrbitDecomposition J hJ b hb)
  apply (conjugates_le_of_isotropicLineTransitive J hJ _
    (le_sup_left.trans le_sup_left) ht (g*a)).trans
  apply sup_le (sup_le ?_ ?_) ?_
  · apply le_iSup_of_le (0 : Fin 3)
    have he : (MulAut.conj (c 0)).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [c]
    rw [he,Subgroup.map_id]
  · exact le_iSup_of_le (1 : Fin 3) le_rfl
  · exact le_iSup_of_le (2 : Fin 3) le_rfl


/-- Transport of the three-conjugate normal-closure bound through a literal isomorphism. -/
theorem of_equiv {H K : Type*} [Group H] [Group K] [Finite H]
    (e : H ≃* K)
    (hK : ∀ P : Sylow 2 K, ∃ c : Fin 3 → K, ∀ g : K,
      (omegaCenterIn (P : Subgroup K)).map (MulAut.conj g).toMonoidHom ≤
        ⨆ i, (omegaCenterIn (P : Subgroup K)).map (MulAut.conj (c i)).toMonoidHom)
    (P : Sylow 2 H) :
    ∃ c : Fin 3 → H, ∀ g : H,
      (omegaCenterIn (P : Subgroup H)).map (MulAut.conj g).toMonoidHom ≤
        ⨆ i, (omegaCenterIn (P : Subgroup H)).map (MulAut.conj (c i)).toMonoidHom := by
  obtain ⟨c,hc⟩ := hK (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  change ∀ g : K, (omegaCenterIn ((P : Subgroup H).map e.toMonoidHom)).map
    (MulAut.conj g).toMonoidHom ≤ ⨆ i,
      (omegaCenterIn ((P : Subgroup H).map e.toMonoidHom)).map
        (MulAut.conj (c i)).toMonoidHom at hc
  refine ⟨fun i => e.symm (c i),?_⟩
  intro g
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [Subgroup.map_iSup]
  simpa only [map_conjugate,
    NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective,
    MulEquiv.coe_toMonoidHom,e.apply_symm_apply,Sylow.coe_mapSurjective] using hc (e g)

omit [CharP F 2] in
/-- Three conjugate Sylow omega-centers contain every conjugate in SU₃(2ⁿ),
including n=1. The generated subgroup need not be all of SU₃(2). -/
theorem special (J : HermitianForm 3 F) {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 J.specialSubgroup) :
    ∃ c : Fin 3 → J.specialSubgroup, ∀ g : J.specialSubgroup,
      (omegaCenterIn (P : Subgroup J.specialSubgroup)).map (MulAut.conj g).toMonoidHom ≤
        ⨆ i, (omegaCenterIn (P : Subgroup J.specialSubgroup)).map
          (MulAut.conj (c i)).toMonoidHom := by
  let : CharP F 2 := charTwo_of_card hc
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hc hconj
  obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hc hf
  exact of_equiv (specialEquiv J C hC) (standard (standardForm J) rfl hn hc hconj) P

omit [CharP F 2] in
private theorem projection_omega (J : HermitianForm 3 F)
    (P : Sylow 2 J.specialSubgroup) :
    (omegaCenterIn (P : Subgroup J.specialSubgroup)).map J.specialToProjective =
      omegaCenterIn (P.mapSurjective J.specialToProjective_surjective :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let Q := P.mapSurjective J.specialToProjective_surjective
  let e := SylowOmega.specialSylowEquivProjective J P
  have he : (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype.comp e.toMonoidHom =
      J.specialToProjective.comp (P : Subgroup J.specialSubgroup).subtype := by
    apply MonoidHom.ext
    intro x
    exact SylowOmega.specialSylowEquivProjective_apply J P x
  have htop : (⊤ : Subgroup P).map e.toMonoidHom = ⊤ := map_top_of_surjective _ e.surjective
  have hw := NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective (⊤ : Subgroup P)
  have hm := congrArg (map (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype) hw
  rw [htop] at hm
  rw [Subgroup.map_map,he,←Subgroup.map_map] at hm
  rw [NilesRankOneKernel.omegaCenterIn_map_injective (P : Subgroup J.specialSubgroup).subtype (P : Subgroup J.specialSubgroup).subtype_injective,
    NilesRankOneKernel.omegaCenterIn_map_injective (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype_injective,
    ←MonoidHom.range_eq_map,range_subtype,←MonoidHom.range_eq_map,range_subtype] at hm
  exact hm


omit [CharP F 2] in
/-- The same normal-closure bound under the actual scalar projection to PSU₃. -/
theorem projective (J : HermitianForm 3 F) {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ c : Fin 3 → ProjectiveSpecialUnitaryMatrixGroup J,
      ∀ g : ProjectiveSpecialUnitaryMatrixGroup J,
      (omegaCenterIn (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).map
        (MulAut.conj g).toMonoidHom ≤
        ⨆ i, (omegaCenterIn (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).map
          (MulAut.conj (c i)).toMonoidHom := by
  obtain ⟨R,rfl⟩ := Sylow.mapSurjective_surjective J.specialToProjective_surjective 2 P
  obtain ⟨c,hc⟩ := special J hn hc hconj R
  refine ⟨fun i => J.specialToProjective (c i),?_⟩
  intro g
  obtain ⟨u,rfl⟩ := J.specialToProjective_surjective g
  have hm := map_mono (f := J.specialToProjective) (hc u)
  simpa only [Subgroup.map_iSup,map_conjugate,projection_omega] using hm

end BenderSuzuki.MatrixGroups.HermitianForm.ThreeOmegaNormalClosure
