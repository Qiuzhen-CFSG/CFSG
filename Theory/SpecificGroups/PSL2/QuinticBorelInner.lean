module
public import Theory.SpecificGroups.PSL2.BorelCoprimeFieldAction
public import Theory.FieldTheory.BinaryTorusTwoPower
public import Theory.FieldTheory.FiniteAutomorphismOrder
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Quintic displacements detect inner automorphisms of PSL₂(16)

A field automorphism of GF(16) fixing a multiplicative subgroup whose order
is divisible by five fixes the three-residual of the torus. The binary
torus theorem forces that field automorphism to be trivial. Projecting a
Borel to its torus therefore detects innerness from displacements on any
subgroup with order divisible by five; the whole torus need not be present.

Sylow conjugacy and a surjection with two-group kernel transport the
criterion while retaining the prescribed Sylow subgroup and the literal
automorphism action. The Chapter14 consumer applies it to the action of
O₂(H) on each exchanged component modulo its own two-core.
Source: Aschbacher--Smith 14.6.14(4)--15, printed pp.1033--1034;
the field-torus argument is also used in 13.8.20, printed p.954.
-/

public section
open Subgroup
open scoped MatrixGroups
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
namespace Theory.PSL2
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem field_eq_one_of_fixed_five_subgroup (hF : Nat.card F = 16)
    (σ : F ≃+* F) (D : Subgroup Fˣ) (hD : 5 ∣ Nat.card D)
    (hfix : ∀ u ∈ D, Units.map σ.toMonoidHom u = u) : σ = 1 := by
  have hcard : Nat.card Fˣ = 15 := by rw [Nat.card_units,hF]
  have hi : D.index ∣ 3 := by
    obtain ⟨k,hk⟩ := hD
    have hh := D.card_mul_index
    rw [hcard,hk] at hh
    have he : k * D.index = 3 := by nlinarith
    exact ⟨k,by nlinarith⟩
  have hp : IsPGroup 3 (Fˣ ⧸ D) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    simpa only [index_eq_card,pow_one] using hi
  have hr : pResidual 3 Fˣ ≤ D := sInf_le ⟨inferInstance,hp⟩
  have hσ : σ ^ (2^2) = 1 := by
    have hh := pow_card_eq_one' (x := σ)
    rwa [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card F = 2^4 by simpa using hF)] at hh
  exact FiniteField.BinaryTorusTwoPower.eq_one_of_fixed_residual
    (show Nat.card F = 2^4 by simpa using hF) (by decide) (by decide) σ hσ
    (fun u hu => hfix u (hr hu))

/-- Five in a preserved Borel subgroup detects the entire field factor over GF(16). -/
theorem inner_of_quintic_borel_displacements (hF : Nat.card F = 16)
    (B : Subgroup PSL(2,F)) (hB : B ≤ borel F) (hfive : 5 ∣ Nat.card B)
    (α : MulAut PSL(2,F)) (hU : (kernel F).map α.toMonoidHom = kernel F)
    (hdisp : ∀ x ∈ B, x⁻¹ * α x ∈ kernel F) :
    α ∈ MulAut.innerSubgroup PSL(2,F) := by
  obtain ⟨g,σ,he⟩ := exists_inner_field F α
  have hg : g ∈ borel F := inner_factor_mem_borel F g σ (he ▸ hU)
  let f : B →* Fˣ := (torusProjection F).comp (inclusion hB)
  have hker : IsPGroup 2 f.ker := by
    have hfker : f.ker ≤ (kernel F).subgroupOf B := by
      intro x hx
      exact (torusProjection_eq_one_iff F (inclusion hB x)).mp hx
    have hP : IsPGroup 2 (kernel F) :=
      (coe_standardSylow F) ▸ (standardSylow F).isPGroup'
    exact (hP.comap_of_injective B.subtype B.subtype_injective).to_le hfker
  have h5 : 5 ∣ Nat.card f.range := by
    obtain ⟨n,hn⟩ := hker.exists_card_eq
    rw [←f.ker.card_mul_index,index_ker,hn] at hfive
    exact (((by decide : Nat.Coprime 5 2).pow_right n).dvd_of_dvd_mul_left hfive)
  have hs : σ = 1 := field_eq_one_of_fixed_five_subgroup hF σ f.range h5 (by
    rintro _ ⟨x,rfl⟩
    apply (borelActor_commutator_mem_core_iff F
      (show Nat.card F = 2^4 by simpa using hF) ⟨g,hg⟩ σ (inclusion hB x)).mp
    rw [twoCoreIn_eq_kernel F (show Nat.card F = 2^4 by simpa using hF)]
    rw [←he]
    exact hdisp x x.property)
  rw [he,hs]
  have hf : Atlas.fieldEquivPSL 2 (1 : F ≃+* F) = 1 :=
    (Atlas.RankOneFieldAutomorphisms.pslFieldAction (F := F)).map_one
  rw [hf,mul_one]
  exact ⟨g,rfl⟩
/-- The same detector retains an arbitrary marked Sylow subgroup. -/
theorem inner_of_quintic_sylow_displacements (hF : Nat.card F = 16)
    (P : Sylow 2 PSL(2,F)) (B : Subgroup PSL(2,F))
    (hB : B ≤ normalizer (P : Set PSL(2,F))) (hfive : 5 ∣ Nat.card B)
    (α : MulAut PSL(2,F)) (hP : (P : Subgroup PSL(2,F)).map α.toMonoidHom = P)
    (hdisp : ∀ x ∈ B, x⁻¹ * α x ∈ (P : Subgroup PSL(2,F))) :
    α ∈ MulAut.innerSubgroup PSL(2,F) := by
  obtain ⟨c,hcU,hcB⟩ := sylow_normalizer_conjugate F P
  let e := MulAut.conj c
  let B' := B.map e.symm.toMonoidHom
  let β := MulAut.congr e.symm α
  have hB' : B' ≤ borel F := by
    rw [←map_symm_eq_iff_map_eq (borel F) (e := e) |>.mpr hcB]
    exact map_mono hB
  have h5' : 5 ∣ Nat.card B' := by
    rw [card_map_of_injective e.symm.injective]
    exact hfive
  have hU : (kernel F).map β.toMonoidHom = kernel F := by
    calc
      _ = (((kernel F).map e.toMonoidHom).map α.toMonoidHom).map e.symm.toMonoidHom := by
        rw [Subgroup.map_map,Subgroup.map_map]
        rfl
      _ = (P : Subgroup PSL(2,F)).map e.symm.toMonoidHom := by rw [hcU,hP]
      _ = kernel F := (map_symm_eq_iff_map_eq (kernel F) (e := e)).mpr hcU
  have hd : ∀ x ∈ B', x⁻¹ * β x ∈ kernel F := by
    rintro _ ⟨x,hx,rfl⟩
    have hh := mem_map_of_mem e.symm.toMonoidHom (hdisp x hx)
    have heP : (P : Subgroup PSL(2,F)).map e.symm.toMonoidHom = kernel F :=
      (map_symm_eq_iff_map_eq (kernel F) (e := e)).mpr hcU
    rw [heP] at hh
    change (e.symm x)⁻¹ * e.symm (α (e (e.symm x))) ∈ kernel F
    rw [e.apply_symm_apply]
    simpa only [map_mul,map_inv,MulEquiv.coe_toMonoidHom] using hh
  obtain ⟨z,hz⟩ := inner_of_quintic_borel_displacements hF B' hB' h5' β hU hd
  refine ⟨e z,?_⟩
  have hh := congrArg (MulAut.congr e) hz
  rw [MulAut.congr_conj] at hh
  exact hh.trans (by ext x; simp [β,MulAut.congr_apply])

/-- Transport the detector through a surjection with two-group kernel. -/
theorem inner_of_quintic_cover_displacements {A : Type*} [_root_.Group A] [Finite A]
    (hF : Nat.card F = 16) (q : A →* PSL(2,F)) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (P : Sylow 2 A) (B : Subgroup A)
    (hB : B ≤ normalizer (P : Set A)) (hfive : 5 ∣ Nat.card B)
    (α : MulAut A) (β : MulAut PSL(2,F)) (he : ∀ x, q (α x) = β (q x))
    (hP : (P : Subgroup A).map α.toMonoidHom = P)
    (hdisp : ∀ x ∈ B, x⁻¹ * α x ∈ (P : Subgroup A)) :
    β ∈ MulAut.innerSubgroup PSL(2,F) := by
  let P' := P.mapSurjective (f := q) hq
  have hn : B.map q ≤ normalizer (P' : Set PSL(2,F)) :=
    (map_mono hB).trans (le_normalizer_map q)
  have h5 : 5 ∣ Nat.card (B.map q) := by
    let f := q.comp B.subtype
    have hf : IsPGroup 2 f.ker :=
      hk.comap_of_injective B.subtype B.subtype_injective
    obtain ⟨n,hn⟩ := hf.exists_card_eq
    rw [←f.ker.card_mul_index,index_ker,hn] at hfive
    have hh := (((by decide : Nat.Coprime 5 2).pow_right n).dvd_of_dvd_mul_left hfive)
    have hr : f.range = B.map q := by rw [MonoidHom.range_comp,range_subtype]
    rwa [hr] at hh
  have hP' : (P' : Subgroup PSL(2,F)).map β.toMonoidHom = P' := by
    change ((P : Subgroup A).map q).map β.toMonoidHom = (P : Subgroup A).map q
    have hc : β.toMonoidHom.comp q = q.comp α.toMonoidHom :=
      MonoidHom.ext (fun x => (he x).symm)
    rw [map_map,hc,←map_map,hP]
  apply inner_of_quintic_sylow_displacements hF P' (B.map q) hn h5 β hP'
  rintro _ ⟨x,hx,rfl⟩
  rw [←he,←map_inv,←map_mul]
  exact mem_map_of_mem q (hdisp x hx)

end Theory.PSL2
