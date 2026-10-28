module

public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Frattini.OmegaProducts
import Mathlib.Tactic

/-!
# The natural binary SU₃ action and its inner elementary actors

The square-one Hermitian root matrices have zero first root coordinate.
Their natural action is v ↦ (v₀+b v₂,v₁,v₂), so all nonidentity elements
fix the same field plane and their displacements are fixed by the whole
central root group. Sylow conjugacy gives codimension 2s for every
nontrivial elementary subgroup and quadraticity for every Sylow omega.
The argument uses the full special-unitary carrier, including its cubic center.

Source: Huppert II.10.12; Aschbacher–Smith, K.3.3, printed p.456,
combined manuscript of 1 March 2004.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups BenderSuzuki.External Subgroup
open Representation.BinaryOffender
namespace Representation.SU3.NaturalMatrix
open HermitianForm HermitianForm.BorelTorus HermitianForm.BorelTorus.EvenCenterAction
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]
  (J : HermitianForm 3 F)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private instance : CharP F 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2

noncomputable def natural : Representation (ZMod 2) J.specialSubgroup (Fin 3 → F) :=
  Representation.restrictScalars ((generalLinearNatural 3).comp J.specialSubgroup.subtype)

theorem natural_apply (g : J.specialSubgroup) (v : Fin 3 → F) :
    natural J g v = Matrix.mulVec g.val.val v := rfl

omit [Algebra (ZMod 2) F] in
private theorem rootSU_injective : Function.Injective (hermitianUnipotentSU J hJ) := by
  intro z w h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun x : J.specialSubgroup => x.val.val 0 1) h)
    (congrArg (fun x : J.specialSubgroup => x.val.val 0 2) h)

private def centralRoot (b : fixedField J) : J.specialSubgroup :=
  hermitianUnipotentSU J hJ (centralCoord J (.ofAdd b))

private theorem centralRoot_action (b : fixedField J) (v : Fin 3 → F) :
    natural J (centralRoot J hJ b) v = ![v 0 + (b : F) * v 2, v 1, v 2] := by
  change Matrix.mulVec !![1,0,(b : F);0,1,-J.conj 0;0,0,1] v = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem centralRoot_zero : centralRoot J hJ 0 = 1 := by
  exact (hermitianUnipotentSU J hJ).map_one

private theorem omega_coordinates {x : J.specialSubgroup}
    (hx : x ∈ omegaOneAmbient (specialRoot J hJ)) : ∃ b, x = centralRoot J hJ b := by
  have hle : omegaOneAmbient (specialRoot J hJ) ≤
      ((hermitianUnipotentSU J hJ).comp (centralCoord J)).range := by
    apply (omegaOneAmbient_le_iff _ _).mpr
    rintro _ ⟨z, rfl⟩ hz
    have hsq : z ^ 2 = 1 := rootSU_injective J hJ (by simpa only [map_pow, map_one] using hz)
    have hfirst := (EvenSemilinear.square_eq_one_iff_first_zero J z).mp hsq
    have hb : J.conj z.val.2 = z.val.2 := by
      have hp := z.property
      rw [hfirst, zero_mul, add_zero] at hp
      exact (eq_neg_of_add_eq_zero_right hp).trans (CharTwo.neg_eq _)
    refine ⟨.ofAdd ⟨z.val.2, hb⟩, ?_⟩
    apply congrArg (hermitianUnipotentSU J hJ)
    exact Subtype.ext (Prod.ext hfirst.symm rfl)
  obtain ⟨b, hb⟩ := hle hx
  exact ⟨b.toAdd, hb.symm⟩

private def fixedPlane : Submodule (ZMod 2) (Fin 3 → F) where
  carrier := {v | v 2 = 0}
  zero_mem' := rfl
  add_mem' := by intro x y hx hy; simp_all
  smul_mem' := by intro c x hx; simp_all

private def fixedPlaneEquiv : fixedPlane (F := F) ≃ₗ[ZMod 2] (Fin 2 → F) where
  toFun v := ![v.val 0, v.val 1]
  invFun v := ⟨![v 0, v 1, 0], rfl⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact v.property.symm
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> rfl

private theorem centralRoot_fixed_iff {b : fixedField J} (hb : b ≠ 0) (v : Fin 3 → F) :
    natural J (centralRoot J hJ b) v = v ↔ v ∈ fixedPlane (F := F) := by
  rw [centralRoot_action]
  constructor
  · intro he
    have h0 := congrFun he 0
    have ht : (b : F) * v 2 = 0 := by simpa using (add_eq_left.mp h0)
    exact (mul_eq_zero.mp ht).resolve_left (fun h => hb (Subtype.ext h))
  · intro hv
    change v 2 = 0 at hv
    ext i
    fin_cases i <;> simp [hv]

private theorem centralRoot_fixes_plane (b : fixedField J) {v : Fin 3 → F}
    (hv : v ∈ fixedPlane (F := F)) : natural J (centralRoot J hJ b) v = v := by
  rw [centralRoot_action]
  change v 2 = 0 at hv
  ext i
  fin_cases i <;> simp [hv]

private theorem centralRoot_displacement_mem (b : fixedField J) (v : Fin 3 → F) :
    natural J (centralRoot J hJ b) v - v ∈ fixedPlane (F := F) := by
  rw [centralRoot_action]
  change v 2 - v 2 = 0
  exact sub_self _

theorem root_omega_quadratic : IsQuadratic (natural J) (omegaOneAmbient (specialRoot J hJ)) := by
  intro a ha b hb v
  obtain ⟨c, rfl⟩ := omega_coordinates J hJ ha
  obtain ⟨d, rfl⟩ := omega_coordinates J hJ hb
  exact centralRoot_fixes_plane J hJ c (centralRoot_displacement_mem J hJ d v)

private theorem fixedSpace_eq_plane {A : Subgroup J.specialSubgroup}
    (hA : A ≠ ⊥) (hle : A ≤ omegaOneAmbient (specialRoot J hJ)) :
    fixedSpace (natural J) A = fixedPlane (F := F) := by
  obtain ⟨a, ha, hne⟩ := A.bot_or_exists_ne_one.resolve_left hA
  obtain ⟨b, rfl⟩ := omega_coordinates J hJ (hle ha)
  have hb : b ≠ 0 := by
    intro hb
    exact hne (hb ▸ centralRoot_zero J hJ)
  ext v
  constructor
  · intro hv
    exact (centralRoot_fixed_iff J hJ hb v).mp (hv ⟨_, ha⟩)
  · intro hv a
    obtain ⟨c, hc⟩ := omega_coordinates J hJ (hle a.property)
    change natural J (a : J.specialSubgroup) v = v
    rw [hc]
    exact centralRoot_fixes_plane J hJ c hv

variable [Finite F]

theorem field_finrank {s : ℕ} (hcard : Nat.card F = (2 ^ s) ^ 2) :
    Module.finrank (ZMod 2) F = 2 * s := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [Nat.card_zmod, hcard, ← pow_mul] at hc
  exact ((Nat.pow_right_injective (by decide : 2 ≤ 2)) hc).symm.trans (Nat.mul_comm _ _)

private theorem fixedCodim_eq_of_le_omega {s : ℕ} (hcard : Nat.card F = (2 ^ s) ^ 2)
    {A : Subgroup J.specialSubgroup} (hA : A ≠ ⊥)
    (hle : A ≤ omegaOneAmbient (specialRoot J hJ)) : fixedCodim (natural J) A = 2 * s := by
  have hd := fixedCodim_add_finrank (natural J) A
  rw [fixedSpace_eq_plane J hJ hA hle, (fixedPlaneEquiv (F := F)).finrank_eq,
    Module.finrank_pi_fintype, Module.finrank_pi_fintype, field_finrank hcard] at hd
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hd
  omega

omit [Algebra (ZMod 2) F] in
/-- The literal special root subgroup is Sylow, retaining its scalar projection. -/
theorem special_root_sylow {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ s) :
    ∃ S : Sylow 2 J.specialSubgroup, (S : Subgroup J.specialSubgroup) = specialRoot J hJ := by
  let R := EvenTwoRank.rootSylow J hJ (by omega : 0 < s) hcard hfixed
  let ec := SylowOmega.projectiveSylowEquivCoords J hs hcard hfixed hJ R
  let es : hermitianUnipotentCoord J ≃* specialRoot J hJ :=
    MonoidHom.ofInjective (rootSU_injective J hJ)
  have hp : IsPGroup 2 (specialRoot J hJ) := (R.isPGroup'.of_equiv ec).of_equiv es
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hc : Nat.card S = Nat.card (specialRoot J hJ) :=
    Nat.card_congr (((SylowOmega.specialSylowEquivProjective J S).trans
      (SylowOmega.projectiveSylowEquivCoords J hs hcard hfixed hJ _)).trans es).toEquiv
  exact ⟨S, (eq_of_le_of_card_ge hS hc.le).symm⟩

include hJ in
/-- All nontrivial elementary two-subgroups of SU₃ have natural codimension 2s. -/
theorem elementary_fixedCodim {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ s)
    {A : Subgroup J.specialSubgroup} (hA : IsElementaryTwo A) :
    fixedCodim (natural J) A = 2 * s := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨U, hU⟩ := special_root_sylow J hJ hs hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J.specialSubgroup P U
  have hP : (P : Subgroup J.specialSubgroup).map (MulAut.conj g).toMonoidHom =
      specialRoot J hJ := (congrArg Sylow.toSubgroup hg).trans hU
  have hAg := hA.map_conj g
  let : IsElementaryAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := hAg.2
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ omegaOneAmbient (specialRoot J hJ) := by
    rw [← omegaOneAmbient_eq_self (A.map (MulAut.conj g).toMonoidHom)]
    exact omegaOneAmbient_mono (hP ▸ map_mono hAP)
  rw [← fixedCodim_map_conj (natural J) A g]
  exact fixedCodim_eq_of_le_omega J hJ hcard hAg.1 hle

private theorem quadratic_map_conj {H V : Type*} [Group H]
    [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) H V}
    {A : Subgroup H} (hA : IsQuadratic ρ A) (g : H) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  have hinv (v : V) : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
  have h := congrArg (ρ g) (hA a ha b hb (ρ g⁻¹ v))
  have hginv (v : V) : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  simpa only [map_mul, Module.End.mul_apply, map_sub, hinv, hginv] using h

include hJ in
/-- Every special-unitary Sylow omega is quadratic on the natural module. -/
theorem sylow_omega_quadratic {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ s)
    (P : Sylow 2 J.specialSubgroup) :
    IsQuadratic (natural J) (omegaOneAmbient (P : Subgroup J.specialSubgroup)) := by
  obtain ⟨U, hU⟩ := special_root_sylow J hJ hs hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J.specialSubgroup U P
  have hP : (specialRoot J hJ).map (MulAut.conj g).toMonoidHom =
      (P : Subgroup J.specialSubgroup) := by
    have hh := congrArg Sylow.toSubgroup hg
    change (U : Subgroup J.specialSubgroup).map (MulAut.conj g).toMonoidHom = _ at hh
    rwa [hU] at hh
  rw [← hP, ← map_omegaOneAmbient_injective _ (MulAut.conj g).injective]
  exact quadratic_map_conj (root_omega_quadratic J hJ) g

end Representation.SU3.NaturalMatrix
