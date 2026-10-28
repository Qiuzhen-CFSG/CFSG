module

public import Theory.SpecificGroups.Suzuki.RootOmega
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.EquivariantOffender
import Mathlib.Tactic

/-!
# The natural Suzuki matrix action in characteristic two

In the standard Sylow subgroup, all square-one matrices are u(0,b).
For b nonzero the fixed space is the plane with last two coordinates zero.
Every displacement by a central root element lies in that plane, proving
quadraticity. Sylow conjugacy transports the calculation to every nontrivial
elementary abelian subgroup and every Sylow omega subgroup.

The representation is the literal GL matrix action restricted to the concrete
Suzuki subgroup and then to F₂. No recognition or dimension premise is used.
Source: Huppert–Blackburn, Finite Groups III, XI.3.1 and XI.3.3;
Aschbacher–Smith, K.3.6, printed p.457 (1 March 2004 manuscript).
-/

@[expose] public section
open BenderSuzuki BenderSuzuki.MatrixGroups PFAppendixIII Subgroup
open Representation.BinaryOffender
namespace Representation.SuzukiNatural
noncomputable section
abbrev F (m : ℕ) := BinaryGaloisField (2 * m + 1)
abbrev W (m : ℕ) := Fin 4 → F m

def natural (m : ℕ) : Representation (ZMod 2) (SuzukiMatrixGroup m) (W m) :=
  Representation.restrictScalars ((generalLinearNatural 4).comp (SuzukiMatrixSubgroup m).subtype)

theorem natural_apply (m : ℕ) (g : SuzukiMatrixGroup m) (v : W m) :
    natural m g v = Matrix.mulVec g.val.val v := rfl

private def centralRoot (m : ℕ) (b : F m) : SuzukiMatrixGroup m :=
  ⟨SuzukiRootGL m 0 b, subset_closure (Or.inl ⟨0, b, rfl⟩)⟩

private theorem centralRoot_action (m : ℕ) (b : F m) (v : W m) :
    natural m (centralRoot m b) v =
      ![v 0 + b * v 2 + b ^ (2 ^ (m + 1)) * v 3, v 1 + b * v 3, v 2, v 3] := by
  ext i
  fin_cases i <;>
    simp [natural_apply, centralRoot, SuzukiRootGL, SuzukiRootMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, add_assoc]

private theorem centralRoot_square (m : ℕ) (b : F m) : (centralRoot m b) ^ 2 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centralRoot, pow_two, SuzukiRootGL, SuzukiRootMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, CharTwo.add_self_eq_zero]

private theorem centralRoot_mem_omega (m : ℕ) (b : F m) :
    centralRoot m b ∈ omegaOneAmbient (SuzukiRootSubgroup m) := by
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl _ _ (centralRoot_square m b)
  exact (mem_suzukiRootSubgroup_iff _ _).mpr ⟨0, b, rfl⟩

private theorem centralRoot_ne_one {m : ℕ} {b : F m} (hb : b ≠ 0) : centralRoot m b ≠ 1 := by
  intro he
  have h := congrArg (fun g : SuzukiMatrixGroup m => g.val.val 0 2) he
  exact hb (by simpa [centralRoot, SuzukiRootGL, SuzukiRootMatrix] using h)

private theorem omega_coordinates {m : ℕ} (hm : 0 < m) {x : SuzukiMatrixGroup m}
    (hx : x ∈ omegaOneAmbient (SuzukiRootSubgroup m)) : ∃ b, x = centralRoot m b := by
  obtain ⟨a, b, he⟩ := (mem_suzukiRootSubgroup_iff m x).mp (omegaOneAmbient_le _ hx)
  let := suzukiRootSubgroup_omega_elementary m hm
  have hs : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hh := congrArg (fun y : SuzukiMatrixGroup m => y.val (0 : Fin 4) (2 : Fin 4)) hs
  have hab : a * a ^ (2 ^ (m + 1)) = 0 := by
    have hc : b + (a * a ^ (2 ^ (m + 1)) + b) = 0 := by
      simpa [pow_two, he, SuzukiRootGL, SuzukiRootMatrix,
        Matrix.mul_apply, Fin.sum_univ_four, add_assoc] using hh
    have hd : b + (a * a ^ (2 ^ (m + 1)) + b) = a * a ^ (2 ^ (m + 1)) := by
      rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    rwa [hd] at hc
  have ha : a = 0 := (mul_eq_zero.mp hab).elim id eq_zero_of_pow_eq_zero
  refine ⟨b, Subtype.ext ?_⟩
  simpa only [ha, centralRoot] using he

private def fixedPlane (m : ℕ) : Submodule (ZMod 2) (W m) where
  carrier := {v | v 2 = 0 ∧ v 3 = 0}
  zero_mem' := ⟨rfl, rfl⟩
  add_mem' := by rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩; exact ⟨by simp [hx, hy], by simp [hx', hy']⟩
  smul_mem' := by rintro c x ⟨hx, hx'⟩; exact ⟨by simp [hx], by simp [hx']⟩

private def fixedPlaneEquiv (m : ℕ) : fixedPlane m ≃ₗ[ZMod 2] (Fin 2 → F m) where
  toFun v := ![v.val 0, v.val 1]
  invFun v := ⟨![v 0, v 1, 0, 0], by simp [fixedPlane]⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [v.property.1, v.property.2]
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> rfl

private theorem fixedPlane_finrank (m : ℕ) :
    Module.finrank (ZMod 2) (fixedPlane m) = 2 * (2 * m + 1) := by
  rw [(fixedPlaneEquiv m).finrank_eq, Module.finrank_pi_fintype]
  simp [F, GaloisField.finrank 2 (by omega : 2 * m + 1 ≠ 0)]

theorem natural_finrank (m : ℕ) : Module.finrank (ZMod 2) (W m) = 4 * (2 * m + 1) := by
  rw [Module.finrank_pi_fintype]
  simp [F, GaloisField.finrank 2 (by omega : 2 * m + 1 ≠ 0)]

private theorem centralRoot_fixed_iff {m : ℕ} {b : F m} (hb : b ≠ 0) (v : W m) :
    natural m (centralRoot m b) v = v ↔ v ∈ fixedPlane m := by
  rw [centralRoot_action]
  constructor
  · intro he
    have h1 := congrFun he 1
    have h0 := congrFun he 0
    have hv3 : v 3 = 0 := by
      have ht : b * v 3 = 0 := by simpa using (add_eq_left.mp h1)
      exact (mul_eq_zero.mp ht).resolve_left hb
    have hv2 : v 2 = 0 := by
      have ht : b * v 2 = 0 := by simpa [hv3] using h0
      exact (mul_eq_zero.mp ht).resolve_left hb
    exact ⟨hv2, hv3⟩
  · rintro ⟨hv2, hv3⟩
    ext i
    fin_cases i <;> simp [hv2, hv3]

private theorem centralRoot_fixes_plane (m : ℕ) (b : F m) {v : W m} (hv : v ∈ fixedPlane m) :
    natural m (centralRoot m b) v = v := by
  rw [centralRoot_action]
  ext i
  fin_cases i <;> simp [hv.1, hv.2]

private theorem centralRoot_displacement_mem (m : ℕ) (b : F m) (v : W m) :
    natural m (centralRoot m b) v - v ∈ fixedPlane m := by
  rw [centralRoot_action]
  constructor <;> simp

private theorem omega_quadratic {m : ℕ} (hm : 0 < m) :
    IsQuadratic (natural m) (omegaOneAmbient (SuzukiRootSubgroup m)) := by
  intro a ha b hb v
  obtain ⟨c, rfl⟩ := omega_coordinates hm ha
  obtain ⟨d, rfl⟩ := omega_coordinates hm hb
  exact centralRoot_fixes_plane m c (centralRoot_displacement_mem m d v)

private theorem fixedSpace_eq_plane {m : ℕ} (hm : 0 < m) {A : Subgroup (SuzukiMatrixGroup m)}
    (hA : A ≠ ⊥) (hle : A ≤ omegaOneAmbient (SuzukiRootSubgroup m)) :
    fixedSpace (natural m) A = fixedPlane m := by
  obtain ⟨a, ha, hne⟩ := A.bot_or_exists_ne_one.resolve_left hA
  obtain ⟨b, rfl⟩ := omega_coordinates hm (hle ha)
  have hb : b ≠ 0 := by
    intro hb
    apply hne
    apply Subtype.ext
    exact hb ▸ External.suzukiRootGL_zero_zero m
  ext v
  constructor
  · intro hv
    exact (centralRoot_fixed_iff hb v).mp (hv ⟨_, ha⟩)
  · intro hv a
    obtain ⟨c, hc⟩ := omega_coordinates hm (hle a.property)
    change natural m (a : SuzukiMatrixGroup m) v = v
    rw [hc]
    exact centralRoot_fixes_plane m c hv

private theorem fixedCodim_eq_of_le_omega {m : ℕ} (hm : 0 < m) {A : Subgroup (SuzukiMatrixGroup m)}
    (hA : A ≠ ⊥) (hle : A ≤ omegaOneAmbient (SuzukiRootSubgroup m)) :
    fixedCodim (natural m) A = 2 * (2 * m + 1) := by
  have hdim := fixedCodim_add_finrank (natural m) A
  rw [fixedSpace_eq_plane hm hA hle, fixedPlane_finrank, natural_finrank] at hdim
  omega

theorem elementary_fixedCodim {m : ℕ} (hm : 0 < m) {A : Subgroup (SuzukiMatrixGroup m)}
    (hA : IsElementaryTwo A) : fixedCodim (natural m) A = 2 * (2 * m + 1) := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨U, hU⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) P U
  have hP : (P : Subgroup (SuzukiMatrixGroup m)).map (MulAut.conj g).toMonoidHom =
      SuzukiRootSubgroup m := (congrArg Sylow.toSubgroup hg).trans hU
  have hAg := hA.map_conj g
  let : IsElementaryAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := hAg.2
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ omegaOneAmbient (SuzukiRootSubgroup m) := by
    intro a ha
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl a
      (hP ▸ map_mono hAP ha) (elemPow_eq_one_of_isElementaryAbelian a ha)
  rw [← fixedCodim_map_conj (natural m) A g]
  exact fixedCodim_eq_of_le_omega hm hAg.1 hle

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

theorem sylow_omega_quadratic {m : ℕ} (hm : 0 < m) (P : Sylow 2 (SuzukiMatrixGroup m)) :
    IsQuadratic (natural m) (omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup m))) := by
  obtain ⟨U, hU⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) U P
  have hP : (SuzukiRootSubgroup m).map (MulAut.conj g).toMonoidHom =
      (P : Subgroup (SuzukiMatrixGroup m)) := by
    have hh := congrArg Sylow.toSubgroup hg
    change (U : Subgroup (SuzukiMatrixGroup m)).map (MulAut.conj g).toMonoidHom = _ at hh
    rwa [hU] at hh
  rw [← hP, ← map_omegaOneAmbient_injective _ (MulAut.conj g).injective]
  exact quadratic_map_conj (omega_quadratic hm) g

end
end Representation.SuzukiNatural
