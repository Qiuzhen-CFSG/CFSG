module
public import Theory.SpecificGroups.SU3.SylowQuadraticInner
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms
public import Theory.GroupTheory.CenterlessSupplementCentralizer
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.PGroupCore
public import BenderSuzuki.External.Huppert.II.theorem_10_13

/-!
# Elementary normal Sylow subgroups in unitary extensions

For an elementary V normal in T, its conjugation on the Sylow intersection
with the normal unitary supplement has square-one displacements. The concrete
Hermitian actor detector makes this action inner. Trivial O₂(H) kills the
centralizer of the centerless Sylow supplement, so V lies in K. The root
omega calculation places it in the center of the same Sylow intersection.

Source: Aschbacher–Smith E.2.7, printed p.218, normal unitary Bender case.
No semilinear, innerness, placement or witness conclusion is an input.
-/

public section
open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.SylowQuadraticInner
open Subgroup
variable {H E : Type*} [Group H] [Finite H] [Field E] [Finite E] [CharP E 2]

theorem normal_elementary_placement
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x : E, J.conj x = x^(2^n))
    (K : Subgroup H) [K.Normal] (e : K ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (T : Sylow 2 H) (hgen : K ⊔ (T : Subgroup H) = ⊤) (hcore : pCore 2 H = ⊥)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal) :
    V ≤ K ∧ ∃ S : Sylow 2 K, (S : Subgroup K) = (T : Subgroup H).subgroupOf K ∧
      V.subgroupOf K ≤ (center S).map (S : Subgroup K).subtype := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have hnonfixed : ∃ x : E, J.conj x ≠ x := by
    by_contra! h
    apply conj_ne_one_of_card J n (by omega) hcard hfixed
    exact RingEquiv.ext h
  have hZmodel := EvenTwoRank.standard_center_eq_bot J hJ hnonfixed
  have hZ : center K = ⊥ := by
    apply (center K).eq_bot_iff_forall.mpr
    intro x hx
    have hh : e x ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) := (centerCongr e ⟨x,hx⟩).property
    rw [hZmodel,mem_bot] at hh
    exact e.injective (hh.trans e.map_one.symm)
  have hC : centralizer (K : Set H) = ⊥ := by
    have hCT := centralizer_le_sylow_of_centerless_supplement K T hgen hZ
    have hCp : centralizer (K : Set H) ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,T.isPGroup'.to_le hCT⟩
    exact le_bot_iff.mp (hCp.trans hcore.le)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J (2^n)
      (lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hn)) hcard hfixed
  have hnorm : (T : Subgroup H) ≤ normalizer (V : Set H) :=
    (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_normal K
  have hVK : V ≤ K := by
    intro v hv
    let a : MulAut K := MulAut.conjNormal v
    have hvT : v ∈ T := hVT hv
    have ha : a^2 = 1 := by
      change (MulAut.conjNormal v : MulAut K)^2 = 1
      rw [←map_pow,elemPow_eq_one_of_isElementaryAbelian v hv,map_one]
    have haS : (S : Subgroup K).map a.toMonoidHom = S := by
      apply eq_of_le_of_card_ge
      · rintro _ ⟨x,hx,rfl⟩
        rw [hS] at hx ⊢
        exact (T : Subgroup H).mul_mem ((T : Subgroup H).mul_mem hvT hx)
          ((T : Subgroup H).inv_mem hvT)
      · rw [card_map_of_injective (f := a.toMonoidHom) (K := (S : Subgroup K)) a.injective]
    have hfix : ∀x ∈ S, (x⁻¹ * a x)^2 = 1 := by
      intro x hx
      have hxT : (x : H) ∈ T := hS.le hx
      have hd : (x : H)⁻¹ * v * (x : H) * v⁻¹ ∈ V :=
        V.mul_mem (by
          simpa only [inv_inv] using (le_normalizer_iff.mp hnorm)
            (x : H)⁻¹ ((T : Subgroup H).inv_mem hxT) v hv) (V.inv_mem hv)
      apply Subtype.ext
      change ((x : H)⁻¹ * (v * (x : H) * v⁻¹))^2 = 1
      simpa only [mul_assoc] using elemPow_eq_one_of_isElementaryAbelian _ hd
    let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let b := MulAut.congr e a
    have hb : b^2 = 1 := by change (MulAut.congr e a)^2 = 1; rw [←map_pow,ha,map_one]
    have hbS : (Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map b.toMonoidHom = Q := by
      change ((S : Subgroup K).map e.toMonoidHom).map b.toMonoidHom = _
      have hh : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        change e (a (e.symm (e x))) = e (a x)
        rw [e.symm_apply_apply]
      rw [Subgroup.map_map,hh,←Subgroup.map_map,haS]
      rfl
    have hbfix : ∀x ∈ Q, (x⁻¹ * b x)^2 = 1 := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := hx
      change ((e y)⁻¹ * e (a (e.symm (e y))))^2 = 1
      rw [e.symm_apply_apply,←map_inv,←map_mul,←map_pow,hfix y hy,map_one]
    obtain ⟨g,hg⟩ := involutive_sylow_displacement_inner J hJ hn hcard hconj Q b hb hbS hbfix
    have hi : a = MulAut.conj (e.symm g) := by
      apply (MulAut.congr e).injective
      rw [MulAut.congr_conj,e.apply_symm_apply]
      exact hg
    have hin : v ∈ (MulAut.innerSubgroup K).comap MulAut.conjNormal := ⟨e.symm g,hi.symm⟩
    rw [MulAut.conjNormal_comap_innerSubgroup,hC,sup_bot_eq] at hin
    exact hin
  refine ⟨hVK,S,hS,?_⟩
  let : IsElementaryAbelian 2 (V.subgroupOf K) := IsElementaryAbelian.subgroupOf hVK
  rw [← (SylowOmega.omega_of_projective_equiv J hn hcard hfixed hJ e S).1,
    ←omegaOneAmbient_eq_self (V.subgroupOf K)]
  apply omegaOneAmbient_mono
  rw [hS]
  exact comap_mono hVT
end BenderSuzuki.MatrixGroups.HermitianForm.SylowQuadraticInner
