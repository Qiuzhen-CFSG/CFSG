module
public import Theory.SpecificGroups.PSL2.SemilinearCoverage
public import Theory.SpecificGroups.SL2.EvenBorelResidual.Semilinear
public import Theory.GroupAction.QuadraticFieldQuotient
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Quadratic actions on the actual binary PSL₂ split complement

A root-preserving automorphism of PSL₂ over a finite field of characteristic
two acts on the Borel quotient by its field coefficient. If its action on
a preserved complement is quadratic, the field automorphism is trivial.
The complement embeds into the unit quotient, so it is fixed pointwise.
Write the remaining inner actor as a root element times an element of the
same complement. The root element centralizes both the root subgroup and
the complement, hence the Borel; its fixed-point-free standard torus forces
it to be the identity. Thus the implementer lies in the original complement.

Sylow conjugacy and carrier transport retain the prescribed root subgroup
and complement. This includes the source's smallest field of order four.
No order hypothesis is needed on the actor once the root is preserved.
Source: Aschbacher--Smith 2.4.8(5), pp.529--530; the quadratic field calculation
is also used in F.1.3(5), p.260. The initial semilinear argument is extracted
from ChapterF.SourceCartan.LinearSuzuki.Linear into the reusable Theory layer.
-/
public section
open scoped MatrixGroups Pointwise
open Subgroup Atlas
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
namespace Theory.PSL2.QuadraticTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem coefficient_action_eq (σ : F ≃+* F) :
    Theory.PSL2.fieldAut σ = Atlas.fieldEquivPSL 2 σ := by
  ext x
  obtain ⟨g, rfl⟩ := Theory.PSL2.quotientMap_surjective F x
  rw [Theory.PSL2.fieldAut_apply_quotientMap]
  change _ = Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ g)
  rw [Atlas.fieldEquivPSL_mk]
  rfl

private theorem coverage (a : MulAut PSL(2,F)) :
    ∃ (g : PSL(2,F)) (σ : F ≃+* F), a = MulAut.conj g * fieldEquivPSL 2 σ := by
  obtain ⟨g, σ, ha⟩ := Theory.PSL2.semilinear_coverage a
  exact ⟨g, σ, coefficient_action_eq σ ▸ ha⟩

private theorem kernel_inf_centralizer_borel (hlarge : 2 < Nat.card F) :
    kernel F ⊓ centralizer (borel F : Set PSL(2,F)) = ⊥ := by
  have hcard : 1 < Nat.card (complement F) := by
    rw [← Nat.card_congr (torusEquiv F).toEquiv, Nat.card_units]
    omega
  let : Nontrivial (complement F) := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨c, hc⟩ := exists_ne (1 : complement F)
  apply eq_bot_iff.mpr
  intro p hp
  apply mem_bot.mpr
  have he : (⟨p, hp.1⟩ : kernel F) = 1 :=
    fixedPointFree F c hc ⟨p, hp.1⟩ (by
      rw [hp.2 c (mem_sup_right c.property), mul_inv_cancel_right])
  exact congrArg Subtype.val he

/-- Standard-root version, with the actual complement as inner implementer. -/
theorem standard_fixes_and_inner (hlarge : 2 < Nat.card F)
    (D : Subgroup PSL(2,F)) (hDB : D ≤ borel F)
    (hd : Disjoint (kernel F) D) (hs : kernel F ⊔ D = borel F)
    (a : MulAut PSL(2,F)) (haU : (kernel F).map a.toMonoidHom = kernel F)
    (haD : D.map a.toMonoidHom = D)
    (hquad : ∀ x ∈ D, a (a x * x⁻¹) = a x * x⁻¹) :
    (∀ x ∈ D, a x = x) ∧ ∃ d ∈ D, a = MulAut.conj d := by
  obtain ⟨g, σ, hg⟩ := coverage a
  have hgB : g ∈ borel F := inner_factor_mem_borel F g σ (hg ▸ haU)
  let b := borelActor F ⟨g, hgB⟩ σ
  have hfix : ∀ x ∈ D, a x = x :=
    MonoidHom.fixes_complement_of_quadratic_field_quotient
      (kernel F) (borel F) D le_sup_left hDB hd hs
      (torusProjection F) (torusProjection_surjective F)
      (by ext x; exact torusProjection_eq_one_iff F x)
      a.toMonoidHom b.toMonoidHom
      (fun x => (borelActor_apply_coe F ⟨g, hgB⟩ σ x).trans
        (MulEquiv.congr_fun hg.symm x)) σ
      (torusProjection_borelActor F ⟨g, hgB⟩ σ)
      (fun x hx => haD ▸ mem_map_of_mem a.toMonoidHom hx) hquad
  have hDmap : (D.subgroupOf (borel F)).map (torusProjection F) = ⊤ := by
    have hgen : (torusProjection F).ker ⊔ D.subgroupOf (borel F) = ⊤ := by
      have hk : (torusProjection F).ker = (kernel F).subgroupOf (borel F) := by
        ext x; exact torusProjection_eq_one_iff F x
      rw [hk, ← subgroupOf_sup (show kernel F ≤ borel F from le_sup_left) hDB,
        hs, subgroupOf_self]
    have he := congrArg (Subgroup.map (torusProjection F)) hgen
    simpa only [Subgroup.map_sup, map_ker_self, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (torusProjection_surjective F)] using he
  have hσ : σ = 1 := by
    have hu (u : Fˣ) : Units.map σ.toMonoidHom u = u := by
      obtain ⟨x, hx, rfl⟩ := hDmap ▸ (show u ∈ (⊤ : Subgroup Fˣ) from trivial)
      rw [← torusProjection_borelActor]
      apply congrArg (torusProjection F)
      apply Subtype.ext
      exact (borelActor_apply_coe F ⟨g, hgB⟩ σ x).trans
        ((MulEquiv.congr_fun hg.symm x).trans (hfix x hx))
    apply RingEquiv.ext
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact congrArg Units.val (hu (Units.mk0 x hx))
  have hinner : a = MulAut.conj g := by
    rw [hg, hσ]
    change MulAut.conj g * RankOneFieldAutomorphisms.pslFieldAction 1 = _
    rw [map_one, mul_one]
  have hab : IsMulCommutative D := by
    let f := (torusProjection F).comp (inclusion hDB)
    have hi : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply eq_bot_iff.mpr
      intro d hd'
      apply mem_bot.mpr
      apply Subtype.ext
      apply disjoint_def.mp hd
      · exact (torusProjection_eq_one_iff F _).mp hd'
      · exact d.property
    exact ⟨⟨fun x y => hi (by rw [map_mul, map_mul, mul_comm])⟩⟩
  let := hab
  have hprod : g ∈ (kernel F : Set PSL(2,F)) * (D : Set PSL(2,F)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (hDB.trans ((normalizer_kernel F).symm.le))]
    rwa [hs]
  obtain ⟨u, hu, d, hD, hgd⟩ := hprod
  have huc : u ∈ centralizer (D : Set PSL(2,F)) := by
    intro x hx
    have hdcomm : d * x = x * d := congrArg Subtype.val
      (mul_comm' (⟨d, hD⟩ : D) ⟨x, hx⟩)
    have hxg : g * x * g⁻¹ = x := by rw [← MulAut.conj_apply, ← hinner]; exact hfix x hx
    rw [← hgd] at hxg
    have hux : u * x * u⁻¹ = x := by
      calc
        _ = (u * d) * x * (u * d)⁻¹ := by rw [mul_inv_rev, mul_assoc u d x, hdcomm]; group
        _ = x := hxg
    exact (mul_inv_eq_iff_eq_mul.mp hux).symm
  have huB : u ∈ centralizer (borel F : Set PSL(2,F)) := by
    rw [← hs, sup_eq_closure, centralizer_closure]
    intro x hx
    rcases hx with hx | hx
    · exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : kernel F) ⟨u, hu⟩)
    · exact huc x hx
  have hu1 : u = 1 := by
    have hm : u ∈ kernel F ⊓ centralizer (borel F : Set PSL(2,F)) := ⟨hu, huB⟩
    simpa only [kernel_inf_centralizer_borel hlarge, mem_bot] using hm
  have hgd' : g = d := by simpa only [hu1, one_mul] using hgd.symm
  exact ⟨hfix, d, hD, hgd' ▸ hinner⟩

/-- A quadratic automorphism preserving a prescribed Sylow root group and
its actual Borel complement fixes that complement and is inner by it. -/
theorem fixes_and_inner (hlarge : 2 < Nat.card F)
    (P : Sylow 2 PSL(2,F)) (D : Subgroup PSL(2,F))
    (hDN : D ≤ normalizer (P : Set PSL(2,F)))
    (hd : Disjoint (P : Subgroup PSL(2,F)) D)
    (hs : (P : Subgroup PSL(2,F)) ⊔ D = normalizer (P : Set PSL(2,F)))
    (a : MulAut PSL(2,F))
    (haP : (P : Subgroup PSL(2,F)).map a.toMonoidHom = P)
    (haD : D.map a.toMonoidHom = D)
    (hquad : ∀ x ∈ D, a (a x * x⁻¹) = a x * x⁻¹) :
    (∀ x ∈ D, a x = x) ∧ ∃ d ∈ D, a = MulAut.conj d := by
  obtain ⟨c, hcU, hcB⟩ := sylow_normalizer_conjugate F P
  let e := (MulAut.conj c).symm
  let E := D.map e.toMonoidHom
  let b := MulAut.congr e a
  have hU : (P : Subgroup PSL(2,F)).map e.toMonoidHom = kernel F :=
    (map_symm_eq_iff_map_eq (kernel F) (e := MulAut.conj c)).mpr hcU
  have hB : (normalizer (P : Set PSL(2,F))).map e.toMonoidHom = borel F :=
    (map_symm_eq_iff_map_eq (borel F) (e := MulAut.conj c)).mpr hcB
  have hEq (x : PSL(2,F)) : b (e x) = e (a x) := by
    change e (a (e.symm (e x))) = e (a x)
    rw [e.symm_apply_apply]
  have hmap (V : Subgroup PSL(2,F)) :
      (V.map e.toMonoidHom).map b.toMonoidHom = (V.map a.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact hEq x
  have hbU : (kernel F).map b.toMonoidHom = kernel F := by rw [← hU, hmap, haP]
  have hbE : E.map b.toMonoidHom = E := by
    change (D.map e.toMonoidHom).map b.toMonoidHom = D.map e.toMonoidHom
    rw [hmap, haD]
  obtain ⟨hfix, d, hdE, hb⟩ := standard_fixes_and_inner hlarge E
    (hB ▸ map_mono hDN) (hU ▸ disjoint_map e.injective hd)
    (by rw [← hU, ← Subgroup.map_sup, hs, hB]) b hbU hbE (by
      rintro x ⟨x, hx, rfl⟩
      change b (b (e x) * (e x)⁻¹) = b (e x) * (e x)⁻¹
      rw [hEq, ← map_inv, ← map_mul, hEq, hquad x hx])
  refine ⟨?_, e.symm d, ?_, ?_⟩
  · intro x hx
    apply e.injective
    rw [← hEq]
    exact hfix (e x) (mem_map_of_mem e.toMonoidHom hx)
  · obtain ⟨x, hx, rfl⟩ := hdE
    change e.symm (e x) ∈ D
    rw [e.symm_apply_apply]
    exact hx
  · apply (MulAut.congr e).injective
    rw [MulAut.congr_conj, e.apply_symm_apply]
    exact hb

/-- Carrier transport, retaining the prescribed Sylow and its complement. -/
theorem fixes_and_inner_of_equiv {K : Type*} [_root_.Group K] [Finite K]
    (e : K ≃* PSL(2,F)) (hlarge : 2 < Nat.card F)
    (P : Sylow 2 K) (D : Subgroup K) (hDN : D ≤ normalizer (P : Set K))
    (hd : Disjoint (P : Subgroup K) D)
    (hs : (P : Subgroup K) ⊔ D = normalizer (P : Set K))
    (a : MulAut K) (haP : (P : Subgroup K).map a.toMonoidHom = P)
    (haD : D.map a.toMonoidHom = D)
    (hquad : ∀ x ∈ D, a (a x * x⁻¹) = a x * x⁻¹) :
    (∀ x ∈ D, a x = x) ∧ ∃ d ∈ D, a = MulAut.conj d := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let E := D.map e.toMonoidHom
  let b := MulAut.congr e a
  have hN : (normalizer (P : Set K)).map e.toMonoidHom = normalizer (Q : Set PSL(2,F)) := by
    exact map_equiv_normalizer_eq (P : Subgroup K) e
  have hEq (x : K) : b (e x) = e (a x) := by
    change e (a (e.symm (e x))) = e (a x)
    rw [e.symm_apply_apply]
  have hmap (V : Subgroup K) :
      (V.map e.toMonoidHom).map b.toMonoidHom = (V.map a.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact hEq x
  have hbQ : (Q : Subgroup PSL(2,F)).map b.toMonoidHom = Q := by
    change ((P : Subgroup K).map e.toMonoidHom).map b.toMonoidHom = _
    rw [hmap, haP]; rfl
  have hbE : E.map b.toMonoidHom = E := by
    change (D.map e.toMonoidHom).map b.toMonoidHom = D.map e.toMonoidHom
    rw [hmap, haD]
  obtain ⟨hfix, d, hdE, hb⟩ := fixes_and_inner hlarge Q E
    (hN ▸ map_mono hDN) (disjoint_map e.injective hd)
    (by change (P : Subgroup K).map e.toMonoidHom ⊔ D.map e.toMonoidHom = _
        rw [← Subgroup.map_sup, hs, hN]) b hbQ hbE (by
      rintro x ⟨x, hx, rfl⟩
      change b (b (e x) * (e x)⁻¹) = b (e x) * (e x)⁻¹
      rw [hEq, ← map_inv, ← map_mul, hEq, hquad x hx])
  refine ⟨?_, e.symm d, ?_, ?_⟩
  · intro x hx
    apply e.injective
    rw [← hEq]
    exact hfix (e x) (mem_map_of_mem e.toMonoidHom hx)
  · obtain ⟨x, hx, rfl⟩ := hdE
    change e.symm (e x) ∈ D
    rw [e.symm_apply_apply]
    exact hx
  · apply (MulAut.congr e).injective
    rw [MulAut.congr_conj, e.apply_symm_apply]
    exact hb

end Theory.PSL2.QuadraticTorus
