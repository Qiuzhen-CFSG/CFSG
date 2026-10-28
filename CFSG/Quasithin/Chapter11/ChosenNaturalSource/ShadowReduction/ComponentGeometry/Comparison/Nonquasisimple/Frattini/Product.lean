module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Radical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.Frattini
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.RelativeModels
public import Theory.GroupTheory.CComponent.SolvableSupplement
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.PerfectCenterFrattini

/-!
# The Frattini product in the point-component comparison

The prime SL₂ model above the literal Fitting preimage gives a PSL₂
radical quotient. The preceding module proves the Sylow assertion from
this model and the original rank-one seed. Frattini's argument and
perfectness then give Kz = O∞(Kz) N_Kz(R₁)^∞. Modulo the Fitting
preimage the radical is central; the central supplement theorem for a
perfect group removes it, giving the exact source factorization.

The complete 11.1.1 catalogue must still produce the prime SL₂ model;
it is an explicit input, not a conclusion of this module. The residual
kernel calculation is a separate step.
Source: Aschbacher--Smith, 11.4.2, printed p.777. The relative Frattini
transport follows LocalGeometry.Normalizers.Frattini; the external-Sylow
product argument also appears in Chapter13, Supplements.CanonicalGeometry.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
variable {G : Type*} [Group G] [Finite G]

private theorem radical_normalizer_frattini {B R : Subgroup G}
    (hRB : R ≤ normalizer (B : Set G))
    (hc : ⁅B,R⁆ ≤ (solvableRadical B).map B.subtype)
    (hs : Chapter1.IsSylowIn 2 R ((solvableRadical B).map B.subtype ⊔ R)) :
    (solvableRadical B).map B.subtype ⊔ (B ⊓ normalizer (R : Set G)) = B := by
  let D := (solvableRadical B).map B.subtype
  let C := D ⊔ R
  let W := B ⊔ R
  have hDB : D ≤ B := map_subtype_le _
  have hWB : W ≤ normalizer (B : Set G) := sup_le B.le_normalizer hRB
  have hWD : W ≤ normalizer (D : Set G) :=
    hWB.trans (normalizer_le_normalizer_characteristic_image B (solvableRadical B))
  have hBC : B ≤ normalizer (C : Set G) := by
    apply le_normalizer_iff.mpr
    intro b hb c hc'
    have hconj : C ≤ C.comap (MulAut.conj b).toMonoidHom := by
      apply sup_le
      · intro d hd
        exact mem_sup_left (le_normalizer_iff.mp hWD b (mem_sup_left hb) d hd)
      · intro r hr
        have hm := C.mul_mem (mem_sup_left (hc (commutator_mem_commutator hb hr)))
          (mem_sup_right hr)
        change b * r * b⁻¹ ∈ C
        simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hm
    exact hconj hc'
  have hRC : R ≤ normalizer (C : Set G) :=
    (le_inf (le_sup_right.trans hWD) R.le_normalizer).trans
      (normalizer_inf_normalizer_le_normalizer_sup D R)
  have hCW : C ≤ W := sup_le (hDB.trans le_sup_left) le_sup_right
  obtain ⟨S, hS⟩ := hs
  have hfr := LocalGeometry.Normalizers.relative_frattini hCW (sup_le hBC hRC) S hS
  apply le_antisymm (sup_le hDB inf_le_left)
  intro b hb
  have hbW : b ∈ C ⊔ (W ⊓ normalizer (R : Set G)) := hfr ▸ mem_sup_left hb
  have hnC : W ⊓ normalizer (R : Set G) ≤ normalizer (C : Set G) :=
    inf_le_left.trans (sup_le hBC hRC)
  obtain ⟨c,hc',n,hn,he⟩ :=
    (coe_mul_of_right_le_normalizer_left C _ hnC).subset hbW
  obtain ⟨d,hd,r,hr,hdr⟩ :=
    (coe_mul_of_right_le_normalizer_left D R (le_sup_right.trans hWD)).subset hc'
  have hrn : r*n ∈ B := by
    have := B.mul_mem (B.inv_mem (hDB hd)) hb
    simpa only [← he,← hdr,mul_assoc,inv_mul_cancel_left] using this
  have hrnN : r*n ∈ normalizer (R : Set G) :=
    (normalizer (R : Set G)).mul_mem (R.le_normalizer hr) hn.2
  have he' : d*(r*n) = b := by
    change d*r=c at hdr
    change c*n=b at he
    rw [← mul_assoc,hdr,he]
  rw [← he']
  exact (D ⊔ (B ⊓ normalizer (R : Set G))).mul_mem (mem_sup_left hd)
    (mem_sup_right ⟨hrn,hrnN⟩)

private theorem fitting_supplement_of_radical_supplement
    {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    [IsQuasisimple (A ⧸ twoFittingCore A)] (B : Subgroup A)
    (hgen : solvableRadical A ⊔ B = ⊤) : twoFittingCore A ⊔ B = ⊤ := by
  let q := QuotientGroup.mk' (twoFittingCore A)
  have hc : (solvableRadical A).map q ≤ center (A ⧸ twoFittingCore A) :=
    (map_solvableRadical_le_of_surjective q (QuotientGroup.mk'_surjective _)).trans
      IsQuasisimple.solvableRadical_le_center
  have hB : B.map q = ⊤ := by
    apply eq_top_of_sup_center_eq_top
    apply top_unique
    have hm := congrArg (map q) hgen
    rw [Subgroup.map_sup, map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hm
    rw [← hm]
    exact sup_le (hc.trans le_sup_right) le_sup_left
  have he := congrArg (comap q) hB
  simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top, sup_comm] using he

variable {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

/-- The actual SL₂ quotient above O₂,F induces the PSL₂ radical model. -/
theorem radical_model_of_fitting_sl2 {p : ℕ} (hp : 3 < p)
    (hm : Source.IsSL (E.Kz ⧸ twoFittingCore E.Kz) 2 p) :
    ClassicalGroup.IsPSL (E.Kz ⧸ solvableRadical E.Kz) 2 p := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let q := QuotientGroup.mk' (twoFittingCore E.Kz)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact twoFittingCore_solvable
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨(solvableRadicalQuotientEquiv q (QuotientGroup.mk'_surjective _)).trans
      (Theory.SpecificGroups.SL2.ResidualTwoExtension.radicalQuotientEquiv (by omega) e)⟩⟩

private theorem radical_frattini_split (h : EarlierGeometry E)
    (hR : E.R₁ ≤ (solvableRadical (pointRadicalJoin E)).map (pointRadicalJoin E).subtype)
    (hs : Chapter1.IsSylowIn 2 E.R₁
      ((solvableRadical (pointRadicalJoin E)).map (pointRadicalJoin E).subtype)) :
    (solvableRadical E.Kz).map E.Kz.subtype ⊔ normalizerResidual E = E.Kz := by
  let J := pointRadicalJoin E
  let A := E.Kz.subgroupOf J
  have hTK : (T : Subgroup G) ≤ normalizer (E.Kz : Set G) :=
    h.sylow_le_pointCentralizer.trans (le_normalizer_conjugateSpanBy _ _)
  have hRT : E.R₁ ≤ (T : Subgroup G) := by
    change (E.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hRK := hRT.trans hTK
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le E.Kz.le_normalizer hRK)
  let e : A ≃* E.Kz := subgroupOfEquivOfLe (show E.Kz ≤ J from le_sup_left)
  have hrad : (solvableRadical E.Kz).map E.Kz.subtype =
      (E.Kz ⊓ (solvableRadical J).map J.subtype) := by
    have he : (solvableRadical A).map A.subtype = solvableRadical J ⊓ A := by
      rw [← radical_subgroupOf_normal A, subgroupOf_map_subtype]
    have hm := congrArg (map J.subtype) he
    rw [map_map, map_inf _ _ _ J.subtype_injective,
      map_subgroupOf_eq_of_le (show E.Kz ≤ J from le_sup_left)] at hm
    rw [← map_solvableRadical_equiv e, map_map]
    exact hm.trans (inf_comm _ _)
  have hc : ⁅E.Kz, E.R₁⁆ ≤ (solvableRadical E.Kz).map E.Kz.subtype := by
    rw [hrad]
    apply le_inf (le_normalizer_iff_commutator_le_left.mp hRK)
    exact (commutator_mono le_rfl hR).trans
      (le_normalizer_iff_commutator_le_right.mp
        (le_sup_left.trans (J.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image J (solvableRadical J)))))
  have hfr := radical_normalizer_frattini hRK hc
    (hs.restrict le_sup_right (sup_le (hrad.le.trans inf_le_right) hR))
  let : Group.IsPerfect E.Kz := Radical.relative_component_perfect h.point_component
  have hm := map_solvableResidual_le_sup_residual_of_sup_eq E.Kz
    ((solvableRadical E.Kz).map E.Kz.subtype) (E.Kz ⊓ normalizer (E.R₁ : Set G))
    (map_subtype_le _) inf_le_left
    (E.Kz.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image E.Kz (solvableRadical E.Kz))) hfr
  rw [solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hm
  exact le_antisymm (sup_le (map_subtype_le _) normalizerResidual_le) hm

/-- The literal source factorization, proved from the preceding seed model
and the remaining exceptional SL₂ model. It assumes no radical, Sylow,
factorization, or residual-quotient conclusion. -/
theorem ofFlag_fitting_factorization_of_model (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hm : Source.IsSL ((ofFlag S f X z H).Kz ⧸ twoFittingCore (ofFlag S f X z H).Kz) 2 p) :
    (ofFlag S f X z H).Kz = fittingPreimage (ofFlag S f X z H) ⊔
      normalizerResidual (ofFlag S f X z H) := by
  let E := ofFlag S f X z H
  have hp3 : 3 < p := by
    have hpl := hp.1.two_le
    have h5 := hp.2.1
    omega
  let : Fact p.Prime := ⟨hp.1⟩
  have hmodel := radical_model_of_fitting_sl2 hp3 hm
  have hR := ofFlag_le_join_radical_of_prime_model S f X z H h hA hp3 hmodel
  have hs := ofFlag_sylow_in_join_radical_of_prime_model S f X z H h hA hseed hp3 hmodel
  have hgen := radical_frattini_split h hR hs
  let : Group.IsPerfect E.Kz := Radical.relative_component_perfect h.point_component
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : IsQuasisimple (E.Kz ⧸ twoFittingCore E.Kz) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv (by omega) e
  have hgen' : solvableRadical E.Kz ⊔ (normalizerResidual E).subgroupOf E.Kz = ⊤ := by
    apply map_injective E.Kz.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le normalizerResidual_le, hgen,
      ← MonoidHom.range_eq_map, range_subtype]
  have hh := congrArg (map E.Kz.subtype)
    (fitting_supplement_of_radical_supplement _ hgen')
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le normalizerResidual_le,
    ← MonoidHom.range_eq_map, range_subtype] at hh
  exact hh.symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
