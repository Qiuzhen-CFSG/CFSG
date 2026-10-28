module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrdinaryLocal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.CubicOrder
public import Theory.GroupAction.SylowFixedCentralQuotient
public import Theory.GroupAction.FourGroupSylowCentralizer

/-!
# Fixed centralizers in perfect central covers of Higman--Sims

An involution fixing a full Sylow two-subgroup pointwise acts on the
literal HS central quotient as conjugation by a two-central involution.
Perfectness lifts innerness to the full cover. Fixed-point lifting through
the central kernel identifies the fixed subgroup with the full preimage
of the HS involution centralizer. Both centralizers are maximal, and the
HS image has order indivisible by nine.

The proof combines the checked native Sylow-fixer theorem with central
fixed-point lifting; no new finite certificate is needed. The actual
automorphism and central projection are retained. This supplies the fixed
centralizer comparison used in the surviving HS branch of Aschbacher--Smith
12.6.12, printed pp.825--826. The native inputs retain their ATLAS
attribution and GLS3 Table 5.3m source references.
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
namespace Sporadic.LeechRelated.HS
variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]

/-- A nontrivial Sylow-fixing involution has the full marked maximal centralizer. -/
theorem sylow_fixed_central_cover
    (e : (X ⧸ center X) ≃* Carrier) (P : Sylow 2 X)
    (a : MulAut X) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hfix : ∀ x ∈ P, a x = x) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
    ∃ u : Carrier, orderOf u = 2 ∧ TwoCentral u ∧
      MulAut.centralQuotientAction e a = MulAut.conj u ∧
      (∃ x : X, a = MulAut.conj x) ∧
      a.fixedSubgroup.map q = centralizer ({u} : Set Carrier) ∧
      (centralizer ({u} : Set Carrier)).comap q = a.fixedSubgroup ∧
      IsCoatom (centralizer ({u} : Set Carrier)) ∧ IsCoatom a.fixedSubgroup ∧
      ¬ 9 ∣ Nat.card (a.fixedSubgroup.map q) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let Q := P.mapSurjective hq
  let b := MulAut.centralQuotientAction e a
  have heq (x : X) : q (a x) = b (q x) :=
    (MulAut.centralQuotientAction_apply e a x).symm
  have hbfix : ∀ x ∈ Q, b x = x := by
    rintro _ ⟨x,hx,rfl⟩
    rw [←heq,hfix x hx]
  obtain ⟨u,hu⟩ := OrdinaryLocal.automorphism_inner_of_fixes_sylow Q b hbfix
  have hb2 : b ^ 2 = 1 := by rw [←map_pow,ha,map_one]
  have hbne : b ≠ 1 := by
    intro hh
    apply hne
    apply MulAut.centralQuotientAction_injective e
    simpa only [map_one] using hh
  have hu2 : u ^ 2 = 1 := by
    apply MulAut.conj_injective_of_center_eq_bot BlockNormalizer.center_carrier_eq_bot
    rw [map_pow,←hu,hb2,map_one]
  have hune : u ≠ 1 := by
    intro hh
    apply hbne
    rw [hu,hh,map_one]
  have huc : ∀ x ∈ Q, Commute u x := by
    intro x hx
    have hh := hbfix x hx
    rw [hu,MulAut.conj_apply] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have huQ : u ∈ Q :=
    Theory.GroupAction.mem_sylow_of_sq_eq_one_of_centralizes Q hu2 (fun x hx => (huc x hx).eq.symm)
  have hucentral : TwoCentral u := by
    refine ⟨Q,huQ,mem_center_iff.mpr ?_⟩
    intro x
    exact Subtype.ext (huc x x.property).eq.symm
  have hinner : ∃ x : X, a = MulAut.conj x :=
    (MulAut.centralQuotientAction_inner_iff e a).mp ⟨u,hu⟩
  have himage : a.fixedSubgroup.map q = b.fixedSubgroup := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [MulAut.mem_fixedSubgroup,←heq,(MulAut.mem_fixedSubgroup _ _).mp hx]
    · intro y hy
      obtain ⟨x,hx⟩ := MulAut.fixedSubgroupMap_surjective_of_sylow_fixed
        a b q hq hk.le heq ha P hfix ⟨y,hy⟩
      exact ⟨x,x.property,congrArg Subtype.val hx⟩
  rw [hu,MulAut.fixedSubgroup_conj] at himage
  have hker : q.ker ≤ a.fixedSubgroup := by
    obtain ⟨x,rfl⟩ := hinner
    intro y hy
    rw [MulAut.mem_fixedSubgroup,MulAut.conj_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp (hk ▸ hy) x)
  have hfull : (centralizer ({u} : Set Carrier)).comap q = a.fixedSubgroup := by
    rw [←himage,comap_map_eq_self hker]
  have huord : orderOf u = 2 := orderOf_eq_prime hu2 hune
  have hmax := OrdinaryLocal.twoCentral_centralizer_isCoatom u huord hucentral
  refine ⟨u,huord,hucentral,hu,hinner,himage,hfull,hmax,?_,?_⟩
  · rw [←hfull]
    exact isCoatom_comap_of_surjective hq hmax
  · rw [himage]
    exact SylowOvergroups.proper_overgroup_not_nine_dvd Q _
      (fun x hx => mem_centralizer_singleton_iff.mpr (huc x hx).eq.symm) hmax.1
end Sporadic.LeechRelated.HS
