module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankOne

/-!
# Literal section actions and transport

Quotient conjugation is specified on representatives. Ambient conjugation
induces a group equivalence of the literal subgroup quotients and intertwines
their actions. The corresponding binary linear equivalence preserves
nonidentity transvections; a surjective intertwiner also descends their formula.
The commutator of a subgroup image is identified with its generated actual
displacements, and equality of these commutators lifts to an ambient bound.

These are the transport steps of Aschbacher–Smith 13.8.9, 13.8.11 and
13.8.18, combined manuscript (1 March 2004), printed pp.949–950 and 953.
All normality is inside the displayed subgroup, never ambient normality.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.SectionActions
variable {G : Type*} [Group G]

noncomputable def quotientAction (P U Z : Subgroup G)
    [hZ : (Z.subgroupOf U).Normal]
    (hn : P ≤ normalizer (U : Set G)) (hz : P ≤ normalizer (Z : Set G)) :
    P →* MulAut (U ⧸ Z.subgroupOf U) :=
  (exists_quotient_conjugation_action P U Z hn hz hZ).choose

theorem quotientAction_apply (P U Z : Subgroup G)
    [hZ : (Z.subgroupOf U).Normal]
    (hn : P ≤ normalizer (U : Set G)) (hz : P ≤ normalizer (Z : Set G))
    (p : P) (u : U) :
    quotientAction P U Z hn hz p (QuotientGroup.mk' (Z.subgroupOf U) u) =
      QuotientGroup.mk' (Z.subgroupOf U)
        ⟨(p : G) * u * (p : G)⁻¹, (mem_normalizer_iff.mp (hn p.property) u).mp u.property⟩ :=
  (exists_quotient_conjugation_action P U Z hn hz hZ).choose_spec p u

theorem quotientAction_displacement (P U Z : Subgroup G)
    [(Z.subgroupOf U).Normal]
    (hn : P ≤ normalizer (U : Set G)) (hz : P ≤ normalizer (Z : Set G)) :
    commutatorAction (quotientAction P U Z hn hz).range (U ⧸ Z.subgroupOf U) =
      (⁅P, U⁆.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
  have hh := quotient_conjugation_commutatorAction_eq_image P U Z P hn le_rfl
    inferInstance (quotientAction P U Z hn hz) (quotientAction_apply P U Z hn hz)
  have hactors : (P.subgroupOf P).map (quotientAction P U Z hn hz) =
      (quotientAction P U Z hn hz).range := by
    rw [subgroupOf_self, ← MonoidHom.range_eq_map]
  have ht := (congrArg (fun A : Subgroup (MulAut (U ⧸ Z.subgroupOf U)) =>
    commutatorAction A (U ⧸ Z.subgroupOf U)) hactors).symm.trans hh
  simpa only [commutator_comm] using ht

theorem quotientAction_all_eq_one_iff (P U Z : Subgroup G)
    [(Z.subgroupOf U).Normal]
    (hn : P ≤ normalizer (U : Set G)) (hz : P ≤ normalizer (Z : Set G)) :
    (∀ p, quotientAction P U Z hn hz p = 1) ↔ ⁅P, U⁆ ≤ Z := by
  constructor
  · intro h
    apply commutator_le.mpr
    intro p hp u hu
    have hh := quotientAction_apply P U Z hn hz ⟨p, hp⟩ ⟨u, hu⟩
    rw [h] at hh
    have he : (QuotientGroup.mk' (Z.subgroupOf U)
        ⟨p * u * p⁻¹, (mem_normalizer_iff.mp (hn hp) u).mp hu⟩) =
        QuotientGroup.mk' (Z.subgroupOf U) ⟨u, hu⟩ := hh.symm
    have hc := (QuotientGroup.eq_iff_div_mem (N := Z.subgroupOf U)).mp he
    simpa only [mem_subgroupOf, coe_div, div_eq_mul_inv, coe_mul, coe_inv, commutatorElement_def] using hc
  · intro h p
    ext w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
    rw [quotientAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [mem_subgroupOf, coe_div, div_eq_mul_inv, coe_mul, coe_inv, commutatorElement_def] using
      h (commutator_mem_commutator p.property u.property)

def sectionEquiv (e : G ≃* G) (U Z : Subgroup G)
    [(Z.subgroupOf U).Normal]
    [((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))).Normal] :
    (U ⧸ Z.subgroupOf U) ≃*
      (U.map (e : G →* G) ⧸ (Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))) :=
  QuotientGroup.congr _ _ (e.subgroupMap U) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_map_of_mem (e : G →* G) hy
    · intro hx
      obtain ⟨z, hz, he⟩ := hx
      refine ⟨(e.subgroupMap U).symm x, ?_, (e.subgroupMap U).apply_symm_apply x⟩
      change e.symm (x : G) ∈ Z
      change e z = (x : G) at he
      rw [← he, e.symm_apply_apply]
      exact hz)

theorem sectionEquiv_apply (e : G ≃* G) (U Z : Subgroup G)
    [(Z.subgroupOf U).Normal]
    [((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))).Normal] (u : U) :
    sectionEquiv e U Z (QuotientGroup.mk' (Z.subgroupOf U) u) =
      QuotientGroup.mk' ((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G)))
        (e.subgroupMap U u) := QuotientGroup.congr_mk' _ _ _ _ u

theorem sectionEquiv_intertwines (e : G ≃* G) (P U Z : Subgroup G)
    [(Z.subgroupOf U).Normal]
    [((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))).Normal]
    (hn : P ≤ normalizer (U : Set G)) (hz : P ≤ normalizer (Z : Set G))
    (hn' : P.map (e : G →* G) ≤ normalizer (U.map (e : G →* G) : Set G))
    (hz' : P.map (e : G →* G) ≤ normalizer (Z.map (e : G →* G) : Set G))
    (p : P) (w : U ⧸ Z.subgroupOf U) :
    sectionEquiv e U Z (quotientAction P U Z hn hz p w) =
      quotientAction _ _ _ hn' hz' (e.subgroupMap P p) (sectionEquiv e U Z w) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
  rw [quotientAction_apply, sectionEquiv_apply, sectionEquiv_apply, quotientAction_apply]
  congr 1
  apply Subtype.ext
  exact (map_mul e _ _).trans (by rw [map_mul, map_inv]; rfl)

/-- Intertwining permits an actor in any containing subgroup. -/
theorem sectionEquiv_intertwines_actor (e : G ≃* G) (P Q U Z : Subgroup G)
    [(Z.subgroupOf U).Normal]
    [((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))).Normal]
    (hn : P ≤ normalizer (U : Set G)) (hz : P ≤ normalizer (Z : Set G))
    (hn' : Q ≤ normalizer (U.map (e : G →* G) : Set G))
    (hz' : Q ≤ normalizer (Z.map (e : G →* G) : Set G))
    (p : P) (q : Q) (hpq : e (p : G) = (q : G))
    (w : U ⧸ Z.subgroupOf U) :
    sectionEquiv e U Z (quotientAction P U Z hn hz p w) =
      quotientAction _ _ _ hn' hz' q (sectionEquiv e U Z w) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
  rw [quotientAction_apply, sectionEquiv_apply, sectionEquiv_apply, quotientAction_apply]
  congr 1
  apply Subtype.ext
  change e ((p : G) * (u : G) * (p : G)⁻¹) = (q : G) * e u * (q : G)⁻¹
  rw [map_mul, map_mul, map_inv, hpq]

/-- The commutator of the image of F with P, on the literal U/Z. -/
def quotientCommutator (F P U Z : Subgroup G) [(Z.subgroupOf U).Normal] :
    Subgroup (U ⧸ Z.subgroupOf U) :=
  (⁅F, P⁆.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))

/-- This image is precisely generated by displacements of F in U/Z. -/
theorem quotientCommutator_eq_closure (F P U Z : Subgroup G)
    [(Z.subgroupOf U).Normal] (hFU : F ≤ U)
    (hn : P ≤ normalizer (U : Set G)) (hz : P ≤ normalizer (Z : Set G)) :
    quotientCommutator F P U Z = closure {w | ∃ p : P, ∃ f : F,
      w = quotientAction P U Z hn hz p
        (QuotientGroup.mk' (Z.subgroupOf U) ⟨f, hFU f.property⟩) *
        (QuotientGroup.mk' (Z.subgroupOf U) ⟨f, hFU f.property⟩)⁻¹} := by
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  let D := closure {w | ∃ p : P, ∃ f : F,
      w = quotientAction P U Z hn hz p (q ⟨f, hFU f.property⟩) *
        (q ⟨f, hFU f.property⟩)⁻¹}
  have hc : ⁅F, P⁆ ≤ U :=
    (commutator_mono hFU le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hn)
  have hformula (p : P) (f : F) :
      quotientAction P U Z hn hz p (q ⟨f, hFU f.property⟩) *
        (q ⟨f, hFU f.property⟩)⁻¹ =
      q ⟨⁅(p : G), (f : G)⁆, by
        rw [commutator_comm] at hc
        exact hc (commutator_mem_commutator p.property f.property)⟩ := by
    rw [quotientAction_apply, ← map_inv, ← map_mul]
    rfl
  apply le_antisymm
  · have hb : ⁅F, P⁆ ≤ (D.comap q).map U.subtype := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro p hp f hf
      refine ⟨⟨⁅p, f⁆, ?_⟩, ?_, rfl⟩
      · rw [commutator_comm] at hc
        exact hc (commutator_mem_commutator hp hf)
      · change q _ ∈ D
        rw [← hformula ⟨p, hp⟩ ⟨f, hf⟩]
        exact subset_closure ⟨⟨p, hp⟩, ⟨f, hf⟩, rfl⟩
    rintro w ⟨u, hu, rfl⟩
    obtain ⟨v, hv, he⟩ := hb hu
    have hve : v = u := Subtype.ext he
    exact hve ▸ hv
  · apply (closure_le _).mpr
    rintro w ⟨p, f, rfl⟩
    rw [hformula]
    apply mem_map_of_mem
    change ⁅(p : G), (f : G)⁆ ∈ ⁅F, P⁆
    rw [commutator_comm]
    exact commutator_mem_commutator p.property f.property

/-- Lifting equality in the literal module gives the required ambient bound. -/
theorem bound_of_quotientCommutator_eq (F P R U Z : Subgroup G)
    [(Z.subgroupOf U).Normal] (hFU : F ≤ U) (hZU : Z ≤ U)
    (hPF : P ≤ normalizer (F : Set G)) (hRF : R ≤ normalizer (F : Set G))
    (he : quotientCommutator F P U Z = quotientCommutator F R U Z) :
    ⁅F, P⁆ ≤ ⁅F, R⁆ ⊔ Z := by
  have hP : ⁅F, P⁆ ≤ U := (le_normalizer_iff_commutator_le_left.mp hPF).trans hFU
  have hR : ⁅F, R⁆ ≤ U := (le_normalizer_iff_commutator_le_left.mp hRF).trans hFU
  have hh := congrArg (fun A : Subgroup (U ⧸ Z.subgroupOf U) =>
    (A.comap (QuotientGroup.mk' (Z.subgroupOf U))).map U.subtype) he
  simp only [quotientCommutator, comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    map_subgroupOf_eq_of_le hP, map_subgroupOf_eq_of_le hR,
    map_subgroupOf_eq_of_le hZU] at hh
  exact le_sup_left.trans hh.le

def binaryEquiv {W X : Type*} [Group W] [Group X]
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 X]
    (e : W ≃* X) : Additive W ≃ₗ[ZMod 2] Additive X :=
  { e.toAdditive with map_smul' := ZMod.map_smul e.toAdditive }

def binaryMap {W X : Type*} [Group W] [Group X]
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 X]
    (f : W →* X) : Additive W →ₗ[ZMod 2] Additive X :=
  { f.toAdditive with map_smul' := ZMod.map_smul f.toAdditive }

section Linear
variable {W X : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X]

theorem transvection_of_surjective_intertwiner
    (q : W →ₗ[ZMod 2] X) (hq : Function.Surjective q)
    (a : W ≃ₗ[ZMod 2] W) (b : X ≃ₗ[ZMod 2] X)
    (hi : ∀ w, q (a w) = b (q w))
    (ha : a ∈ LinearEquiv.transvections (ZMod 2) W) :
    b ∈ LinearEquiv.transvections (ZMod 2) X := by
  obtain ⟨f, v, hf, rfl⟩ := ha
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hs' (x : X) : q (s x) = x := LinearMap.congr_fun hs x
  have hb (x : X) : b x = x + (f.comp s) x • q v := by
    rw [← hs' x, ← hi, LinearEquiv.transvection.apply, map_add, map_smul]
    simp only [LinearMap.comp_apply, hs']
  by_cases hv : q v = 0
  · have he : b = 1 := by ext x; simp [hb, hv]
    rw [he]
    exact LinearEquiv.one_mem_transvections
  · have hfix : b (q v) = q v := by
      rw [← hi, LinearEquiv.transvection.apply, hf, zero_smul, add_zero]
    have hf' : (f.comp s) (q v) = 0 := by
      have hh := hb (q v)
      rw [hfix] at hh
      exact (smul_eq_zero.mp (add_eq_left.mp hh.symm)).resolve_right hv
    refine ⟨f.comp s, q v, hf', ?_⟩
    ext x
    exact hb x
end Linear

/-- A multiplicative equivalence transports both the formula and nonidentity. -/
theorem transport_nonidentity {W X : Type*} [Group W] [Group X]
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 X]
    (e : W ≃* X) (a : MulAut W) (b : MulAut X)
    (hi : ∀ w, e (a w) = b (e w)) (hne : a ≠ 1)
    (ha : binaryLinear a ∈ LinearEquiv.transvections (ZMod 2) (Additive W)) :
    b ≠ 1 ∧ binaryLinear b ∈ LinearEquiv.transvections (ZMod 2) (Additive X) := by
  refine ⟨?_, transvection_of_surjective_intertwiner (binaryEquiv e).toLinearMap
    (binaryEquiv e).surjective (binaryLinear a) (binaryLinear b) hi ha⟩
  intro hb
  apply hne
  ext w
  apply e.injective
  simpa only [hb, MulAut.one_apply] using hi w

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.SectionActions

end
