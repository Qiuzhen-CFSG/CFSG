module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Basic

/-!
# Centrality tests in the two action quotients

Two-centrality is equivalent to membership in the component, order two,
and odd index of the relative centralizer. Thus a comparison of actual
fixed groups can be used without identifying an actor with a component
element before projection.

An ambient isomorphism induces an isomorphism of N(L)/C(L), carrying the
actual component and actor images to their corresponding images. All
central kernels are retained. The common residual also gives an
isomorphism between full residuals after moving the second component back
by conjugation; it does not identify their two central-quotient images.

These are transport tools for the row comparison in Aschbacher–Smith,
combined manuscript of 1 March 2004, 16.5.6(4), printed p.1197. They do not
assert the comparison of the rows in 16.1.4–5.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality
open Subgroup

variable {G H : Type*} [Group G] [Group H]

/-- The centralizer is taken inside the component, even for an outer actor. -/
abbrev relativeCentralizer (L : Subgroup G) (v : G) : Subgroup L :=
  (centralizer ({v} : Set G)).subgroupOf L

/-- The intrinsic index criterion retains component membership as a separate
condition. Odd fixed-group index alone is insufficient for an outer actor. -/
theorem twoCentral_iff_odd_index [Finite G] {L : Subgroup G} {v : G} :
    IsTwoCentralIn L v ↔ orderOf v = 2 ∧ v ∈ L ∧
      Odd (relativeCentralizer L v).index := by
  constructor
  · rintro ⟨hv2, S, ⟨P, rfl⟩, hvS, hSC⟩
    have hP : (P : Subgroup L) ≤ relativeCentralizer L v := by
      intro x hx
      exact hSC (mem_map_of_mem L.subtype hx)
    refine ⟨hv2, (map_subtype_le _) hvS, ?_⟩
    exact Nat.not_even_iff_odd.mp (fun he => P.not_dvd_index
      ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hP)))
  · rintro ⟨hv2, hvL, hodd⟩
    let C := relativeCentralizer L v
    let vC : C := ⟨⟨v, hvL⟩, mem_centralizer_singleton_iff.mpr rfl⟩
    have hvC : orderOf vC = 2 := by
      rw [← orderOf_coe vC, ← orderOf_coe (vC : L)]
      exact hv2
    have hp : IsPGroup 2 (zpowers vC) := by
      apply IsPGroup.of_card (n := 1)
      simpa only [Nat.card_zpowers, pow_one] using hvC
    obtain ⟨P, hvP⟩ := hp.exists_le_sylow
    let Q := (P : Subgroup C).map C.subtype
    have hQindex : ¬ 2 ∣ Q.index := by
      rw [index_map_subtype]
      intro h
      rcases Nat.prime_two.dvd_mul.mp h with h | h
      · exact P.not_dvd_index h
      · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    let S := (P.isPGroup'.map C.subtype).toSylow hQindex
    refine ⟨hv2, Q.map L.subtype, ⟨S, rfl⟩, ?_, ?_⟩
    · exact mem_map.mpr ⟨⟨v, hvL⟩,
        mem_map.mpr ⟨vC, hvP (mem_zpowers vC), rfl⟩, rfl⟩
    · rintro x ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      exact w.property

/-- An isomorphism of the actual relative fixed groups preserves their
indices when the components have the same order. -/
theorem relativeCentralizer_index_eq [Finite G] [Finite H]
    {L : Subgroup G} {M : Subgroup H} {u : G} {v : H}
    (hLM : Nat.card L = Nat.card M)
    (eC : relativeCentralizer L u ≃* relativeCentralizer M v) :
    (relativeCentralizer L u).index = (relativeCentralizer M v).index := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := relativeCentralizer L u))
  rw [(relativeCentralizer L u).card_mul_index, Nat.card_congr eC.toEquiv,
    (relativeCentralizer M v).card_mul_index, hLM]

/-- Once row analysis gives an inner actor and an actual fixed-group
isomorphism, its Sylow-centrality follows from the index criterion. -/
theorem twoCentral_of_fixedGroup_equiv [Finite G] [Finite H]
    {L : Subgroup G} {M : Subgroup H} {u : G} {v : H}
    (hLM : Nat.card L = Nat.card M)
    (eC : relativeCentralizer L u ≃* relativeCentralizer M v)
    (hv : v ∈ M) (hv2 : orderOf v = 2) (hu : IsTwoCentralIn L u) :
    IsTwoCentralIn M v := by
  apply twoCentral_iff_odd_index.mpr
  refine ⟨hv2, hv, ?_⟩
  rw [← relativeCentralizer_index_eq hLM eC]
  exact (twoCentral_iff_odd_index.mp hu).2.2

/-- Transport a witnessing Sylow subgroup between different ambient types. -/
theorem twoCentral_map [Finite G] [Finite H]
    {L : Subgroup G} {u : G} (hu : IsTwoCentralIn L u) (e : G ≃* H) :
    IsTwoCentralIn (L.map e.toMonoidHom) (e u) := by
  obtain ⟨hu2, S, ⟨P, rfl⟩, huS, hSC⟩ := hu
  let eL := L.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨(e.orderOf_eq u).trans hu2,
    ((P : Subgroup L).map L.subtype).map e.toMonoidHom, ?_,
    mem_map_of_mem e.toMonoidHom huS, ?_⟩
  · refine ⟨P.mapSurjective (f := eL.toMonoidHom) eL.surjective, ?_⟩
    change ((P : Subgroup L).map eL.toMonoidHom).map
      (L.map e.toMonoidHom).subtype = _
    rw [map_map, map_map]
    rfl
  · rintro y ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      congrArg e (mem_centralizer_singleton_iff.mp (hSC hx))

/-- Normalizers transport with the actual component. -/
noncomputable def normalizerEquiv (L : Subgroup G) (e : G ≃* H) :
    normalizer (L : Set G) ≃* normalizer (L.map e.toMonoidHom : Set H) :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_equiv_normalizer_eq L e))

/-- Transport preserves the relative centralizer kernel, including Z(L). -/
theorem normalizerEquiv_map_kernel (L : Subgroup G) (e : G ≃* H) :
    ((centralizer (L : Set G)).subgroupOf (normalizer (L : Set G))).map
      (normalizerEquiv L e).toMonoidHom =
    (centralizer (L.map e.toMonoidHom : Set H)).subgroupOf
      (normalizer (L.map e.toMonoidHom : Set H)) := by
  ext x
  rw [mem_map_equiv]
  change e.symm (x : H) ∈ centralizer (L : Set G) ↔
    (x : H) ∈ centralizer (L.map e.toMonoidHom : Set H)
  constructor
  · intro hx
    apply mem_centralizer_iff.mpr
    rintro y ⟨z, hz, rfl⟩
    simpa only [map_mul, e.apply_symm_apply, MulEquiv.coe_toMonoidHom] using
      congrArg e (mem_centralizer_iff.mp hx z hz)
  · intro hx
    apply mem_centralizer_iff.mpr
    intro z hz
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      mem_centralizer_iff.mp hx (e z) (mem_map_of_mem e.toMonoidHom hz)

/-- The induced equivalence of the two genuine action quotients. -/
noncomputable def actionQuotientEquiv (L : Subgroup G) (e : G ≃* H) :
    ActionQuotient L ≃* ActionQuotient (L.map e.toMonoidHom) :=
  QuotientGroup.congr _ _ (normalizerEquiv L e) (normalizerEquiv_map_kernel L e)

/-- The induced equivalence preserves the specified actor projection. -/
theorem actionQuotientEquiv_actionMap {L A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G)) (e : G ≃* H)
    (hAe : A.map e.toMonoidHom ≤ normalizer (L.map e.toMonoidHom : Set H))
    (a : A) :
    actionQuotientEquiv L e (actionMap hA a) =
      actionMap hAe (A.equivMapOfInjective e.toMonoidHom e.injective a) := rfl

/-- In particular L* maps to the actual component image on the other side. -/
theorem actionQuotientEquiv_componentImage (L : Subgroup G) (e : G ≃* H) :
    (componentImage L).map (actionQuotientEquiv L e).toMonoidHom =
      componentImage (L.map e.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨L.equivMapOfInjective e.toMonoidHom e.injective a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨actionMap L.le_normalizer ((L.equivMapOfInjective e.toMonoidHom e.injective).symm a),
      ⟨_, rfl⟩, ?_⟩
    change actionQuotientEquiv L e (actionMap L.le_normalizer _) = _
    rw [actionQuotientEquiv_actionMap L.le_normalizer e
      (L.map e.toMonoidHom).le_normalizer, MulEquiv.apply_symm_apply]

/-- Centrality transports in the quotients while the actor remains projected. -/
theorem twoCentral_actionMap_transport [Finite G] [Finite H]
    {L A : Subgroup G} (hA : A ≤ normalizer (L : Set G)) (e : G ≃* H)
    (hAe : A.map e.toMonoidHom ≤ normalizer (L.map e.toMonoidHom : Set H))
    (a : A) (ha : IsTwoCentralIn (componentImage L) (actionMap hA a)) :
    IsTwoCentralIn (componentImage (L.map e.toMonoidHom))
      (actionMap hAe (A.equivMapOfInjective e.toMonoidHom e.injective a)) := by
  have h := twoCentral_map ha (actionQuotientEquiv L e)
  rwa [actionQuotientEquiv_componentImage,
    actionQuotientEquiv_actionMap hA e hAe] at h

/-- Move the opposite residual back into L before comparing its full group
structure. No equality of images modulo the two centers is asserted. -/
noncomputable def residualEquiv_of_common [Finite G]
    {L X : Subgroup G} {g u i : G}
    (hu : modifiedCentralizerResidual L u = X)
    (hi : modifiedCentralizerResidual (L.conjBy g) i = X) :
    modifiedCentralizerResidual L u ≃*
      modifiedCentralizerResidual L (MulAut.conj g⁻¹ i) :=
  (MulEquiv.subgroupCongr (hu.trans hi.symm)).trans
    (((modifiedCentralizerResidual (L.conjBy g) i).equivMapOfInjective
      (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).trans
      (MulEquiv.subgroupCongr (by
        rw [modifiedCentralizerResidual_map]
        change modifiedCentralizerResidual ((L.conjBy g).conjBy g⁻¹) _ = _
        rw [conjBy_inv])))

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality
