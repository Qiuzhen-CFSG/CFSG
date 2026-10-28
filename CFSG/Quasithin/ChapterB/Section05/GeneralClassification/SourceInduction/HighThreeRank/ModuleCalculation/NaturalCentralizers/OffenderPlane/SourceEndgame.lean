module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers.OffenderPlane
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.Algebra.Prime.Lemmas

/-!
# The source offender endgame in B.5.7

Write U = [V,L] and W = [V,O₃(G)]. The crossed-fixation input makes these
invariant subspaces disjoint. Their fixed codimensions add inside V. Since A
moves W, its action on U is a strong offender. This excludes the natural
seven-point action, whose offender ratio is one: the equality case of the
B.1.5(8) restriction inequality leaves no displacement on W. The genuine
six-point strong-offender classification then gives rank A = 3, fixed
codimension two on U, and fixed codimension at most one on W.

The original three-core is cyclic. A nontrivial square-one automorphism of a
cyclic three-group is inversion, as follows by factoring k²-1 modulo 3ⁿ for
its exponent on a generator. Thus the commutator of a moving element of A
with a core generator still generates the core. The commutator displacement
bound gives dim W ≤ 2. Faithfulness excludes dimensions zero and one. Only
then is `threeCoreEquiv_of_plane` applied to obtain the actual order-three
isomorphism. The surviving marking constructs the actual component
isomorphism, on the same section and embedded component as the input model.

No numerical or span premise, global fixed-space splitting, or additional
universal earlier-source implication is assumed. The restriction inequalities
and six/seven-point offender classifications are proved lower-layer results.
The old `OffenderPlaneBounds` interface is not used.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, B.5.7,
printed p.106, final paragraph; B.1.5(8), B.3.2(4), B.3.4(2)(i).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
namespace SourceEndgame

section Numerical

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) [FiniteDimensional (ZMod 2) V]

private theorem disjoint_codim (U W : Subrepresentation ρ)
    (hd : Disjoint U.toSubmodule W.toSubmodule) (A : Subgroup G) :
    fixedCodim U.toRepresentation A + fixedCodim W.toRepresentation A ≤ fixedCodim ρ A := by
  let C := fixedSpace ρ A
  have hfix : (U.toSubmodule ⊔ W.toSubmodule) ⊓ C =
      (U.toSubmodule ⊓ C) ⊔ (W.toSubmodule ⊓ C) := by
    apply le_antisymm
    · rintro v ⟨hv, hc⟩
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
      have huf : u ∈ C := by
        intro a
        have he : ρ a u - u = -(ρ a w - w) := by
          have hh := hc a
          change ρ a (u + w) = u + w at hh
          rw [map_add] at hh
          exact eq_neg_iff_add_eq_zero.mpr (by rw [sub_add_sub_comm, hh, sub_self])
        apply sub_eq_zero.mp
        apply Submodule.disjoint_def.mp hd
        · exact U.toSubmodule.sub_mem (U.apply_mem_toSubmodule a hu) hu
        · change ρ a u - u ∈ W.toSubmodule
          rw [he]
          exact W.toSubmodule.neg_mem (W.toSubmodule.sub_mem
            (W.apply_mem_toSubmodule a hw) hw)
      have hwf : w ∈ C := by
        simpa only [add_sub_cancel_left] using C.sub_mem hc huf
      exact Submodule.add_mem_sup ⟨hu, huf⟩ ⟨hw, hwf⟩
    · exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)
  have hdim := U.toSubmodule.finrank_sup_add_finrank_inf_eq W.toSubmodule
  have hfdim := (U.toSubmodule ⊓ C).finrank_sup_add_finrank_inf_eq (W.toSubmodule ⊓ C)
  rw [hd.eq_bot, finrank_bot, add_zero] at hdim
  rw [(hd.mono inf_le_left inf_le_left).eq_bot, finrank_bot, add_zero] at hfdim
  have hu := (subrepresentationFixedEquiv ρ U A).finrank_eq
  have hw := (subrepresentationFixedEquiv ρ W A).finrank_eq
  have hs := (subrepresentationFixedEquiv ρ (U ⊔ W) A).finrank_eq
  change _ = Module.finrank (ZMod 2) ((U.toSubmodule ⊔ W.toSubmodule) ⊓ C : Submodule (ZMod 2) V) at hs
  rw [hfix, hfdim] at hs
  have hcu := fixedCodim_add_finrank U.toRepresentation A
  have hcw := fixedCodim_add_finrank W.toRepresentation A
  have hcs := fixedCodim_add_finrank (U ⊔ W).toRepresentation A
  change _ + _ = Module.finrank (ZMod 2) (U.toSubmodule ⊔ W.toSubmodule : Submodule (ZMod 2) V) at hcs
  have hb := fixedCodim_subrepresentation_le ρ (U ⊔ W) A
  dsimp only [C] at *
  omega


variable [Finite G] {K : GroupClass}

omit [FiniteDimensional (ZMod 2) V] [Finite G] in
private theorem component_codim {L A : Subgroup G} [L.Normal] (m : SymmetricMovedModel ρ L A) :
    fixedCodim m.sectionData.space.toRepresentation (A.subgroupOf (L ⊔ A)) =
      fixedCodim (normalMoved ρ L).toRepresentation A := by
  let E := LinearEquiv.ofEq _ _ (model_space_eq ρ m)
  have h := fixedCodim_map_equivariant m.sectionData.space.toRepresentation
    (normalMoved ρ L).toRepresentation (L ⊔ A).subtype E
    (fun g v => by apply Subtype.ext; rfl) (A.subgroupOf (L ⊔ A))
  rwa [map_subgroupOf_eq_of_le le_sup_right] at h

private theorem component_strong (hyp : FFHypothesis K ρ) {L A : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L)
    (hA : IsBestOffender ρ A)
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G))
    (hfix : moved ρ L ≤ fixedSpace ρ (pCore 3 G))
    (m : SymmetricMovedModel ρ L A) :
    IsStrongOffender m.sectionData.space.toRepresentation (A.subgroupOf (L ⊔ A)) ∧
      fixedCodim m.sectionData.space.toRepresentation (A.subgroupOf (L ⊔ A)) +
        fixedCodim (normalMoved ρ (pCore 3 G)).toRepresentation A ≤ rank A := by
  let : L.Normal := d.normal
  have hdec := threeCore_moved_decomposition ρ hL d hfix
  have hbound := (disjoint_codim ρ (normalMoved ρ L) (normalMoved ρ (pCore 3 G))
    hdec.2.1 A).trans (hA.isOffender ρ).2
  rw [← component_codim ρ m] at hbound
  have hn : 0 < fixedCodim (normalMoved ρ (pCore 3 G)).toRepresentation A := by
    by_contra! hz
    have hf := (fixedCodim_eq_zero_iff _ A).mp (Nat.eq_zero_of_le_zero hz)
    apply threeCore_moved_not_fixed ρ hyp hm
    intro v hv a
    have hmem : (⟨v, hv⟩ : (normalMoved ρ (pCore 3 G)).toSubmodule) ∈
        fixedSpace (normalMoved ρ (pCore 3 G)).toRepresentation A := by rw [hf]; trivial
    exact congrArg Subtype.val (hmem a)
  refine ⟨⟨(hA.subgroupOf ρ le_sup_right).1, ?_⟩, hbound⟩
  rw [rank_subgroupOf le_sup_right]
  omega

variable {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]

omit [FiniteDimensional (ZMod 2) V] [Finite G] in
private theorem marked_strong {L : Subgroup G} {σ : Representation (ZMod 2) E W}
    {M : Subgroup E} (e : MarkedActionEquiv ρ ⊤ L σ M)
    {A : Subgroup G} (hA : IsStrongOffender ρ A) :
    let f : G ≃* E := Subgroup.topEquiv.symm.trans e.action.groupEquiv
    IsStrongOffender σ (A.map f.toMonoidHom) ∧
      rank (A.map f.toMonoidHom) = rank A ∧
      fixedCodim σ (A.map f.toMonoidHom) = fixedCodim ρ A := by
  dsimp only
  let f : G ≃* E := Subgroup.topEquiv.symm.trans e.action.groupEquiv
  have hE (g : G) (v : V) : e.action.linearEquiv (ρ g v) =
      σ (f g) (e.action.linearEquiv v) := e.action.intertwines ⟨g, mem_top g⟩ v
  have hc := fixedCodim_map_equivariant ρ σ f.toMonoidHom e.action.linearEquiv hE A
  have hr := rank_map_injective f.toMonoidHom f.injective A
  have he := (IsOffender.map_equivariant ρ σ f.toMonoidHom f.injective
    e.action.linearEquiv hE ⟨hA.1, hA.2.le⟩).1
  exact ⟨⟨he, by rw [← hc, hr]; exact hA.2⟩, hr, hc.symm⟩

open CFSG.Quasithin.ChapterB.Offenders

private theorem numerical (hyp : FFHypothesis K ρ) {L A : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L)
    (hA : IsBestOffender ρ A)
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G))
    (hfix : moved ρ L ≤ fixedSpace ρ (pCore 3 G))
    (m : SymmetricMovedModel ρ L A) :
    (Nonempty (MarkedActionEquiv m.sectionData.space.toRepresentation ⊤
      (L.subgroupOf (L ⊔ A)) (BinaryPermutation.naturalRepresentation (Fin 6))
      (alternatingGroup (Fin 6))) ∨
    Nonempty (MarkedActionEquiv m.sectionData.space.toRepresentation ⊤
      (L.subgroupOf (L ⊔ A)) (BinaryPermutation.coreRepresentation (Fin 6))
      (alternatingGroup (Fin 6)))) ∧
    rank A = 3 ∧
    fixedCodim m.sectionData.space.toRepresentation (A.subgroupOf (L ⊔ A)) = 2 ∧
    fixedCodim (normalMoved ρ (pCore 3 G)).toRepresentation A ≤ 1 := by
  obtain ⟨hs, hb⟩ := component_strong ρ hyp hL d hA hm hfix m
  have hr := rank_subgroupOf (le_sup_right : A ≤ L ⊔ A)
  cases m.action with
  | natural n hn e =>
    obtain ⟨ht, htr, htc⟩ := marked_strong _ e hs
    rcases hn with rfl | rfl
    · have hcon := (Six.isStrongOffender_natural_iff _).mp ht
      have hcr := hcon.rank_eq.trans Six.rank_D
      have hcc := (hcon.fixedCodim_eq _).trans Six.fixedCodim_D.2.2.2
      exact ⟨Or.inl ⟨e⟩, by omega, by omega, by omega⟩
    · exact (Odd.not_isStrongOffender_natural (Or.inr rfl) _ ht).elim
  | coreSix e =>
    obtain ⟨ht, htr, htc⟩ := marked_strong _ e hs
    have hcon := (Six.isStrongOffender_core_iff _).mp ht
    have hcr := hcon.rank_eq.trans Six.rank_D
    have hcc := (hcon.fixedCodim_eq _).trans Six.fixedCodim_D.2.2.1
    exact ⟨Or.inr ⟨e⟩, by omega, by omega, by omega⟩

end Numerical

private theorem cyclic_three_inversion {X : Type*} [Group X] [Finite X] [IsCyclic X]
    (hp : IsPGroup 3 X) (φ : MulAut X) (hφ : Function.Involutive φ)
    (hne : φ ≠ 1) : ∀ x, φ x = x⁻¹ := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := X)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have ho : orderOf x = 3 ^ n := (orderOf_eq_card_of_forall_mem_zpowers hx).trans hn
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hx (φ x))
  have hpow : x ^ (k * k - 1) = 1 := by
    have he : x ^ (k * k) = x := by
      rw [zpow_mul, hk, ← map_zpow, hk, hφ x]
    rw [zpow_sub, he, zpow_one, mul_inv_cancel]
  have hd : (3 : ℤ) ^ n ∣ (k - 1) * (k + 1) := by
    have hh := orderOf_dvd_iff_zpow_eq_one.mpr hpow
    rw [ho, Nat.cast_pow, Nat.cast_ofNat] at hh
    convert hh using 1
    ring
  have hprime : Prime (3 : ℤ) := by norm_num
  have hminus : ¬ (3 : ℤ) ^ n ∣ k - 1 := by
    intro h
    have he : x ^ (k - 1) = 1 := by
      apply orderOf_dvd_iff_zpow_eq_one.mp
      simpa only [ho, Nat.cast_pow, Nat.cast_ofNat] using h
    have hfix : φ x = x := by
      rw [zpow_sub, zpow_one, hk, mul_inv_eq_one] at he
      exact he
    apply hne
    apply MulEquiv.ext
    intro y
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hx y)
    simp only [map_zpow, hfix, MulAut.one_apply]
  have hnminus : ¬ (3 : ℤ) ∣ k - 1 := by
    intro hm
    have hnplus : ¬ (3 : ℤ) ∣ k + 1 := by
      intro hplus
      have hh := dvd_sub hplus hm
      norm_num at hh
    exact hminus (hprime.pow_dvd_of_dvd_mul_right n hnplus hd)
  have hpplus : (3 : ℤ) ^ n ∣ k + 1 :=
    hprime.pow_dvd_of_dvd_mul_left n hnminus hd
  have hinv : φ x = x⁻¹ := by
    have he : x ^ (k + 1) = 1 := by
      apply orderOf_dvd_iff_zpow_eq_one.mp
      simpa only [ho, Nat.cast_pow, Nat.cast_ofNat] using hpplus
    rw [zpow_add, zpow_one, hk] at he
    exact eq_inv_of_mul_eq_one_left he
  intro y
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hx y)
  simp only [map_zpow, hinv, inv_zpow]

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {K : CFSG.Quasithin.GroupClass}

private theorem cyclic_three_plane (hyp : FFHypothesis K ρ) {L A : Subgroup G}
    (d : NoncentralContext K G L) (hA : IsElementaryTwo A)
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G))
    (hc : fixedCodim (normalMoved ρ (pCore 3 G)).toRepresentation A ≤ 1) :
    Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) = 2 := by
  classical
  let := hyp.finite_module
  let : IsCyclic (pCore 3 G) := threeCore_cyclic d
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a, ha, hna⟩ := Set.not_subset.mp hm
  let φ : MulAut (pCore 3 G) := MulAut.conjNormal a
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hi : Function.Involutive φ := by
    have he : φ * φ = 1 := by
      change MulAut.conjNormal a * MulAut.conjNormal a = 1
      rw [← map_mul, ← pow_two, ha2, map_one]
    intro x
    change (φ * φ) x = x
    rw [he]
    rfl
  have hn : φ ≠ 1 := by
    intro he
    apply hna
    intro x hx
    have hh := congrArg (fun f : MulAut (pCore 3 G) => (f ⟨x, hx⟩ : G)) he
    change a * x * a⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := pCore 3 G)
  have hg : zpowers (x : G) = pCore 3 G := by
    have ht : zpowers x = ⊤ := (eq_top_iff' (H := zpowers x)).mpr hx
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype, Subgroup.subtype_apply] using
      congrArg (fun H : Subgroup (pCore 3 G) => H.map (pCore 3 G).subtype) ht
  have hinv : a * (x : G) * a⁻¹ = (x : G)⁻¹ :=
    congrArg Subtype.val (cyclic_three_inversion pCore_isPGroup φ hi hn x)
  have ho : Odd (orderOf (x : G)) := by
    rw [← Nat.card_zpowers, hg]
    exact threeCore_odd
  have hsq : zpowers ((x : G) ^ 2) = pCore 3 G := by
    refine le_antisymm (zpowers_le.mpr ((pCore 3 G).pow_mem x.property 2)) ?_
    exact hg.ge.trans
      (zpowers_le.mpr (mem_zpowers_pow_iff.mpr ho.coprime_two_left.gcd_eq_one))
  have hgen : zpowers (a * (x : G) * a⁻¹ * (x : G)⁻¹) = pCore 3 G := by
    rw [hinv, ← mul_inv_rev, ← pow_two, zpowers_inv, hsq]
  let σ := (normalMoved ρ (pCore 3 G)).toRepresentation
  have hbound := fixedCodim_commutator_le_twice σ a (x : G)
  rw [hgen] at hbound
  have hmono : fixedCodim σ (zpowers a) ≤ fixedCodim σ A := by
    have hspace : fixedSpace σ A ≤ fixedSpace σ (zpowers a) := by
      intro v hv b
      exact hv ⟨b, (zpowers_le.mpr ha) b.property⟩
    have hd := Submodule.finrank_mono hspace
    have h1 := fixedCodim_add_finrank σ A
    have h2 := fixedCodim_add_finrank σ (zpowers a)
    omega
  have hfixed : fixedSpace σ (pCore 3 G) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro v hv
    change v = 0
    apply Subtype.ext
    apply Submodule.disjoint_def.mp (odd_moved_complement ρ (pCore 3 G) threeCore_odd).disjoint
      (v : V) v.property
    intro y
    exact congrArg Subtype.val (hv y)
  have hd := fixedCodim_add_finrank σ (pCore 3 G)
  rw [hfixed, finrank_bot, add_zero] at hd
  change _ = Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) at hd
  have hu : Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) ≤ 2 := by
    change fixedCodim σ A ≤ 1 at hc
    omega
  have hdiv := Representation.card_dvd_card_GL_of_injective
    ((normalMoved ρ (pCore 3 G)).toRepresentation.comp (pCore 3 G).subtype)
    (threeCore_moved_faithful ρ hyp)
  change Nat.card (pCore 3 G) ∣ Nat.card
    (Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 2) (moved ρ (pCore 3 G)))) (ZMod 2)) at hdiv
  interval_cases he : Module.finrank (ZMod 2) (moved ρ (pCore 3 G))
  · norm_num [he, Matrix.card_GL_field, Fin.prod_univ_succ] at hdiv
    exact (d.noncentral (hdiv ▸ bot_le)).elim
  · rw [Matrix.card_GL_field] at hdiv
    norm_num [Fin.prod_univ_succ] at hdiv
    exact (d.noncentral (hdiv ▸ bot_le)).elim
  · rfl

end SourceEndgame

/-- B.5.7's offender endgame on the original component and three-core. The
parent supplies the crossed fixation from the marked model commutant; every
numerical assertion and both actual group equivalences are derived here. -/
theorem source_offender_plane
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {K : GroupClass} (ρ : Representation (ZMod 2) G V)
    (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (hL : IsComponent G L) (d : NoncentralContext K G L)
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G))
    (hfix : moved ρ L ≤ fixedSpace ρ (pCore 3 G))
    (m : SymmetricMovedModel ρ L A) :
    OffenderPlaneConclusion ρ d m := by
  let := hyp.finite_module
  obtain ⟨marking, hrank, hcodim, hcubic⟩ :=
    SourceEndgame.numerical ρ hyp hL d hA hm hfix m
  have hplane := SourceEndgame.cyclic_three_plane ρ hyp d hA.1 hm hcubic
  refine {
    marking := marking
    componentEquiv := ?_
    plane := hplane
    threeCoreEquiv := ⟨threeCoreEquiv_of_plane ρ hyp d hplane⟩
    rank_eq := hrank
    component_fixedCodim_eq := hcodim }
  rcases marking with h | h
  all_goals
    obtain ⟨e⟩ := h
    exact ⟨(subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).symm.trans e.subgroupEquiv⟩

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
