module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.SmallCentralizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.InvolutionGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.Frattini
public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# The actual core quotient and its small critical displacement

The local commutator containment [core,Q] ≤ U makes core/U abelian.
Critical-pair involution generation makes this quotient elementary abelian.
Conjugation descends through the specified SL3(2) projection; residual
commutator idempotence and the non-Frattini premise make it faithful and
fully moving. The natural marking of U gives |core| = 8 |core/U|.

At a critical endpoint v, D = [core,Z_v] has order at most four. Its
intersection with U contains the nontrivial [U,Z_v]: triviality would
contradict critical-pair reversal and faithfulness of the natural action
on U. Therefore D has image of order at most two in core/U. Any element
of Z_v outside Q gives the required nonidentity involution in SL3(2).
No commutativity of core or stronger conjugate-generation identity is used.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), natural branch of (3.6), printed pp.870--871, using the critical
local commutators from (3.3)--(3.5). The containment [core,Q] ≤ U remains
an explicit premise, discharged by the independent commutator argument.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.QuotientOrder
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

instance layer_normal : ((U R (alpha R)).subgroupOf (core R (alpha R))).Normal :=
  U_subgroupOf_core_normal (alpha R) rfl

abbrev Factor (R : Subgroup M) :=
  core R (alpha R) ⧸ (U R (alpha R)).subgroupOf (core R (alpha R))

instance factor_finite : Finite (Factor R) := by
  let := finite_core (R := R) (alpha R)
  exact Quotient.finite _

theorem factor_elementary (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (hcomm : ⁅core R (alpha R), Q R (alpha R)⁆ ≤ U R (alpha R)) :
    IsElementaryAbelian 2 (Factor R) := by
  let C := core R (alpha R)
  let N := (U R (alpha R)).subgroupOf C
  let q : C →* Factor R := QuotientGroup.mk' N
  have hderived : _root_.commutator C ≤ N := by
    intro x hx
    have hh := mem_map_of_mem C.subtype hx
    rw [map_subtype_commutator] at hh
    exact hcomm (commutator_mono le_rfl (core_le_Q (alpha R)) hh)
  let : IsMulCommutative (Factor R) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hderived
  have hpow (x : C) : q x ^ 2 = 1 := by
    have hx : x ∈ closure {x : C | x ^ 2 = 1} :=
      (involution_generation source geometry hb).symm ▸ mem_top x
    induction hx using closure_induction with
    | mem y hy => rw [← map_pow, hy, map_one]
    | one => simp
    | mul y z _ _ hy hz => rw [map_mul, mul_pow, hy, hz, one_mul]
    | inv y _ hy => rw [map_inv, inv_pow, hy, inv_one]
  exact { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact hpow y) }

omit [Finite M] in
theorem core_card_eq (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection) :
    Nat.card (core R (alpha R)) = 8 * Nat.card (Factor R) := by
  let N := (U R (alpha R)).subgroupOf (core R (alpha R))
  have hN : Nat.card N = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (U_le_core geometry (by omega) (alpha R) rfl)).toEquiv).trans natural.card
  have h := N.card_mul_index
  rw [hN, index_eq_card] at h
  exact h.symm

theorem exists_faithful_full_action (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    (hcomm : ⁅core R (alpha R), Q R (alpha R)⁆ ≤ U R (alpha R)) :
    ∃ a : SL →* MulAut (Factor R),
      Function.Injective a ∧ commutatorAction a.range (Factor R) = ⊤ ∧
      ∀ (m : M) (x y : core R (alpha R)),
        (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
        a (source.projection m) (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ y := by
  let C := core R (alpha R)
  let N := (U R (alpha R)).subgroupOf C
  let P := Mbar R
  have hPC : P ≤ normalizer C := by
    simpa only [P, C, alpha, stabilizer_m_base] using core_normalized (R := R) (alpha R)
  have hLP : Ltilde R (alpha R) ≤ P := by
    change Ltilde R (alpha R) ≤ Mbar R
    rw [← stabilizer_m_base]
    exact Ltilde_le_stabilizer _
  obtain ⟨a, ha, hkillQ, hfull⟩ := exists_quotient_conjugation_full_action
    P C (U R (alpha R)) (Ltilde R (alpha R)) (Q R (alpha R))
    hPC natural.normalized inferInstance hLP
    (source.core_full_commutation (alpha R) rfl) hcomm
  let i : M →* P := (embedM R).rangeRestrict
  let aM := a.comp i
  have hkill : source.projection.ker ≤ aM.ker := by
    intro m hm
    apply hkillQ
    change embedM R m ∈ Q R (alpha R)
    rw [Q_alpha R source.two_group source.core_le]
    exact mem_map_of_mem _ (source.projection_kernel ▸ hm)
  let aSL : SL →* MulAut (Factor R) := source.projection.liftOfSurjective
    source.projection_surjective ⟨aM, hkill⟩
  have haSL (m : M) : aSL (source.projection m) = aM m :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hact (m : M) (x y : C)
      (hy : (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹) :
      aSL (source.projection m) (QuotientGroup.mk' N x) = QuotientGroup.mk' N y := by
    rw [haSL]
    change a (i m) _ = _
    rw [ha]
    congr 1
    exact Subtype.ext hy.symm
  have hinj : Function.Injective aSL := by
    let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
    apply aSL.ker_eq_bot_iff.mp
    rcases (inferInstance : aSL.ker.Normal).eq_bot_or_eq_top with hk | hk
    · exact hk
    exfalso
    have htriv (m : M) : a (i m) = 1 := by
      rw [← show aM m = a (i m) from rfl, ← haSL]
      exact (show source.projection m ∈ aSL.ker from hk.symm ▸ mem_top _)
    have hCU : C ≤ U R (alpha R) := by
      change core R (alpha R) ≤ _
      rw [← source.core_full_commutation (alpha R) rfl, commutator_comm]
      apply commutator_le.mpr
      intro l hl x hx
      have hlM : l ∈ Mbar R := by
        rw [← stabilizer_m_base R]
        exact map_subtype_le _ hl
      obtain ⟨m, rfl⟩ := hlM
      have hh := ha (i m) ⟨x, hx⟩
      rw [htriv] at hh
      have hmem := QuotientGroup.eq_iff_div_mem.mp hh.symm
      change embedM R m * x * (embedM R m)⁻¹ / x ∈ U R (alpha R) at hmem
      simpa only [commutatorElement_def, div_eq_mul_inv] using hmem
    exact hlarge (hCU.trans ((U_le_Z _).trans
      ((geometry.omega_bound (alpha R) rfl (by change 0 < geometry.b R; omega)).trans
        le_sup_right)))
  refine ⟨aSL, hinj, ?_, hact⟩
  apply top_unique
  rw [← hfull]
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  apply Subgroup.closure_mono
  rintro x ⟨⟨g, hg⟩, y, rfl⟩
  obtain ⟨p, _, rfl⟩ := hg
  obtain ⟨m, hm⟩ := p.property
  have hip : i m = p := Subtype.ext hm
  refine ⟨⟨a p, ?_⟩, y, rfl⟩
  exact ⟨source.projection m, (haSL m).trans (congrArg a hip)⟩

private theorem cyclic_commutator_le {E : Type*} [Group E]
    (g : MulAut E) (H : Subgroup E) (h : ∀ x, x⁻¹ * g x ∈ H) :
    commutatorAction (zpowers g) E ≤ H := by
  let B : Subgroup (MulAut E) := {
    carrier := {a | ∀ x, x⁻¹ * a x ∈ H}
    one_mem' := by intro x; simp
    mul_mem' := by
      intro a b ha hb x
      have hh := H.mul_mem (hb x) (ha (b x))
      simpa only [mul_assoc, mul_inv_cancel_left, MulAut.mul_apply] using hh
    inv_mem' := by
      intro a ha x
      have hh := H.inv_mem (ha (a⁻¹ x))
      simpa only [MulAut.apply_inv_self, mul_inv_rev, inv_inv] using hh }
  have hB : zpowers g ≤ B := zpowers_le.mpr h
  rw [commutatorAction_eq_closure]
  apply (closure_le _).mpr
  rintro x ⟨a, y, rfl⟩
  exact hB a.property y

theorem exists_small_displacement (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (a : SL →* MulAut (Factor R))
    (hact : ∀ (m : M) (x y : core R (alpha R)),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      a (source.projection m) (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ y) :
    ∃ t : SL, t ^ 2 = 1 ∧ t ≠ 1 ∧
      Nat.card (commutatorAction (zpowers (a t)) (Factor R)) ≤ 2 := by
  obtain ⟨v, e, hc, hae, hve⟩ := critical_edge_exists geometry hb
  have hv := critical_endpoint_color R (alpha R) rfl _ hc
  have hreverse := source.critical_reverse geometry (alpha R) rfl v hv hc
  have hvS := (source.critical_Z_le_stabilizer geometry (alpha R) rfl v hc).2
  have hUZ : ⁅U R (alpha R), Z R v⁆ ≠ ⊥ := by
    intro hzero
    apply hreverse.2
    rw [← natural.centralizer_alpha]
    exact le_inf hvS (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hzero))
  let C := core R (alpha R)
  let N := (U R (alpha R)).subgroupOf C
  let q : C →* Factor R := QuotientGroup.mk' N
  let D := ⁅C, Z R v⁆
  have hDC : D ≤ C := critical_core_commutator_le_core source geometry hc
  let f : D →* Factor R := q.comp (inclusion hDC)
  have hcard : Nat.card D ≤ 4 :=
    critical_core_commutator_card_le_four source geometry natural hc hae hve
  let : Finite C := finite_core (alpha R)
  let : Finite D := Finite.of_injective (inclusion hDC) (inclusion_injective hDC)
  have hker : f.ker ≠ ⊥ := by
    have hnle : ¬ ⁅U R (alpha R), Z R v⁆ ≤ ⊥ := fun h => hUZ (bot_unique h)
    obtain ⟨w, hw, hwn⟩ := Set.not_subset.mp hnle
    have hwne : w ≠ 1 := fun he => hwn (he.symm ▸ one_mem _)
    have hwD : w ∈ D := commutator_mono
      (U_le_core geometry (by omega) (alpha R) rfl) le_rfl hw
    have hwU : w ∈ U R (alpha R) :=
      le_normalizer_iff_commutator_le_left.mp (hvS.trans (U_normalized (alpha R))) hw
    have hwker : (⟨w, hwD⟩ : D) ∈ f.ker := by
      change q (inclusion hDC ⟨w, hwD⟩) = 1
      exact (QuotientGroup.eq_one_iff _).mpr hwU
    intro hbot
    have heq := mem_bot.mp (hbot ▸ hwker)
    exact hwne (congrArg Subtype.val heq)
  have himage : Nat.card f.range ≤ 2 := by
    have hk := (one_lt_card_iff_ne_bot f.ker).mpr hker
    have hprod := f.ker.card_mul_index
    rw [index_ker] at hprod
    nlinarith
  obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp hreverse.2
  have hzM : z ∈ Mbar R := (stabilizer_m_base R) ▸ hvS hz
  obtain ⟨m, rfl⟩ := hzM
  have hmQ : source.projection m ≠ 1 := by
    intro hm
    apply hzQ
    rw [Q_alpha R source.two_group source.core_le]
    exact mem_map_of_mem _ (source.projection_kernel ▸ hm)
  have hm2 : m ^ 2 = 1 := by
    apply embedM_injective R
    rw [map_pow, map_one]
    exact (mem_omegaCenter_iff.mp (geometry.omega_bound v hv (by
      rw [geometry.distance_constant v hv]
      change 0 < geometry.b R
      omega) hz)).2.1
  refine ⟨source.projection m, by rw [← map_pow, hm2, map_one], hmQ, ?_⟩
  have hle : commutatorAction (zpowers (a (source.projection m))) (Factor R) ≤
      f.range := by
    apply cyclic_commutator_le
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    let y' : C := ⟨embedM R m * y * (embedM R m)⁻¹,
      le_normalizer_iff.mp (core_normalized (alpha R)) _ (hvS hz) _ y.property⟩
    rw [hact m y y' rfl, ← map_inv, ← map_mul]
    have hd : ((y⁻¹ * y' : C) : FreeAmalgam R) ∈ D := by
      have hh := commutator_mem_commutator (C.inv_mem y.property) hz
      simpa only [y', Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def,
        inv_inv, mul_assoc] using hh
    refine ⟨⟨_, hd⟩, ?_⟩
    rfl
  exact (card_le_of_le hle).trans himage

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.QuotientOrder
