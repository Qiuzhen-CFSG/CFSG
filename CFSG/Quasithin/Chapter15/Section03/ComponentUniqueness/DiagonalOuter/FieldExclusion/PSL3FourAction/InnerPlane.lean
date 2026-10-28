module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.PSL3FourAction.Descent
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.PSL3FourAction.FixedIndex
public import Theory.SpecificGroups.PSL3Four.InnerInvolutionCentralizers
public import Theory.SpecificGroups.PSL3Four.InnerFixedCoverSize

/-!
# The inner-actor case for central covers of PSL₃(4)

Let a TI four-group act faithfully on a perfect central cover of PSL₃(4),
with a nonidentity inner actor a. Write H for the inner image of the full
fixed subgroup and C for the inner image of the a-fixed subgroup. The TI
index bound gives |C:H| ≤ 2. Once the projective involution centralizer is
a two-group, so are C and H. In any compatible action image D, H is normal,
so O₃(D) centralizes H. A cubic automorphism of a two-group with fixed
subgroup of index at most two is trivial, by orbit counting modulo three.
Thus each cubic element of O₃(D) centralizes all of C.

Faithful descent now reduces the remaining rigidity step to two cardinal
bounds: the actual lifted fixed inner image has order greater than four,
and the common inner centralizer of an inner involution and a commuting
nonidentity cubic automorphism downstairs has order at most four.
`contradiction_of_inner_bounds` applies this reduction to the actual joint
residual and the complete component-centralizer alternative.

`threeCoreFreeAction_of_inner` discharges all three bounds using the actual
projective involution and cubic centralizer calculations and the square-root
lifting bound for central covers. `contradiction_of_inner` completes the
inner-actor branch for the E₉ joint residual. The lifted fixed subgroup is
never identified with the whole projective fixed subgroup. The center is
unrestricted, retaining genuine central covers and the exceptional SL₃(4)
branch.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137 (PDF p.1154). `JointCentralizer` explains the correction
from the printed order-27 residual to the actual E₉ joint residual used here.
The concrete calculations and their sources are in the two imported model
modules; the square-root lifting proof applies to all central covers directly.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3FourAction.InnerPlane

private theorem cube_fixed_index {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (b : MulAut P) (hb : b ^ 3 = 1)
    (hi : b.fixedSubgroup.index ≤ 2) : b = 1 := by
  let B := zpowers b
  have hp : IsPGroup 3 B := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [B, Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hb)
  have hfixed : FixedPoints.subgroup B P = b.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup b x).mpr (hx ⟨b, mem_zpowers b⟩)
    · intro hx
      have hle : B ≤ MulAction.stabilizer (MulAut P) x :=
        zpowers_le.mpr ((MulAut.mem_fixedSubgroup b x).mp hx)
      exact fun c => hle c.property
  have hmod := hp.card_modEq_card_fixedPoints P
  change Nat.card P % 3 = Nat.card (FixedPoints.subgroup B P) % 3 at hmod
  rw [hfixed] at hmod
  have hpos := b.fixedSubgroup.index_ne_zero_of_finite
  have hcount := b.fixedSubgroup.index_mul_card
  have hnot : ¬ 3 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := hP.exists_card_dvd_pow
    intro hd
    have := hd.trans hn
    have hd2 : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow this
    norm_num at hd2
  have hi1 : b.fixedSubgroup.index = 1 := by
    have hnmod := mt Nat.dvd_of_mod_eq_zero hnot
    have hi12 : b.fixedSubgroup.index = 1 ∨ b.fixedSubgroup.index = 2 := by omega
    rcases hi12 with h | h
    · exact h
    · rw [h] at hcount
      omega
  have ht := index_eq_one.mp hi1
  ext x
  exact (MulAut.mem_fixedSubgroup b x).mp (ht ▸ mem_top x)

private theorem map_relIndex_le {P Q : Type*} [Group P] [Finite P] [Group Q]
    (f : P →* Q) (H C : Subgroup P) :
    (H.map f).relIndex (C.map f) ≤ H.relIndex C := by
  rw [← relIndex_comap]
  exact relIndex_le_of_le_left (le_comap_map f H) (H.subgroupOf C).index_ne_zero_of_finite

private theorem conj_conj {P : Type*} [Group P] (b : MulAut P) (x : P) :
    MulAut.conj (b x) = b * MulAut.conj x * b⁻¹ := by
  ext y
  simp

private theorem inner_fixed_normalized {A P : Type*} [Group A] [Group P]
    (φ : A →* MulAut P) (b : MulAut P) (hb : ∀ a, Commute b (φ a)) :
    b ∈ normalizer ((fixedSubgroupOfAction φ).map (MulAut.conj : P →* MulAut P) :
      Set (MulAut P)) := by
  apply mem_normalizer_iff.mpr
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨b x, ?_, (conj_conj b x)⟩
    intro a
    have he := MulEquiv.congr_fun (hb a).eq x
    change b (φ a x) = φ a (b x) at he
    rw [hx a] at he
    exact he.symm
  · intro hy
    obtain ⟨x, hx, he⟩ := hy
    refine ⟨b⁻¹ x, ?_, ?_⟩
    · intro a
      apply b.injective
      have hc := MulEquiv.congr_fun (hb a).eq (b⁻¹ x)
      change b (φ a (b⁻¹ x)) = φ a (b (b⁻¹ x)) at hc
      simpa only [MulAut.apply_inv_self, hx a] using hc
    · have hc := conj_conj b (b⁻¹ x)
      simp only [MulAut.apply_inv_self] at hc
      apply_fun (fun z : MulAut P => b⁻¹ * z * b) at hc he
      simpa only [inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using hc.symm.trans he

private theorem inner_element_fixed_normalized {P : Type*} [Group P]
    (a b : MulAut P) (hb : Commute b a) :
    b ∈ normalizer (a.fixedSubgroup.map (MulAut.conj : P →* MulAut P) :
      Set (MulAut P)) := by
  let φ : zpowers a →* MulAut P := (zpowers a).subtype
  have he : fixedSubgroupOfAction φ = a.fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup a x).mpr (hx ⟨a, mem_zpowers a⟩)
    · intro hx
      have hle : zpowers a ≤ MulAction.stabilizer (MulAut P) x :=
        zpowers_le.mpr ((MulAut.mem_fixedSubgroup a x).mp hx)
      exact fun c => hle c.property
  rw [← he]
  apply inner_fixed_normalized φ b
  rintro ⟨c, hc⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc
  exact hb.zpow_right n

/-- An automorphism of order three centralizing the inner image of an
index-at-most-two subgroup of a two-group centralizes the whole two-group. -/
private theorem commute_of_cube_of_index {P : Type*} [Group P] [Finite P]
    (H C : Subgroup P) (hC : IsPGroup 2 C)
    (hi : H.relIndex C ≤ 2) (b : P) (hb : b ^ 3 = 1)
    (hbN : b ∈ normalizer (C : Set P))
    (hfix : ∀ x ∈ H, Commute b x) : ∀ x ∈ C, Commute b x := by
  let n : normalizer (C : Set P) := ⟨b, hbN⟩
  let β := C.normalizerMonoidHom n
  have hn : n ^ 3 = 1 := Subtype.ext hb
  have hβ : β ^ 3 = 1 := by rw [← map_pow, hn, map_one]
  have hle : H.subgroupOf C ≤ β.fixedSubgroup := by
    intro x hx
    apply (MulAut.mem_fixedSubgroup β x).mpr
    apply Subtype.ext
    change b * (x : P) * b⁻¹ = (x : P)
    rw [(hfix x hx).eq, mul_inv_cancel_right]
  have hiβ : β.fixedSubgroup.index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (H.subgroupOf C).index_ne_zero_of_finite)
      (index_dvd_of_le hle)).trans hi
  have he := cube_fixed_index hC β hβ hiβ
  intro x hx
  have he' := congrArg Subtype.val (MulEquiv.congr_fun he ⟨x, hx⟩)
  change b * x * b⁻¹ = x at he'
  exact mul_inv_eq_iff_eq_mul.mp he'


/-- The inner image of a lifted involution centralizer is a two-group
when the corresponding projective inner involution centralizer is one.
Only containment of the actual image is used. -/
theorem inner_fixed_isTwoGroup {K : Type*} [Group K] [Group.IsPerfect K]
    (eK : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (a : MulAut K) (ha : a ∈ MulAut.innerSubgroup K)
    (hne : a ≠ 1) (hsq : a ^ 2 = 1)
    (hmodel : ∀ t : MulAut Matrix.PSL3Four.PSL,
      t ∈ MulAut.innerSubgroup Matrix.PSL3Four.PSL → t ≠ 1 → t ^ 2 = 1 →
      IsPGroup 2 ↥(MulAut.innerSubgroup Matrix.PSL3Four.PSL ⊓
        centralizer ({t} : Set (MulAut Matrix.PSL3Four.PSL)))) :
    IsPGroup 2 (a.fixedSubgroup.map (MulAut.conj : K →* MulAut K)) := by
  let d := projectiveAutMap eK
  let C := a.fixedSubgroup.map (MulAut.conj : K →* MulAut K)
  have hd : Function.Injective d := projectiveAutMap_injective eK
  have hda : d a ∈ MulAut.innerSubgroup Matrix.PSL3Four.PSL :=
    (projectiveAutMap_mem_inner_iff eK a).mpr ha
  have hdn : d a ≠ 1 := fun h => hne (hd (h.trans (map_one d).symm))
  have hds : (d a) ^ 2 = 1 := by rw [← map_pow, hsq, map_one]
  have hle : C.map d ≤ MulAut.innerSubgroup Matrix.PSL3Four.PSL ⊓
      centralizer ({d a} : Set (MulAut Matrix.PSL3Four.PSL)) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    constructor
    · exact (projectiveAutMap_mem_inner_iff eK _).mpr ⟨x, rfl⟩
    · apply mem_centralizer_singleton_iff.mpr
      have hc : a * MulAut.conj x * a⁻¹ = MulAut.conj x := by
        rw [← conj_conj, (MulAut.mem_fixedSubgroup a x).mp hx]
      have he := congrArg d (mul_inv_eq_iff_eq_mul.mp hc).symm
      simpa only [map_mul] using he
  have hp := (hmodel (d a) hda hdn hds).of_injective
    (inclusion hle) (inclusion_injective hle)
  exact hp.of_equiv (C.equivMapOfInjective d hd).symm

/-- The TI index constraint reduces the inner-actor case to two intrinsic
model calculations. Neither calculation is asserted by this theorem. -/
theorem threeCoreFreeAction_of_inner_calculations
    {A K : Type*} [Group A] [IsKleinFour A] [Group K] [Finite K] [Group.IsPerfect K]
    (eK : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (φ : A →* MulAut K) (hφ : Function.Injective φ)
    (hcontrol : FixedCentralizerControl φ)
    (hinner : ∃ a : A, a ≠ 1 ∧ φ a ∈ MulAut.innerSubgroup K)
    (htwo : ∀ t : MulAut Matrix.PSL3Four.PSL,
      t ∈ MulAut.innerSubgroup Matrix.PSL3Four.PSL → t ≠ 1 → t ^ 2 = 1 →
      IsPGroup 2 ↥(MulAut.innerSubgroup Matrix.PSL3Four.PSL ⊓
        centralizer ({t} : Set (MulAut Matrix.PSL3Four.PSL))))
    (hrigid : ∀ a b : MulAut K, a ∈ MulAut.innerSubgroup K → a ≠ 1 → a ^ 2 = 1 →
      b ^ 3 = 1 → Commute b a →
      (∀ x ∈ a.fixedSubgroup, Commute b (MulAut.conj x)) → b = 1) :
    ThreeCoreFreeAction φ := by
  obtain ⟨u, hu, hui⟩ := hinner
  have hun : φ u ≠ 1 := fun he => hu (hφ (he.trans (map_one φ).symm))
  have hu2 : (φ u) ^ 2 = 1 := by
    rw [← map_pow, pow_two, IsKleinFour.mul_self, map_one]
  let H := (fixedSubgroupOfAction φ).map (MulAut.conj : K →* MulAut K)
  let C := (φ u).fixedSubgroup.map (MulAut.conj : K →* MulAut K)
  have hHC : H ≤ C := map_mono (by
    intro x hx
    exact (MulAut.mem_fixedSubgroup (φ u) x).mpr (hx u))
  have hCtwo : IsPGroup 2 C := inner_fixed_isTwoGroup eK (φ u) hui hun hu2 htwo
  have helem : elementFixedSubgroup φ u = (φ u).fixedSubgroup := by
    ext x
    exact (MulAut.mem_fixedSubgroup (φ u) x).symm
  have hi : H.relIndex C ≤ 2 :=
    (map_relIndex_le (MulAut.conj : K →* MulAut K) _ _).trans
      (by simpa only [helem] using (hcontrol u hu).2)
  intro D hD hHD
  have hcomm (b : D) (a : A) : Commute (b : MulAut K) (φ a) :=
    (hD b.property (φ a) ⟨a, rfl⟩).symm
  have hHD' : H ≤ D := hHD
  let H₀ := H.subgroupOf D
  have hHnormal : H₀.Normal := (normal_subgroupOf_iff_le_normalizer hHD').mpr (by
    intro b hb
    exact inner_fixed_normalized φ b (hcomm ⟨b, hb⟩))
  let := hHnormal
  have hHtwo : IsPGroup 2 H₀ :=
    hCtwo.of_injective ((inclusion hHC).comp (subgroupOfEquivOfLe hHD').toMonoidHom)
      ((inclusion_injective hHC).comp (subgroupOfEquivOfLe hHD').injective)
  have hdis : Disjoint (pCore 3 D) H₀ :=
    IsPGroup.disjoint_of_coprime pCore_isPGroup hHtwo (by decide)
  have hcentral : pCore 3 D ≤ centralizer (H₀ : Set D) :=
    commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdis)
  rcases (pCore_isPGroup (p := 3) (G := D)).card_eq_or_dvd with hone | hdiv
  · exact (pCore 3 D).eq_bot_of_card_eq hone
  · obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := pCore 3 D) 3 hdiv
    have hb3 : (((b : pCore 3 D) : D) : MulAut K) ^ 3 = 1 := by
      exact congrArg (fun x : pCore 3 D => ((x : D) : MulAut K))
        (by simpa only [hb] using pow_orderOf_eq_one b)
    have hfix : ∀ x ∈ H, Commute (((b : pCore 3 D) : D) : MulAut K) x := by
      intro x hx
      exact congrArg Subtype.val (hcentral b.property ⟨x, hHD' hx⟩ hx).symm
    have hbC := inner_element_fixed_normalized (φ u) (b : D) (hcomm b u)
    have hfixC := commute_of_cube_of_index H C hCtwo hi (b : D) hb3 hbC hfix
    have hb1 := hrigid (φ u) (b : D) hui hun hu2 hb3 (hcomm b u)
      (fun x hx => hfixC _ (mem_map_of_mem MulAut.conj hx))
    have hb1' : b = 1 := Subtype.ext (Subtype.ext hb1)
    have : orderOf b = 1 := by rw [hb1', orderOf_one]
    omega

/-- A lower bound for the actual lifted fixed inner image combines with a
projective common-centralizer bound to give cubic rigidity. -/
theorem inner_rigidity_of_card_bounds
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (eK : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (hsmall : ∀ t b : MulAut Matrix.PSL3Four.PSL,
      t ∈ MulAut.innerSubgroup Matrix.PSL3Four.PSL → t ≠ 1 → t ^ 2 = 1 →
      b ≠ 1 → b ^ 3 = 1 → Commute b t →
      Nat.card ↥(MulAut.innerSubgroup Matrix.PSL3Four.PSL ⊓
        centralizer ({t} : Set (MulAut Matrix.PSL3Four.PSL)) ⊓
        centralizer ({b} : Set (MulAut Matrix.PSL3Four.PSL))) ≤ 4)
    (hlarge : ∀ a : MulAut K, a ∈ MulAut.innerSubgroup K → a ≠ 1 → a ^ 2 = 1 →
      4 < Nat.card (a.fixedSubgroup.map (MulAut.conj : K →* MulAut K)))
    (a b : MulAut K) (ha : a ∈ MulAut.innerSubgroup K) (ha1 : a ≠ 1)
    (ha2 : a ^ 2 = 1) (hb3 : b ^ 3 = 1) (hba : Commute b a)
    (hfix : ∀ x ∈ a.fixedSubgroup, Commute b (MulAut.conj x)) : b = 1 := by
  by_contra hb1
  let d := projectiveAutMap eK
  let C := a.fixedSubgroup.map (MulAut.conj : K →* MulAut K)
  have hd : Function.Injective d := projectiveAutMap_injective eK
  have hda : d a ∈ MulAut.innerSubgroup Matrix.PSL3Four.PSL :=
    (projectiveAutMap_mem_inner_iff eK a).mpr ha
  have hda1 : d a ≠ 1 := fun h => ha1 (hd (h.trans (map_one d).symm))
  have hdb1 : d b ≠ 1 := fun h => hb1 (hd (h.trans (map_one d).symm))
  have hda2 : (d a) ^ 2 = 1 := by rw [← map_pow, ha2, map_one]
  have hdb3 : (d b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hdbda : Commute (d b) (d a) := hba.map d
  have hle : C.map d ≤ MulAut.innerSubgroup Matrix.PSL3Four.PSL ⊓
      centralizer ({d a} : Set (MulAut Matrix.PSL3Four.PSL)) ⊓
      centralizer ({d b} : Set (MulAut Matrix.PSL3Four.PSL)) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨⟨(projectiveAutMap_mem_inner_iff eK _).mpr ⟨x, rfl⟩, ?_⟩, ?_⟩
    · apply mem_centralizer_singleton_iff.mpr
      have hc : a * MulAut.conj x * a⁻¹ = MulAut.conj x := by
        rw [← conj_conj, (MulAut.mem_fixedSubgroup a x).mp hx]
      simpa only [map_mul] using congrArg d (mul_inv_eq_iff_eq_mul.mp hc).symm
    · apply mem_centralizer_singleton_iff.mpr
      exact ((hfix x hx).map d).eq.symm
  have hcard := (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)).trans
    (hsmall (d a) (d b) hda hda1 hda2 hdb1 hdb3 hdbda)
  rw [Subgroup.card_map_of_injective hd] at hcard
  exact (not_lt_of_ge hcard) (hlarge a ha ha1 ha2)

/-- Conditional assembly of the actual inner-actor branch. The two projective
bounds and the lifted fixed-image bound remain explicit model obligations. -/
theorem contradiction_of_inner_bounds
    {G : Type*} [Group G] [Finite G]
    (U K : Subgroup G) [IsKleinFour U] [IsQuasisimple K] (f : G)
    (hTI : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U)
    (hKf : K ≤ centralizer ({f} : Set G))
    (hn : (K.subgroupOf (centralizer ({f} : Set G))).Normal)
    (hUf : U ≤ centralizer ({f} : Set G))
    (eK : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (eR : jointResidual U f ≃* ElementaryNine)
    (hC : FieldComponentCentralizerAlternative (centralizer ({f} : Set G)) K)
    (hinner : let hUN := hUf.trans ((normal_subgroupOf_iff_le_normalizer hKf).mp hn)
      ∃ u : U, u ≠ 1 ∧
        (K.normalizerMonoidHom.comp (inclusion hUN)) u ∈ MulAut.innerSubgroup K)
    (htwo : ∀ t : MulAut Matrix.PSL3Four.PSL,
      t ∈ MulAut.innerSubgroup Matrix.PSL3Four.PSL → t ≠ 1 → t ^ 2 = 1 →
      IsPGroup 2 ↥(MulAut.innerSubgroup Matrix.PSL3Four.PSL ⊓
        centralizer ({t} : Set (MulAut Matrix.PSL3Four.PSL))))
    (hsmall : ∀ t b : MulAut Matrix.PSL3Four.PSL,
      t ∈ MulAut.innerSubgroup Matrix.PSL3Four.PSL → t ≠ 1 → t ^ 2 = 1 →
      b ≠ 1 → b ^ 3 = 1 → Commute b t →
      Nat.card ↥(MulAut.innerSubgroup Matrix.PSL3Four.PSL ⊓
        centralizer ({t} : Set (MulAut Matrix.PSL3Four.PSL)) ⊓
        centralizer ({b} : Set (MulAut Matrix.PSL3Four.PSL))) ≤ 4)
    (hlarge : ∀ a : MulAut K, a ∈ MulAut.innerSubgroup K → a ≠ 1 → a ^ 2 = 1 →
      4 < Nat.card (a.fixedSubgroup.map (MulAut.conj : K →* MulAut K))) : False := by
  let hUN := hUf.trans ((normal_subgroupOf_iff_le_normalizer hKf).mp hn)
  have hJN : jointCentralizer U f ≤ normalizer (K : Set G) :=
    inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer hKf).mp hn)
  let φ := K.normalizerMonoidHom.comp (inclusion hUN)
  have hfree : ThreeCoreFreeAction φ :=
    threeCoreFreeAction_of_inner_calculations eK φ
      (faithful_action_of_jointResidual_model U K f hTI hKf hUN eR)
      (conjugation_fixedCentralizerControl U K hTI hUN) hinner htwo
      (inner_rigidity_of_card_bounds eK hsmall hlarge)
  exact jointResidual_contradiction_of_threeCore U K f eR hJN
    (hfree _ (jointAction_range_le_centralizer U K f hUN hJN)
      (fixed_inner_le_jointAction_range U K f hKf hUN hJN)) hC

/-- A faithful four-group action with the TI fixed-centralizer constraint and
a nonidentity inner actor has trivial three-core in every compatible action
image. All projective and central-cover model bounds are discharged. -/
theorem threeCoreFreeAction_of_inner
    {A K : Type*} [Group A] [IsKleinFour A] [Group K] [Finite K] [Group.IsPerfect K]
    (eK : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (φ : A →* MulAut K) (hφ : Function.Injective φ)
    (hcontrol : FixedCentralizerControl φ)
    (hinner : ∃ a : A, a ≠ 1 ∧ φ a ∈ MulAut.innerSubgroup K) :
    ThreeCoreFreeAction φ := by
  apply threeCoreFreeAction_of_inner_calculations eK φ hφ hcontrol hinner
    Matrix.PSL3Four.InnerInvolutionCentralizers.innerCentralizer_isTwoGroup
  exact inner_rigidity_of_card_bounds eK
    Matrix.PSL3Four.InnerInvolutionCentralizers.card_commonCentralizer_le
    (fun a ha _ ha2 =>
      Matrix.PSL3Four.InnerFixedCoverSize.four_lt_card_inner_fixed_image eK a ha ha2)

/-- The actual TI-plane action on a quasisimple cover of PSL₃(4) cannot contain
a nonidentity inner actor when the joint residual is E₉ and the complete
component-centralizer alternative holds. Normality is relative to C_G(f),
and no further model or lifting hypotheses are required. -/
theorem contradiction_of_inner
    {G : Type*} [Group G] [Finite G]
    (U K : Subgroup G) [IsKleinFour U] [IsQuasisimple K] (f : G)
    (hTI : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U)
    (hKf : K ≤ centralizer ({f} : Set G))
    (hn : (K.subgroupOf (centralizer ({f} : Set G))).Normal)
    (hUf : U ≤ centralizer ({f} : Set G))
    (eK : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL)
    (eR : jointResidual U f ≃* ElementaryNine)
    (hC : FieldComponentCentralizerAlternative (centralizer ({f} : Set G)) K)
    (hinner : let hUN := hUf.trans ((normal_subgroupOf_iff_le_normalizer hKf).mp hn)
      ∃ u : U, u ≠ 1 ∧
        (K.normalizerMonoidHom.comp (inclusion hUN)) u ∈ MulAut.innerSubgroup K) :
    False := by
  exact contradiction_of_inner_bounds U K f hTI hKf hn hUf eK eR hC hinner
    Matrix.PSL3Four.InnerInvolutionCentralizers.innerCentralizer_isTwoGroup
    Matrix.PSL3Four.InnerInvolutionCentralizers.card_commonCentralizer_le
    (fun a ha _ ha2 =>
      Matrix.PSL3Four.InnerFixedCoverSize.four_lt_card_inner_fixed_image eK a ha ha2)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.PSL3FourAction.InnerPlane
