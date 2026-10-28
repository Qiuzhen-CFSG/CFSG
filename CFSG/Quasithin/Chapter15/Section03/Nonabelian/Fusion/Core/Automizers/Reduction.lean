module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PCoreNormalizedOvergroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The two-layer deduction in 15.3.59

Conjugation defines the actual actions of M on V and Q/V. If Q contains
its relative centralizer in M, the simultaneous action kernel is a
two-group: its two-residual centralizes Q by the displacement calculation,
and both that residual and its quotient are two-groups.

The two normalizer calculations control the residual image on each layer.
Their images must use the same element of Y. When V is central in Q and
V ≤ [Q,Q], the three-subgroups lemma shows that fixing Q/V also fixes V,
which supplies this compatibility. Pulling the image bound back through
the two-group kernel gives O²(M) = Y.

The last theorem retains the actual Sylow subgroup, Y normal in M, and
Q = O₂(Y). A separately proved transfer identifies O₂(M) with O₂(Y) from
O₂(YT) = O₂(Y), and the earlier characteristic-two condition identifies
F*(M) with that core. The source supplement M = YT is not assumed.

This module proves conditional reductions. It does not supply the local
core equality, the central-derived structure, or the two automizer
normalizer identities from the s = 1 models. Those calculations must be
supplied before the source result can be assembled in `Automizers`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.59, printed p.1150; the required module descriptions are
15.3.53(1), 15.3.54(4), and 15.3.58, printed pp.1146 and 1148–1149.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- Literal conjugation on the lower layer V. -/
def lowerAction (M V : Subgroup G) (hMV : M ≤ normalizer (V : Set G)) :
    M →* MulAut V := V.normalizerMonoidHom.comp (inclusion hMV)

/-- Literal conjugation on Q/V, with normality only inside Q. -/
noncomputable def upperAction (M Q V : Subgroup G)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] : M →* MulAut (Q ⧸ V.subgroupOf Q) :=
  Classical.choose (exists_quotient_conjugation_action M Q V hMQ hMV inferInstance)

theorem lowerAction_apply (M V : Subgroup G) (hMV : M ≤ normalizer (V : Set G))
    (m : M) (v : V) :
    (lowerAction M V hMV m v : G) = (m : G) * (v : G) * (m : G)⁻¹ := rfl

theorem upperAction_mk (M Q V : Subgroup G)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] (m : M) (q : Q) :
    upperAction M Q V hMQ hMV m (QuotientGroup.mk' _ q) =
      QuotientGroup.mk' (V.subgroupOf Q)
        ⟨(m : G) * (q : G) * (m : G)⁻¹,
          (mem_normalizer_iff.mp (hMQ m.property) q).mp q.property⟩ :=
  Classical.choose_spec (exists_quotient_conjugation_action M Q V hMQ hMV inferInstance) m q

/-- The simultaneous action retains the same actor in both factors. -/
noncomputable def jointAction (M Q V : Subgroup G)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] :
    M →* MulAut V × MulAut (Q ⧸ V.subgroupOf Q) :=
  (lowerAction M V hMV).prod (upperAction M Q V hMQ hMV)

/-- The actual Y-automizer of V, inside the automorphism group of V. -/
def lowerImage (M Y V : Subgroup G) (hMV : M ≤ normalizer (V : Set G)) :
    Subgroup (MulAut V) := (Y.subgroupOf M).map (lowerAction M V hMV)

/-- The actual Y-automizer of Q/V, with its literal denominator. -/
noncomputable def upperImage (M Y Q V : Subgroup G)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] : Subgroup (MulAut (Q ⧸ V.subgroupOf Q)) :=
  (Y.subgroupOf M).map (upperAction M Q V hMQ hMV)

/-- Equality with the embedded two-residual of the full automorphism
normalizer. For elementary binary groups, MulAut is canonically GL. -/
def IsNormalizerResidual {A : Type*} [Group A] (J : Subgroup A) : Prop :=
  (pResidual 2 (normalizer (J : Set A))).map (normalizer (J : Set A)).subtype = J

/-- The lower action kernel is exactly the relative centralizer. -/
theorem lowerAction_ker (M V : Subgroup G) (hMV : M ≤ normalizer (V : Set G)) :
    (lowerAction M V hMV).ker = (centralizer (V : Set G)).subgroupOf M := by
  ext m
  constructor
  · intro hm v hv
    have he := congrArg (fun a : MulAut V => (a ⟨v, hv⟩ : G)) (MonoidHom.mem_ker.mp hm)
    change (m : G) * v * (m : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hm
    apply MonoidHom.mem_ker.mpr
    ext v
    change (m : G) * (v : G) * (m : G)⁻¹ = v
    have he : (v : G) * (m : G) = (m : G) * (v : G) := hm v v.property
    rw [← he, mul_inv_cancel_right]

/-- Fixing Q/V means that the actual commutators land in V. -/
theorem upperAction_kernel_commutator (M Q V : Subgroup G)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] :
    ⁅(upperAction M Q V hMQ hMV).ker.map M.subtype, Q⁆ ≤ V := by
  apply commutator_le.mpr
  rintro _ ⟨m, hm, rfl⟩ q hq
  let qQ : Q := ⟨q, hq⟩
  let mq : Q := ⟨(m : G) * q * (m : G)⁻¹,
    (mem_normalizer_iff.mp (hMQ m.property) q).mp hq⟩
  have he : QuotientGroup.mk' (V.subgroupOf Q) mq = QuotientGroup.mk' _ qQ := by
    rw [← upperAction_mk M Q V hMQ hMV m qQ, MonoidHom.mem_ker.mp hm]
    rfl
  have hqv : mq * qQ⁻¹ ∈ V.subgroupOf Q := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (V.subgroupOf Q) (mq * qQ⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  exact hqv

/-- When V is central in Q and generated by Q-commutators, fixing Q/V
also fixes V. The three-subgroups lemma supplies the compatibility between
the two layers; independent choices of actors on the layers are not used. -/
theorem upperAction_kernel_le_lowerAction_kernel (M Q V : Subgroup G)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] (hcentral : V ≤ centralizer (Q : Set G))
    (hderived : V ≤ ⁅Q, Q⁆) :
    (upperAction M Q V hMQ hMV).ker ≤ (lowerAction M V hMV).ker := by
  let D := (upperAction M Q V hMQ hMV).ker.map M.subtype
  have hDQ : ⁅D, Q⁆ ≤ V := upperAction_kernel_commutator M Q V hMQ hMV
  have h₁ : ⁅⁅D, Q⁆, Q⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hDQ.trans hcentral)
  have h₂ : ⁅⁅Q, D⁆, Q⁆ = ⊥ := by rwa [commutator_comm Q D]
  have h₃ : ⁅⁅Q, Q⁆, D⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h₂ h₁
  have hDV : D ≤ centralizer (V : Set G) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h₃)).trans
      (centralizer_le hderived)
  rw [lowerAction_ker]
  intro m hm
  exact hDV (mem_map_of_mem M.subtype hm)

/-- The actual images on the two layers match the same Y-element when
V is central and generated by Q-commutators. -/
theorem layerImages_match_of_central_derived (M Y Q V : Subgroup G)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] (hcentral : V ≤ centralizer (Q : Set G))
    (hderived : V ≤ ⁅Q, Q⁆) :
    (jointAction M Q V hMQ hMV).range ⊓
        ((Y.subgroupOf M).map (lowerAction M V hMV)).prod
          ((Y.subgroupOf M).map (upperAction M Q V hMQ hMV)) ≤
      (Y.subgroupOf M).map (jointAction M Q V hMQ hMV) := by
  rintro _ ⟨⟨m, rfl⟩, _, hupper⟩
  obtain ⟨y, hy, he⟩ := hupper
  change upperAction M Q V hMQ hMV y = upperAction M Q V hMQ hMV m at he
  have hk : m * y⁻¹ ∈ (upperAction M Q V hMQ hMV).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have hk₁ := upperAction_kernel_le_lowerAction_kernel M Q V hMQ hMV hcentral hderived hk
  have he₁ : lowerAction M V hMV m = lowerAction M V hMV y := by
    have h := MonoidHom.mem_ker.mp hk₁
    rw [map_mul, map_inv, mul_inv_eq_one] at h
    exact h
  refine ⟨y, hy, ?_⟩
  exact Prod.ext he₁.symm he

private theorem isTwoGroup_of_residual_le_twoGroup [Finite G]
    (D Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hR : (pResidual 2 D).map D.subtype ≤ Q) : IsPGroup 2 D := by
  intro d
  obtain ⟨n, hn⟩ := isPGroup_quotient_pResidual (G := D) 2
    (QuotientGroup.mk' (pResidual 2 D) d)
  have hd : d ^ 2 ^ n ∈ pResidual 2 D := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (pResidual 2 D) (d ^ 2 ^ n) = 1
    rwa [map_pow]
  have hdQ : (d : G) ^ 2 ^ n ∈ Q := hR (mem_map_of_mem D.subtype hd)
  obtain ⟨k, hk⟩ := hQ ⟨(d : G) ^ 2 ^ n, hdQ⟩
  refine ⟨n + k, Subtype.ext ?_⟩
  have he := congrArg Subtype.val hk
  change ((d : G) ^ 2 ^ n) ^ 2 ^ k = 1 at he
  simpa only [coe_pow, coe_one, pow_add, pow_mul] using he

/-- The two-layer fixer is a two-group when Q contains its relative
centralizer in M. This is the coprime-action kernel step, not the model
normalizer calculation. -/
theorem jointAction_kernel_isTwoGroup [Finite G] (M Q V : Subgroup G)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] (hQ : IsPGroup 2 Q) (hVQ : V ≤ Q)
    (hc : M ⊓ centralizer (Q : Set G) ≤ Q) :
    IsPGroup 2 (jointAction M Q V hMQ hMV).ker := by
  let f := jointAction M Q V hMQ hMV
  let D := f.ker.map M.subtype
  have hDM : D ≤ M := map_subtype_le _
  have hDV : D ≤ centralizer (V : Set G) := by
    rintro _ ⟨m, hm, rfl⟩
    have he := congrArg Prod.fst (MonoidHom.mem_ker.mp hm)
    have hm₁ : m ∈ (lowerAction M V hMV).ker := he
    rw [lowerAction_ker] at hm₁
    exact hm₁
  have hDQ : ⁅D, Q⁆ ≤ V := by
    apply le_trans (commutator_mono (map_mono (f := M.subtype) ?_) le_rfl)
      (upperAction_kernel_commutator M Q V hMQ hMV)
    intro m hm
    exact congrArg Prod.snd (MonoidHom.mem_ker.mp hm)
  have hR : (pResidual 2 D).map D.subtype ≤ Q :=
    (le_inf ((map_subtype_le _).trans hDM)
      (residual_centralizes_of_two_layer D Q V (hQ.to_le hVQ) hDV hDQ)).trans hc
  have hp := isTwoGroup_of_residual_le_twoGroup D Q hQ hR
  exact hp.of_equiv (f.ker.equivMapOfInjective M.subtype M.subtype_injective).symm

/-- Normality puts the simultaneous kernel in the actual two-core of M. -/
theorem jointAction_kernel_le_core [Finite G] (M Q V : Subgroup G)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] (hQ : IsPGroup 2 Q) (hVQ : V ≤ Q)
    (hc : M ⊓ centralizer (Q : Set G) ≤ Q) :
    (jointAction M Q V hMQ hMV).ker ≤ pCore 2 M :=
  le_sSup ⟨inferInstance, jointAction_kernel_isTwoGroup M Q V hMQ hMV hQ hVQ hc⟩

/-- Transfer a core equality from the Sylow supplement to M using relative
normality of Y. No equality M = YT is assumed. -/
theorem core_eq_of_supplement_core [Finite G] (T : Sylow 2 G) (M Y : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hMY : M ≤ normalizer (Y : Set G))
    (hlocal : Stellmacher.twoCoreAmbient (Y ⊔ (T : Subgroup G)) =
      Stellmacher.twoCoreAmbient Y) :
    Stellmacher.twoCoreAmbient M = Stellmacher.twoCoreAmbient Y := by
  have hn : M ≤ normalizer
      ((pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)).map (Y ⊔ (T : Subgroup G)).subtype : Set G) := by
    change M ≤ normalizer (Stellmacher.twoCoreAmbient (Y ⊔ (T : Subgroup G)) : Set G)
    rw [hlocal]
    exact hMY.trans (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  exact (mapped_pCore_eq_of_normalized_local_pCore T (Y ⊔ (T : Subgroup G)) M
    le_sup_right (sup_le hYM hTM) hn).trans hlocal

/-- The earlier characteristic-two hypothesis and the transferred core
identify the actual generalized Fitting subgroup as well. -/
theorem fitting_eq_of_supplement_core [Finite G] (T : Sylow 2 G) (M Y : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hMY : M ≤ normalizer (Y : Set G))
    (hlocal : Stellmacher.twoCoreAmbient (Y ⊔ (T : Subgroup G)) =
      Stellmacher.twoCoreAmbient Y)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    (Theory.GroupTheory.generalizedFitting M).map M.subtype =
      Stellmacher.twoCoreAmbient Y := by
  rw [Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar]
  exact core_eq_of_supplement_core T M Y hTM hYM hMY hlocal

/-- A normal subgroup's automizer controls the image of the ambient residual
when it is the two-residual of its full automorphism normalizer. -/
theorem residual_image_le_of_normalizer_residual {A : Type*} [Group A]
    (f : G →* A) (Y : Subgroup G) [Y.Normal]
    (hn : (pResidual 2 (normalizer (Y.map f : Set A))).map
      (normalizer (Y.map f : Set A)).subtype = Y.map f) :
    (pResidual 2 G).map f ≤ Y.map f := by
  have hf : f.range ≤ normalizer (Y.map f : Set A) := by
    have h := Y.le_normalizer_map f
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map] at h
  let g := f.codRestrict (normalizer (Y.map f : Set A)) (fun x => hf ⟨x, rfl⟩)
  have h := map_mono (f := (normalizer (Y.map f : Set A)).subtype)
    (map_pResidual_le 2 g)
  rw [hn, map_map] at h
  exact h

private theorem residual_notation [Finite G] (M : Subgroup G) :
    Stellmacher.twoResidualAmbient M = (pResidual 2 M).map M.subtype := by
  unfold Stellmacher.twoResidualAmbient Stellmacher.twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    exact ⟨hN, IsPGroup.of_card (by simpa only [index_eq_card] using hn)⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hN, by simpa only [index_eq_card] using IsPGroup.iff_card.mp hp⟩

/-- Descent through the actual joint action. The image covering is a separate
model calculation; the two-layer kernel is proved here. -/
theorem residual_eq_of_joint_image [Finite G] (M Y Q V : Subgroup G)
    (hYM : Y ≤ M) (hY : IsPPerfect 2 Y)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] (hQ : IsPGroup 2 Q) (hVQ : V ≤ Q)
    (hc : M ⊓ centralizer (Q : Set G) ≤ Q)
    (hcore : Stellmacher.twoCoreAmbient M ≤ Y)
    (himage : (pResidual 2 M).map (jointAction M Q V hMQ hMV) ≤
      (Y.subgroupOf M).map (jointAction M Q V hMQ hMV)) :
    Stellmacher.twoResidualAmbient M = Y := by
  let f := jointAction M Q V hMQ hMV
  have hk : f.ker ≤ Y.subgroupOf M := by
    intro x hx
    exact hcore (mem_map_of_mem M.subtype
      (jointAction_kernel_le_core M Q V hMQ hMV hQ hVQ hc hx))
  have hr : pResidual 2 M ≤ Y.subgroupOf M := by
    have h := (le_comap_map f (pResidual 2 M)).trans (comap_mono himage)
    rw [comap_map_eq] at h
    exact h.trans (sup_le le_rfl hk)
  have hp : IsPPerfect 2 (Y.subgroupOf M) :=
    hY.of_surjective (subgroupOfEquivOfLe hYM).symm.toMonoidHom
      (subgroupOfEquivOfLe hYM).symm.surjective
  rw [residual_notation, le_antisymm hr (le_pResidual_of_isPPerfect _ hp),
    map_subgroupOf_eq_of_le hYM]

/-- The two normalizer calculations and compatibility of the two images
suffice for the source residual identity. Compatibility refers to the
simultaneous conjugation image, so the actor matching in the two module
models is retained. This theorem does not assert those model calculations. -/
theorem residual_eq_of_two_automizers [Finite G] (M Y Q V : Subgroup G)
    (hYM : Y ≤ M) (hMY : M ≤ normalizer (Y : Set G)) (hY : IsPPerfect 2 Y)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] (hQ : IsPGroup 2 Q) (hVQ : V ≤ Q)
    (hc : M ⊓ centralizer (Q : Set G) ≤ Q)
    (hcore : Stellmacher.twoCoreAmbient M ≤ Y)
    (hlower : IsNormalizerResidual (lowerImage M Y V hMV))
    (hupper : IsNormalizerResidual (upperImage M Y Q V hMQ hMV))
    (hcompatible : (jointAction M Q V hMQ hMV).range ⊓
        ((Y.subgroupOf M).map (lowerAction M V hMV)).prod
          ((Y.subgroupOf M).map (upperAction M Q V hMQ hMV)) ≤
      (Y.subgroupOf M).map (jointAction M Q V hMQ hMV)) :
    Stellmacher.twoResidualAmbient M = Y := by
  let : (Y.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMY
  have h₁ := residual_image_le_of_normalizer_residual (lowerAction M V hMV)
    (Y.subgroupOf M) hlower
  have h₂ := residual_image_le_of_normalizer_residual (upperAction M Q V hMQ hMV)
    (Y.subgroupOf M) hupper
  apply residual_eq_of_joint_image M Y Q V hYM hY hMQ hMV hQ hVQ hc hcore
  rintro _ ⟨m, hm, rfl⟩
  apply hcompatible
  exact ⟨⟨m, rfl⟩, h₁ (mem_map_of_mem _ hm), h₂ (mem_map_of_mem _ hm)⟩

/-- A directly usable two-layer deduction for the special core in 15.3.59.
The normalizer identities remain explicit concrete-model obligations; the
actor compatibility and the coprime kernel argument are proved here. -/
theorem residual_eq_of_central_derived_automizers [Finite G] (M Y Q V : Subgroup G)
    (hYM : Y ≤ M) (hMY : M ≤ normalizer (Y : Set G)) (hY : IsPPerfect 2 Y)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] (hQ : IsPGroup 2 Q) (hVQ : V ≤ Q)
    (hc : M ⊓ centralizer (Q : Set G) ≤ Q)
    (hcore : Stellmacher.twoCoreAmbient M ≤ Y)
    (hcentral : V ≤ centralizer (Q : Set G)) (hderived : V ≤ ⁅Q, Q⁆)
    (hlower : IsNormalizerResidual (lowerImage M Y V hMV))
    (hupper : IsNormalizerResidual (upperImage M Y Q V hMQ hMV)) :
    Stellmacher.twoResidualAmbient M = Y :=
  residual_eq_of_two_automizers M Y Q V hYM hMY hY hMQ hMV hQ hVQ hc hcore
    hlower hupper (layerImages_match_of_central_derived M Y Q V hMQ hMV hcentral hderived)

/-- The final group-theoretic assembly with Q anchored to O₂(Y), the actual
Sylow subgroup T, and relative normality of Y in M. The remaining premises
are precisely the local core and concrete module calculations, not M = YT
or O²(M) = Y. -/
theorem residual_eq_of_local_core_and_automizers [Finite G]
    (T : Sylow 2 G) (M Y Q V : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hMY : M ≤ normalizer (Y : Set G)) (hY : IsPPerfect 2 Y)
    (hQY : Q = Stellmacher.twoCoreAmbient Y)
    (hMQ : M ≤ normalizer (Q : Set G)) (hMV : M ≤ normalizer (V : Set G))
    [(V.subgroupOf Q).Normal] (hVQ : V ≤ Q)
    (hlocal : Stellmacher.twoCoreAmbient (Y ⊔ (T : Subgroup G)) = Q)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hcentral : V ≤ centralizer (Q : Set G)) (hderived : V ≤ ⁅Q, Q⁆)
    (hlower : IsNormalizerResidual (lowerImage M Y V hMV))
    (hupper : IsNormalizerResidual (upperImage M Y Q V hMQ hMV)) :
    Stellmacher.twoResidualAmbient M = Y := by
  have hcore : Stellmacher.twoCoreAmbient M = Q :=
    (core_eq_of_supplement_core T M Y hTM hYM hMY (hlocal.trans hQY)).trans hQY.symm
  have hQ : IsPGroup 2 Q := hQY.symm ▸ pCore_isPGroup.map Y.subtype
  have hc : M ⊓ centralizer (Q : Set G) ≤ Q := by
    intro m hm
    have hmc : (⟨m, hm.1⟩ : M) ∈ centralizer (pCore 2 M : Set M) := by
      intro q hq
      apply Subtype.ext
      exact hm.2 q (hcore ▸ mem_map_of_mem M.subtype hq)
    exact hcore ▸ mem_map_of_mem M.subtype (hchar hmc)
  have hcoreY : Stellmacher.twoCoreAmbient M ≤ Y := by
    rw [hcore, hQY]
    exact map_subtype_le _
  exact residual_eq_of_central_derived_automizers M Y Q V hYM hMY hY hMQ hMV hQ hVQ
    hc hcoreY hcentral hderived hlower hupper

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers
