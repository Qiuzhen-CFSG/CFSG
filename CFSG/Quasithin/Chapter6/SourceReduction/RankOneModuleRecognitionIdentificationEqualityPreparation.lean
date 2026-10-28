module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationContracts

/-!
# Canonical subgroups and initial geometry in the equality branch

Let H = C_G(z), K = ⟨V^H⟩ and P = O₂(K). These definitions keep K and
P inside H; characteristic normality makes P normal in H and puts its
ambient image in the original Sylow subgroup. No extraspecial assertion
is included in the definitions.

In the equality branch, [V,U] lies in the plane Z_S. If it had order at
most two, T-invariance would put it in Ω₁Z(T) = ⟨z⟩. The action-kernel
identity would then put all of V in O₂(H), contrary to the order-eight
intersection. Hence [V,U] = Z_S. We also apply the natural hyperplane
geometry to the actual V ∩ O₂(H), with a constructed cubic in N_L(T∩L).

Source: Aschbacher--Smith, 6.2.13, printed pp.687--688. These are initial
steps; the action classification, extension analysis and final recognition
still require their source proofs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
universe u
variable {G : Type u} [Group G] [Finite G]

@[expose] def equalityLayerClosure (L R : Subgroup G) (z : G) :
    Subgroup (centralizer ({z} : Set G)) :=
  normalClosure ((layer L R).subgroupOf (centralizer ({z} : Set G)) :
    Set (centralizer ({z} : Set G)))

instance equalityLayerClosure_normal (L R : Subgroup G) (z : G) :
    (equalityLayerClosure L R z).Normal := by
  unfold equalityLayerClosure
  infer_instance

@[expose] def equalityCore (L R : Subgroup G) (z : G) :
    Subgroup (centralizer ({z} : Set G)) :=
  (equalityLayerClosure L R z).pCoreIn 2

instance equalityCore_normal (L R : Subgroup G) (z : G) :
    (equalityCore L R z).Normal := by
  exact ConjAct.normal_of_characteristic_of_normal

omit [Finite G] in
theorem equalityCore_le_sylow {T : Sylow 2 G} {L R : Subgroup G} {z : G}
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    (equalityCore L R z).map (centralizer ({z} : Set G)).subtype ≤ (T : Subgroup G) := by
  have hP : equalityCore L R z ≤ pCore 2 (centralizer ({z} : Set G)) :=
    le_sSup ⟨inferInstance, (equalityLayerClosure L R z).isPGroup_pCoreIn 2⟩
  have hs := pCoreIn_le_sylow (centralizer ({z} : Set G)) (T.subtype hTH)
  have hm := (map_mono (f := (centralizer ({z} : Set G)).subtype) hP).trans hs
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using hm

omit [Finite G] in
theorem sourceClosure_normalized (T L R : Subgroup G) (z : G) :
    centralizer ({z} : Set G) ≤ normalizer (sourceClosure T L R z : Set G) := by
  have hh := (sourceEight ((ZS T L R).subgroupOf (centralizer ({z} : Set G)))).le_normalizer_map
    (centralizer ({z} : Set G)).subtype
  simpa only [sourceClosure, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh

variable {κ : GroupClass.{u}} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

theorem LocalAnalysis.layer_closure_commutator_not_le_line
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    ¬ ⁅layer L R, sourceClosure (T : Subgroup G) L R z⁆ ≤ zpowers z := by
  intro hc
  have hVQ : layer L R ≤ (centralizer ({z} : Set G)).pCoreIn 2 := by
    intro v hv
    apply (A.action_kernel v (layer_le_involution_centralizer h611 hz hv)).mp
    intro u hu
    exact hc (commutator_mem_commutator hv hu)
  have he := A.layer_core_card
  rw [inf_eq_left.mpr hVQ, hnatural.2.1.card] at he
  norm_num at he

omit [Finite G] in
private theorem le_centralOmega_of_normalized_card_two (C : Subgroup G)
    (hCT : C ≤ (T : Subgroup G)) (hn : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hc : Nat.card C = 2) : C ≤ centralOmega (T : Subgroup G) := by
  let : (C.subgroupOf (T : Subgroup G)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCT).mpr hn
  have hcard : Nat.card (C.subgroupOf (T : Subgroup G)) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hCT).toEquiv).trans hc
  have hcentral := central_of_normal_card_two (C.subgroupOf (T : Subgroup G)) hcard
  intro x hx
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl x
  · refine ⟨hCT hx, ?_⟩
    apply mem_centralizer_iff.mpr
    intro t ht
    exact congrArg Subtype.val (mem_center_iff.mp
      (hcentral (show (⟨x, hCT hx⟩ : T) ∈ C.subgroupOf (T : Subgroup G) from hx)) ⟨t, ht⟩)
  · have hp := pow_card_eq_one' (x := (⟨x, hx⟩ : C))
    rw [hc] at hp
    exact congrArg Subtype.val hp

theorem LocalAnalysis.layer_closure_commutator_eq_plane
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R =
      ZS (T : Subgroup G) L R) :
    ⁅layer L R, sourceClosure (T : Subgroup G) L R z⁆ = ZS (T : Subgroup G) L R := by
  let C := ⁅layer L R, sourceClosure (T : Subgroup G) L R z⁆
  have hCZ : C ≤ ZS (T : Subgroup G) L R := by
    have hh := A.layer_closure_commutator
    rwa [inf_comm, hbranch] at hh
  have hn : (T : Subgroup G) ≤ normalizer (C : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change C.map (MulAut.conj t).toMonoidHom = C
    dsimp only [C]
    have hV : (layer L R).map (MulAut.conj t).toMonoidHom = layer L R :=
      mem_normalizer_iff_map_conj_eq.mp (h611.sylow_normalizes_layer ht)
    have hU : (sourceClosure (T : Subgroup G) L R z).map (MulAut.conj t).toMonoidHom =
        sourceClosure (T : Subgroup G) L R z :=
      mem_normalizer_iff_map_conj_eq.mp
        (sourceClosure_normalized (T : Subgroup G) L R z (hTH ht))
    rw [map_commutator, hV, hU]
  have hcard := (h611.natural_ZS_geometry hnatural).2.1
  have hdvd : Nat.card C ∣ 2 ^ 2 := by
    simpa only [hcard, Nat.reducePow] using card_dvd_of_le hCZ
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hnot := A.layer_closure_commutator_not_le_line h611 hnatural hz
  have hc : Nat.card C = 4 := by
    interval_cases k
    · have hbot : C = ⊥ := card_eq_one.mp (by simpa using he)
      exact (hnot (by change C ≤ _; rw [hbot]; exact bot_le)).elim
    · have hcle := le_centralOmega_of_normalized_card_two C (hCZ.trans h611.ZS_le_T)
        hn (by simpa using he)
      rw [A.central_omega] at hcle
      exact (hnot hcle).elim
    · simpa using he
  exact (eq_of_le_of_card_ge hCZ (by rw [hc, hcard]))

theorem LocalAnalysis.core_intersection_cubic_geometry
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) :
    ∃ d ∈ L, d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G) ∧ orderOf d = 3 ∧
      let B := layer L R ⊓ (centralizer ({z} : Set G)).pCoreIn 2
      ⁅B, (T : Subgroup G) ⊓ L⁆ = ZS (T : Subgroup G) L R ∧
      B ⊓ B.map (MulAut.conj d⁻¹).toMonoidHom = ZS (T : Subgroup G) L R := by
  obtain ⟨d, hdL, hdT, hd⟩ := exists_cubic_in_layer_sylow_normalizer h611 hnatural
  refine ⟨d, hdL, hdT, hd, ?_⟩
  apply h611.natural_eight_cubic_geometry hnatural.2.1 _ inf_le_left A.layer_core_card
    (le_inf inf_le_left ?_) hdL hdT hd
  exact ((ZS_le_sourceClosure_intersection h611 hz).trans inf_le_left).trans A.closure_le_core


end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
