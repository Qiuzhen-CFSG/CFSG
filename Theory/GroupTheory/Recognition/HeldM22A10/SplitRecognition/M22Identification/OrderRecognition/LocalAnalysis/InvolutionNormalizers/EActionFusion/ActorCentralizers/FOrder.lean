module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.ActorCentralizers.Containment
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.AmbientElementary
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# The order-24 F-normalizer quotient under actor nonfusion

The established equality C(a) = C(a) ∩ C(z), together with fusion of d and
a in N(E), gives |C(d)| = 32. The elementary-sixteen normality theorem
places C(d) inside N(F); its order prevents N(F) from being just T.

On the other hand, the orbit of z under N(F) lies in (E ∩ F) minus the
identity, a set of size three, since any conjugate in F outside E would
fuse z with d. The stabilizer is exactly T, so its odd index is three.
Consequently |N(F)| = 384 and its quotient by the actual normal F has
order 24. No splitting or identification of that quotient is assumed.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, pp.6–7 and Lemma 7. We obtain the local
centralizer first using Sylow normalizer control, then recover the source
order calculation.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- Fusion inside N(E) transports the order of the full actor centralizer. -/
public theorem actor_d_centralizer_card (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) :
    Nat.card (centralizer ({into D k d} : Set G)) = 32 := by
  obtain ⟨n, hna⟩ := normalizer_actor_d_conjugate_a D k hE
  rw [card_centralizer_eq_of_isConj _ _ (isConj_iff.mpr ⟨(n : G), hna⟩),
    actorCentralizer_eq_local D k hE hn, actorLocalCentralizer_card]

/-- The full centralizer of d normalizes the elementary sixteen F. -/
public theorem actor_d_centralizer_le_normalizer_F (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) :
    centralizer ({into D k d} : Set G) ≤ normalizer (F D k : Set G) := by
  have hC : IsPGroup 2 (centralizer ({into D k d} : Set G)) :=
    IsPGroup.of_card (n := 5) (by rw [actor_d_centralizer_card D k hE hn]; rfl)
  obtain ⟨S, hCS⟩ := hC.exists_le_sylow
  have hFC : F D k ≤ centralizer ({into D k d} : Set G) := by
    rw [← modelF_map D k]
    rintro x ⟨y, hy, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul] using congrArg (into D k) (mem_centralizer_singleton_iff.mp hy))
  exact hCS.trans ((normal_subgroupOf_iff_le_normalizer (hFC.trans hCS)).mp
    (elementary_sixteen_normal_in_sylow D k S (F D k) (hFC.trans hCS)
      (F_elementary D k) (F_card D k)))

private theorem F_not_normalizer_eq_sylow (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) :
    normalizer (F D k : Set G) ≠ (caseIISylow D k : Subgroup G) := by
  intro hN
  have hCC : centralizer ({into D k d} : Set G) ≤ D.centralizer :=
    (actor_d_centralizer_le_normalizer_F D k hE hn).trans
      (hN ▸ (show (caseIISylow D k : Subgroup G) ≤ D.centralizer from
        (map_le_range _ _).trans (by
          rw [into, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr k.surjective,
            ← MonoidHom.range_eq_map, D.centralizer.range_subtype])))
  have hCF : centralizer ({into D k d} : Set G) ≤ F D k := by
    intro x hx
    obtain ⟨y, hy⟩ := k.surjective ⟨x, hCC hx⟩
    have hyx : into D k y = x := congrArg Subtype.val hy
    rw [← modelF_map D k]
    refine ⟨y, mem_centralizer_singleton_iff.mpr ?_, hyx⟩
    apply into_injective D k
    simpa only [map_mul, hyx] using mem_centralizer_singleton_iff.mp hx
  have hc := card_le_of_le hCF
  rw [actor_d_centralizer_card D k hE hn, F_card] at hc
  omega

private def fNormalizerPoint : F D k := ⟨D.z, by
  rw [← into_z_zero D k, ← modelF_map D k]
  exact mem_map_of_mem _ modelF_generators.1⟩

private theorem fNormalizerPoint_stabilizer :
    MulAction.stabilizer (normalizer (F D k : Set G)) (fNormalizerPoint D k) =
      (caseIISylow D k : Subgroup G).subgroupOf (normalizer (F D k : Set G)) := by
  ext g
  rw [MulAction.mem_stabilizer_iff]
  change (⟨(g : G) * D.z * (g : G)⁻¹, _⟩ : F D k) = fNormalizerPoint D k ↔
    (g : G) ∈ caseIISylow D k
  rw [Subtype.ext_iff]
  change (g : G) * D.z * (g : G)⁻¹ = D.z ↔ _
  rw [mul_inv_eq_iff_eq_mul, ← mem_centralizer_singleton_iff]
  change (g : G) ∈ D.centralizer ↔ (g : G) ∈ (caseIISylow D k : Subgroup G)
  rw [← normalizer_F_inf_centralizer D k]
  exact ⟨fun h => ⟨g.property, h⟩, fun h => h.2⟩

omit [Finite G] in
private theorem E_subgroupOf_F_card : Nat.card ((E D k).subgroupOf (F D k)) = 4 := by
  rw [← inf_subgroupOf_left, inf_comm (F D k) (E D k)]
  rw [Nat.card_congr (subgroupOfEquivOfLe (H := E D k ⊓ F D k) inf_le_right).toEquiv]
  rw [← modelE_map D k, ← modelF_map D k, ← map_inf _ _ _ (into_injective D k),
    card_map_of_injective (into_injective D k)]
  let : DecidableEq TwistedModel := fun x y =>
    decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
  let : Fintype TwistedModel := Fintype.ofEquiv
    (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
  let : DecidablePred (· ∈ modelE) := fun x => inferInstanceAs (Decidable (x.right = 1))
  let : DecidablePred (· ∈ modelF) := fun x =>
    decidable_of_iff (x * d = d * x) mem_centralizer_singleton_iff.symm
  let : DecidablePred (· ∈ modelE ⊓ modelF) := fun x =>
    decidable_of_iff (x ∈ modelE ∧ x ∈ modelF) mem_inf.symm
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- Contrary actor nonfusion forces the normalizer of F to have order 384. -/
public theorem fNormalizer_card_of_actor_nonfusion (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) :
    Nat.card (normalizer (F D k : Set G)) = 384 := by
  let N := normalizer (F D k : Set G)
  let T := (caseIISylow D k : Subgroup G).subgroupOf N
  let O := MulAction.orbit N (fNormalizerPoint D k)
  have hbound : O.ncard ≤ 3 := by
    have hO : O ⊆ ((E D k).subgroupOf (F D k) : Set (F D k)) \ {1} := by
      intro x hx
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hx
      have hzx : IsConj D.z (x : G) := isConj_iff.mpr ⟨(g : G), congrArg Subtype.val hg⟩
      refine ⟨marked_conjugate_mem_E D k hE hn
        (caseIISylow_le_normalizer_E D k (F_le_caseIISylow D k x.property)) hzx, ?_⟩
      intro hx1
      have h1 : (x : G) = 1 := congrArg Subtype.val hx1
      have heq := congrArg Subtype.val hg
      change (g : G) * D.z * (g : G)⁻¹ = (x : G) at heq
      rw [h1] at heq
      exact D.z_ne_one ((MulAut.conj (g : G)).injective (heq.trans (map_one _).symm))
    have h := Set.ncard_le_ncard hO
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem _)] at h
    change O.ncard ≤ Nat.card ((E D k).subgroupOf (F D k)) - 1 at h
    rw [E_subgroupOf_F_card] at h
    exact h
  have hodd : Odd T.index := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact (caseIISylow D k).not_dvd_index
      ((even_iff_two_dvd.mp he).trans
        (relIndex_dvd_index_of_le (caseIISylow_le_normalizer_F D k)))
  have hi : T.index = O.ncard := by
    change ((caseIISylow D k : Subgroup G).subgroupOf N).index =
      (MulAction.orbit N (fNormalizerPoint D k)).ncard
    rw [← fNormalizerPoint_stabilizer D k, MulAction.index_stabilizer]
  have hne : T.index ≠ 1 := by
    intro h1
    have htop : T = ⊤ := index_eq_one.mp h1
    exact F_not_normalizer_eq_sylow D k hE hn
      (le_antisymm (subgroupOf_eq_top.mp htop) (caseIISylow_le_normalizer_F D k))
  have hindex : T.index = 3 := by
    rw [hi] at hodd hne ⊢
    rcases hodd with ⟨m, hm⟩
    omega
  have hc := T.card_mul_index
  have hTc : Nat.card T = 128 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (caseIISylow_le_normalizer_F D k)).toEquiv]
    change Nat.card (modelT.map (into D k)) = 128
    rw [card_map_of_injective (into_injective D k), modelT_card]
  rw [hTc, hindex] at hc
  exact hc.symm

/-- The literal quotient N(F)/F has order 24 in the contrary case. -/
public theorem fNormalizerQuotient_card_of_actor_nonfusion (hE : ENormalizerAction D k)
    (hn : ¬ IsConj D.z (into D k d)) :
    Nat.card (normalizer (F D k : Set G) ⧸
      (F D k).subgroupOf (normalizer (F D k : Set G))) = 24 := by
  have h := card_eq_card_quotient_mul_card_subgroup
    ((F D k).subgroupOf (normalizer (F D k : Set G)))
  rw [fNormalizer_card_of_actor_nonfusion D k hE hn,
    Nat.card_congr (subgroupOfEquivOfLe (F D k).le_normalizer).toEquiv, F_card] at h
  omega

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
