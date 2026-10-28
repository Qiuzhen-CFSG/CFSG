module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section41Nu.Seed
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.LambdaSeparation.NormalizerAction

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.SylowActor.LocalGeometry

/-!
# Counting the initial actor's centralizer in Held's normalizer

Let S be the actual elementary subgroup of order sixteen and N its ambient
normalizer. Assuming |N| = 1152 and pi--mu nonfusion, we prove
|C_N(mu)| = 192 and obtain an actual element of order three centralizing mu.
The normalizer's pi orbit has nine points. Its mu orbit is disjoint from that
orbit and the identity, so has at most six points. The group C_N(mu) acts on
the latter orbit minus mu; the stabilizer of pi*mu is the known local
intersection of order 64. These two orbit-stabilizer equations force 192.
This replaces the corresponding counting step of Held's Lemma 2.11.

The consumer in InitialActor proves the normalizer order from the earlier
tau fusion, then supplies this order-three element to the marked-action and
inversion adjustments from the first paragraph of Lemma 4.1.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemmas 2.10--2.11 (p.230) and 4.1 (p.232).
All centralizers below are actual subgroups; initialNuCentralizer is relative
to N, not the whole centralizer of mu in G. No order of C_G(mu) is assumed.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
open Fusion Fusion.LambdaSeparation

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- The centralizer of mu inside the actual normalizer of S. -/
public abbrev initialNuCentralizer : Subgroup (sNormalizer D e) :=
  (centralizer ({D.a10ModelEmbedding e Coordinates.mu} : Set G)).subgroupOf
    (sNormalizer D e)

private noncomputable def muPoint : ambientElementary D e 1 :=
  ⟨D.a10ModelEmbedding e Coordinates.mu, mem_map_of_mem _ (mu_mem_elementary 1)⟩

omit [Finite G] in
private theorem muPoint_ne_one : muPoint D e ≠ 1 := by
  intro h
  have hm : Coordinates.mu ≠ 1 := by decide +kernel
  apply hm
  apply D.a10ModelEmbedding_injective e
  simpa only [muPoint, map_one, Subgroup.coe_one] using congrArg Subtype.val h

omit [Finite G] in
private theorem isConj_of_mem_orbit {x y : ambientElementary D e 1}
    (h : y ∈ MulAction.orbit (sNormalizer D e) x) : IsConj (x : G) (y : G) := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
  exact isConj_iff.mpr ⟨(g : G), congrArg Subtype.val hg⟩

omit [Finite G] in
private theorem muPoint_stabilizer :
    MulAction.stabilizer (sNormalizer D e) (muPoint D e) = initialNuCentralizer D e := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
  change (g : G) * D.a10ModelEmbedding e Coordinates.mu * (g : G)⁻¹ =
      D.a10ModelEmbedding e Coordinates.mu ↔
    (g : G) ∈ centralizer ({D.a10ModelEmbedding e Coordinates.mu} : Set G)
  rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

private theorem muPoint_orbit_card_le_six
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcard : Nat.card (sNormalizer D e) = 1152) :
    (MulAction.orbit (sNormalizer D e) (muPoint D e)).ncard ≤ 6 := by
  have hpi : (MulAction.orbit (sNormalizer D e) (piPoint D e)).ncard = 9 := by
    rw [normalizer_card] at hcard
    omega
  have hp : MulAction.orbit (sNormalizer D e) (piPoint D e) ⊆ {1}ᶜ := by
    intro x hx hx1
    have he : x = 1 := hx1
    have hc := isConj_of_mem_orbit D e hx
    rw [he] at hc
    exact D.z_ne_one (isConj_one_left.mp hc)
  have hm : MulAction.orbit (sNormalizer D e) (muPoint D e) ⊆
      {1}ᶜ \ MulAction.orbit (sNormalizer D e) (piPoint D e) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · intro hx1
      have he : x = 1 := hx1
      have hc := isConj_of_mem_orbit D e hx
      rw [he] at hc
      exact muPoint_ne_one D e (Subtype.ext (isConj_one_left.mp hc))
    · intro hpx
      exact hfusion ((isConj_of_mem_orbit D e hpx).trans
        (isConj_of_mem_orbit D e hx).symm)
  have hc := Set.ncard_le_ncard hm
  rw [Set.ncard_sdiff hp, Set.ncard_compl, Set.ncard_singleton,
    ambientElementary_card, hpi] at hc
  exact hc

private noncomputable def corePiPoint : ambientElementary D e 1 :=
  ⟨D.a10ModelEmbedding e corePi,
    mem_map_of_mem _ ((elementary 1).mul_mem (pi_mem_elementary 1) (mu_mem_elementary 1))⟩

private theorem corePiPoint_mem_muPoint_orbit :
    corePiPoint D e ∈ MulAction.orbit (sNormalizer D e) (muPoint D e) := by
  let f := D.a10ModelEmbedding e
  have ht : Coordinates.taup ∈ modelD := subset_closure ⟨(4 : Fin 7), rfl⟩
  let t : sNormalizer D e := ⟨f Coordinates.taup,
    ambientSylow_le_normalizer_S D e (mem_map_of_mem _ ht)⟩
  refine MulAction.mem_orbit_iff.mpr ⟨t, Subtype.ext ?_⟩
  change f Coordinates.taup * f Coordinates.mu * (f Coordinates.taup)⁻¹ = f corePi
  have h : Coordinates.taup * Coordinates.mu * Coordinates.taup⁻¹ = corePi := by
    decide +kernel
  simpa only [← map_inv, ← map_mul] using congrArg f h

omit [Finite G] in
private theorem corePiPoint_ne_muPoint : corePiPoint D e ≠ muPoint D e := by
  intro h
  have hlocal : corePi ≠ Coordinates.mu := by decide +kernel
  exact hlocal (D.a10ModelEmbedding_injective e
    (congrArg (fun x : ambientElementary D e 1 => (x : G)) h))

omit [Finite G] in
private theorem initialNuCentralizer_fixes_muPoint (g : initialNuCentralizer D e) :
    g • muPoint D e = muPoint D e := by
  apply Subtype.ext
  change (g.val : G) * D.a10ModelEmbedding e Coordinates.mu * (g.val : G)⁻¹ = _
  rw [mul_inv_eq_iff_eq_mul]
  exact mem_centralizer_singleton_iff.mp g.property

private theorem corePiPoint_orbit_card_le_five
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcard : Nat.card (sNormalizer D e) = 1152) :
    (MulAction.orbit (initialNuCentralizer D e) (corePiPoint D e)).ncard ≤ 5 := by
  have hsub : MulAction.orbit (initialNuCentralizer D e) (corePiPoint D e) ⊆
      MulAction.orbit (sNormalizer D e) (muPoint D e) \ {muPoint D e} := by
    intro x hx
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    refine ⟨?_, ?_⟩
    · obtain ⟨t, ht⟩ := MulAction.mem_orbit_iff.mp (corePiPoint_mem_muPoint_orbit D e)
      exact MulAction.mem_orbit_iff.mpr ⟨g.val * t, by rw [mul_smul, ht]; rfl⟩
    · intro he
      have he' : g • corePiPoint D e = g • muPoint D e :=
        (Set.mem_singleton_iff.mp he).trans (initialNuCentralizer_fixes_muPoint D e g).symm
      exact corePiPoint_ne_muPoint D e ((MulAction.injective g) he')
  have h := Set.ncard_le_ncard hsub
  have hmem : {muPoint D e} ⊆ MulAction.orbit (sNormalizer D e) (muPoint D e) := by
    simpa only [Set.singleton_subset_iff] using MulAction.mem_orbit_self (muPoint D e)
  rw [Set.ncard_sdiff hmem, Set.ncard_singleton] at h
  have hb := muPoint_orbit_card_le_six D e hfusion hcard
  omega

private theorem corePiPoint_stabilizer_card :
    Nat.card (MulAction.stabilizer (initialNuCentralizer D e) (corePiPoint D e)) = 64 := by
  let C₀ := initialNuCentralizer D e
  have hmem (g : C₀) :
      g ∈ MulAction.stabilizer C₀ (corePiPoint D e) ↔ (g.val : G) ∈ D.centralizer := by
    rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    change (g.val : G) * D.a10ModelEmbedding e corePi * (g.val : G)⁻¹ =
        D.a10ModelEmbedding e corePi ↔ _
    rw [mul_inv_eq_iff_eq_mul, mem_centralizer_singleton_iff]
    have hm : (g.val : G) * D.a10ModelEmbedding e Coordinates.mu =
        D.a10ModelEmbedding e Coordinates.mu * (g.val : G) :=
      mem_centralizer_singleton_iff.mp g.property
    rw [corePi, map_mul, D.a10ModelEmbedding_central e]
    constructor
    · intro h
      apply mul_right_cancel (b := D.a10ModelEmbedding e Coordinates.mu)
      simpa only [mul_assoc, ← hm] using h
    · intro h
      calc
        _ = ((g.val : G) * D.z) * D.a10ModelEmbedding e Coordinates.mu := by group
        _ = D.z * ((g.val : G) * D.a10ModelEmbedding e Coordinates.mu) := by rw [h, mul_assoc]
        _ = _ := by rw [hm]; group
  let E : MulAction.stabilizer C₀ (corePiPoint D e) ≃ muIntersection D e :=
    { toFun := fun x => ⟨x.val.val.val, ⟨(hmem x.val).mp x.property, x.val.property⟩⟩
      invFun := fun x =>
        let g : C₀ := ⟨⟨x.val, ambientSylow_le_normalizer_S D e
          (muIntersection_le_sylow D e x.property)⟩, x.property.2⟩
        ⟨g, (hmem g).mpr x.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr E).trans (muIntersection_card D e)

/-- The source centralizer order is relative to N_G(S), and follows from
its order and nonfusion by two orbit-stabilizer counts. -/
public theorem initialNuCentralizer_card_of_normalizer_card
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcard : Nat.card (sNormalizer D e) = 1152) :
    Nat.card (initialNuCentralizer D e) = 192 := by
  have hc := (MulAction.stabilizer (sNormalizer D e) (muPoint D e)).card_mul_index
  rw [muPoint_stabilizer, hcard] at hc
  have hb : (initialNuCentralizer D e).index ≤ 6 := by
    rw [← muPoint_stabilizer, MulAction.index_stabilizer]
    exact muPoint_orbit_card_le_six D e hfusion hcard
  have hc' := (MulAction.stabilizer (initialNuCentralizer D e) (corePiPoint D e)).card_mul_index
  rw [corePiPoint_stabilizer_card, MulAction.index_stabilizer] at hc'
  have hb' := corePiPoint_orbit_card_le_five D e hfusion hcard
  generalize (MulAction.orbit (initialNuCentralizer D e) (corePiPoint D e)).ncard = r at *
  rw [← hc'] at hc ⊢
  interval_cases r <;> omega

/-- The order-1152 normalizer and pi--mu nonfusion force a factor of three
in the centralizer of mu within that normalizer. -/
public theorem three_dvd_initialNuCentralizer_of_normalizer_card
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcard : Nat.card (sNormalizer D e) = 1152) :
    3 ∣ Nat.card (initialNuCentralizer D e) := by
  rw [initialNuCentralizer_card_of_normalizer_card D e hfusion hcard]
  norm_num

/-- The first existence step of Held 4.1, conditional only on the earlier
normalizer order. The element is in the actual ambient group. -/
public theorem exists_initialNu_three_of_normalizer_card
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcard : Nat.card (sNormalizer D e) = 1152) :
    ∃ v : G, v ∈ sNormalizer D e ∧ orderOf v = 3 ∧
      Commute v (D.a10ModelEmbedding e Coordinates.mu) := by
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := initialNuCentralizer D e) 3
    (three_dvd_initialNuCentralizer_of_normalizer_card D e hfusion hcard)
  refine ⟨v.val.val, v.val.property, ?_, ?_⟩
  · simpa only [Subgroup.orderOf_coe] using hv
  · exact mem_centralizer_singleton_iff.mp v.property


end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
