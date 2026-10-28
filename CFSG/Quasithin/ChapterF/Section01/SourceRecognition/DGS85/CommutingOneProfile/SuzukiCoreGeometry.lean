module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairSuzukiBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CubicIntersections
public import Theory.GroupAction.PrimeDegreeCoprimeIndex

/-!
# The full Suzuki center-pair orbit and core intersection

For positive Suzuki parameters the two Sylow omega-centers generate the
entire local quotient. Lifting through the actual core makes the source
center pair transitive on the beta star. At parameter zero its image need
not be the whole group of order twenty: the pair is not a two-group, so
its index is prime to five and it is transitive on the five-point star.

The pair centralizes the intersection of its two alpha cores. Its orbit
therefore identifies that intersection with the intersection over every
beta neighbor. SuzukiExclusion combines this with the proved (11.6)(a)
center equality and the source core span to exclude every Suzuki parameter.
Source: DGS85, Groups and Graphs (1985), (5.3) and the Suzuki case of
(11.8), printed pp.105--106 and 176. The full local kernel is kept distinct
from the intrinsic two-core throughout the orbit transport.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open BenderSuzuki.MatrixGroups Representation.RankOne.QuadraticRecognition
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem suzuki_omega_pair {m : ℕ} (hm : 0 < m)
    (R T : Sylow 2 (SuzukiMatrixGroup m)) (hne : R ≠ T) :
    omegaCenterIn (R : Subgroup (SuzukiMatrixGroup m)) ⊔ omegaCenterIn (T : Subgroup (SuzukiMatrixGroup m)) = ⊤ := by
  have hd : Disjoint (R : Subgroup (SuzukiMatrixGroup m)) (T : Subgroup (SuzukiMatrixGroup m)) := by
    obtain ⟨S,hS⟩ := suzukiRootSubgroup_isSylow m hm
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) S R
    obtain ⟨t,ht⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) S T
    have hR : (R : Subgroup (SuzukiMatrixGroup m)) = (SuzukiRootSubgroup m).map (MulAut.conj g).toMonoidHom := by
      rw [←hg,←hS]; rfl
    have hT : (T : Subgroup (SuzukiMatrixGroup m)) = (SuzukiRootSubgroup m).map (MulAut.conj t).toMonoidHom := by
      rw [←ht,←hS]; rfl
    rw [hR,hT]
    exact suzukiRootSubgroup_conjugates_disjoint m hm g t (fun he =>
      hne (Sylow.ext (hR.trans (he.trans hT.symm))))
  rw [omegaCenterIn_eq_omegaOneAmbient,omegaCenterIn_eq_omegaOneAmbient,
    suzuki_omega_center_eq,suzuki_omega_center_eq]
  have hTne : omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup m)) ≠ ⊥ := by
    intro he
    have hh := suzukiSylow_omega_card hm (MulEquiv.refl _) T
    rw [he,card_bot] at hh
    have hp := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by omega : 2*m+1 ≠ 0)
    omega
  obtain ⟨t,ht,ht1⟩ := (omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup m))).bot_or_exists_ne_one.resolve_left hTne
  let := suzukiSylow_omega_elementary hm (MulEquiv.refl _) T
  have ht2 : t^2=1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have htR : t ∉ R := fun hh => ht1 (disjoint_def.mp hd hh (omegaOneAmbient_le _ ht))
  have htN : t ∉ normalizer (R : Set (SuzukiMatrixGroup m)) := by
    intro hn
    have hp : IsPGroup 2 (zpowers t) :=
      (IsElementaryAbelian.zpowers_of_pow_eq_one ht2).isPGroup
    have hi := hp.inf_normalizer_sylow R
    exact htR (hi.le ⟨mem_zpowers t,hn⟩).2
  obtain ⟨e,hR,hB⟩ := suzukiSylow_aligned_equiv hm (MulEquiv.refl _) R
  have htB : e.symm t ∉ SuzukiBorelSubgroup m := by
    intro hh
    apply htN
    rw [←hB]
    simpa only [MulEquiv.coe_toMonoidHom,e.apply_symm_apply] using mem_map_of_mem e.toMonoidHom hh
  have hgen := congrArg (map e.toMonoidHom)
    (suzukiRootSubgroup_omega_sup_zpowers_eq_top m hm (e.symm t) htB)
  rw [Subgroup.map_sup,map_omegaOneAmbient_injective e.toMonoidHom e.injective,hR,
    MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom,e.apply_symm_apply,map_top_of_surjective _ e.surjective] at hgen
  exact top_unique (hgen ▸ sup_le le_sup_left ((zpowers_le.mpr ht).trans le_sup_right))

private theorem nonbinary_center_pair_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    {m : ℕ} (hm : 0 < m)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SuzukiMatrixGroup m) :
    ∀ v, (graph (family P)).Adj b v →
      ∃ t ∈ Z (family P) a ⊔ Z (family P) c, t • a = v := by
  let := finite_endpoints h
  let K := d.localGroup b
  let W := Z (family P) a ⊔ Z (family P) c
  let H := W ⊔ Q (family P) b
  let : Finite K := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite (K ⧸ pCore 2 K) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hHK,R,T,hRT,hker,ha,hc',hr⟩ := source_pair_actor_map h hB d hc hb hbc hac (.suzuki m ⟨eb⟩)
  let q := QuotientGroup.mk' (pCore 2 K)
  let f := eb.toMonoidHom.comp (q.comp (inclusion hHK))
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,hr,Subgroup.map_sup,
      NilesRankOneKernel.omegaCenterIn_map_injective eb.toMonoidHom eb.injective,
      NilesRankOneKernel.omegaCenterIn_map_injective eb.toMonoidHom eb.injective]
    apply suzuki_omega_pair hm (R.mapSurjective eb.surjective) (T.mapSurjective eb.surjective)
    intro he
    exact hRT (Sylow.ext (map_injective eb.injective (congrArg Sylow.toSubgroup he)))
  have hKH : K ≤ H := by
    intro x hx
    obtain ⟨y,hy⟩ := hsurj (eb (q ⟨x,hx⟩))
    have hy' : q (inclusion hHK y) = q ⟨x,hx⟩ := eb.injective hy
    have hz : (inclusion hHK y)⁻¹ * ⟨x,hx⟩ ∈ pCore 2 K := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q _ = 1
      rw [map_mul,map_inv,hy',inv_mul_cancel]
    have hz' : (y:G)⁻¹*x ∈ Q (family P) b := by
      exact (localGroup_core_eq (family P) d b).le (mem_map_of_mem K.subtype hz)
    have hh := H.mul_mem y.property (mem_sup_right hz')
    simpa only [mul_inv_cancel_left] using hh
  have hgen : H = K := le_antisymm hHK hKH
  have hn : W ≤ normalizer (Q (family P) b : Set G) :=
    (le_sup_left.trans (hHK.trans (d.local_le b))).trans (stabilizer_normalizes_Q _ b)
  have hab := source_critical_one_adjacent hc hb
  intro v hbv
  obtain ⟨t,ht,hta⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨v,hbv⟩
  have ht' : t ∈ (W : Set G) * (Q (family P) b : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right W (Q (family P) b) hn]
    change t ∈ H
    rw [hgen]
    exact ht
  obtain ⟨w,hw,z,hz,rfl⟩ := ht'
  have hza : z • a = a := ((source_Z_Q_U h b).2.trans
    ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right)) hz
  exact ⟨w,hw,by simpa only [mul_smul,hza] using hta⟩

private theorem small_suzuki_normalizer_index
    (R T U : Sylow 2 (SuzukiMatrixGroup 0)) (hne : R ≠ T) :
    (normalizer (U : Set (SuzukiMatrixGroup 0))).index = 5 := by
  have hcard : Nat.card U = 4 := by
    rw [U.card_eq_multiplicity,suzukiZero_card]
    decide +kernel
  have hidx : (U : Subgroup (SuzukiMatrixGroup 0)).index = 5 := by
    have hh := (U : Subgroup (SuzukiMatrixGroup 0)).card_mul_index
    rw [hcard,suzukiZero_card] at hh
    omega
  have hd := Subgroup.index_dvd_of_le (le_normalizer (H := (U : Subgroup (SuzukiMatrixGroup 0))))
  rw [hidx] at hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with hi | hi
  · have hn : (U : Subgroup (SuzukiMatrixGroup 0)).Normal :=
      normalizer_eq_top_iff.mp ((Subgroup.index_eq_one).mp hi)
    let := Sylow.unique_of_normal U hn
    exact (hne (Subsingleton.elim R T)).elim
  · exact hi

private theorem small_center_pair_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SuzukiMatrixGroup 0) :
    ∀ v, (graph (family P)).Adj b v →
      ∃ t ∈ Z (family P) a ⊔ Z (family P) c, t • a = v := by
  let := finite_endpoints h
  let K := d.localGroup b
  let W := Z (family P) a ⊔ Z (family P) c
  let H := W ⊔ Q (family P) b
  let Mb : IsRankOneModel (K ⧸ pCore 2 K) := .suzuki 0 ⟨eb⟩
  let : Finite K := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite (K ⧸ pCore 2 K) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hHK,R,T,hRT,_⟩ := source_pair_actor_map h hB d hc hb hbc hac Mb
  let q := eb.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eb.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eb.injective,QuotientGroup.ker_mk']
  let R' := R.mapSurjective (f := eb.toMonoidHom) eb.surjective
  let T' := T.mapSurjective (f := eb.toMonoidHom) eb.surjective
  have hRT' : R' ≠ T' := fun he => hRT
    (Sylow.ext (map_injective eb.injective (congrArg Sylow.toSubgroup he)))
  let A := H.subgroupOf K
  have hkerA : q.ker ≤ A := by
    rw [hk]
    intro x hx
    exact mem_sup_right ((localGroup_core_eq (family P) d b).le (mem_map_of_mem K.subtype hx))
  have hnot : ¬ IsPGroup 2 (A.map q) := by
    intro hp
    have hA := hp.comap_of_ker_isPGroup q (hk ▸ pCore_isPGroup)
    rw [comap_map_eq,sup_eq_left.mpr hkerA] at hA
    have hH : IsPGroup 2 H := hA.of_equiv (subgroupOfEquivOfLe hHK)
    exact source_rankOne_centers_not_isPGroup h hB d hc hb hbc hac Mb (hH.to_le le_sup_left)
  have hcop : Nat.Coprime 5 A.index := by
    rw [←A.index_map_eq hq hkerA]
    apply (Nat.prime_five.coprime_iff_not_dvd).mpr
    rintro ⟨n,hn⟩
    have hh := (A.map q).card_mul_index
    rw [suzukiZero_card,hn] at hh
    have hd : Nat.card (A.map q) ∣ 2^2 := ⟨n,by nlinarith⟩
    exact hnot (IsPGroup.of_card_dvd_pow hd)
  have hab := source_critical_one_adjacent hc hb
  obtain ⟨U,hU⟩ := source_edge_core_local_sylow h hB d hab.symm
  let U' := U.mapSurjective hq
  have hUU : (U' : Subgroup (SuzukiMatrixGroup 0)).comap q = U := by
    change ((U : Subgroup K).map q).comap q = _
    rw [comap_map_eq,hk,sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal U)]
  have hN : (normalizer (U' : Set (SuzukiMatrixGroup 0))).comap q = normalizer (U : Set K) := by
    change (normalizer ((U' : Subgroup (SuzukiMatrixGroup 0)) : Set (SuzukiMatrixGroup 0))).comap q = _
    rw [comap_normalizer_eq_of_surjective _ hq,hUU]
    rfl
  have hidx : (MulAction.stabilizer K a).index = 5 := by
    have hs : MulAction.stabilizer K a = normalizer (U : Set K) :=
      (source_edge_local_normalizer h d hab.symm Mb U hU).2
    rw [hs,←hN,index_comap_of_surjective _ hq]
    exact small_suzuki_normalizer_index R' T' U' hRT'
  let X := MulAction.orbit K a
  have hcard : Nat.card X = 5 := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer K a),←index_eq_card,hidx]
  let : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : MulAction.IsPretransitive A X :=
    MulAction.isPretransitive_of_prime_card_of_coprime_index (by decide) hcard A hcop
  have hn : W ≤ normalizer (Q (family P) b : Set G) :=
    (le_sup_left.trans (hHK.trans (d.local_le b))).trans (stabilizer_normalizes_Q _ b)
  intro v hbv
  obtain ⟨t,ht,hta⟩ := d.transitive b ⟨a,hab.symm⟩ ⟨v,hbv⟩
  let xa : X := ⟨a,MulAction.mem_orbit_self a⟩
  let xv : X := ⟨v,⟨(⟨t,ht⟩ : K),hta⟩⟩
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq A xa xv
  have hua : ((u : K) : G) • a = v := congrArg Subtype.val hu
  have huH : ((u : K) : G) ∈ H := u.property
  have hu' : ((u : K) : G) ∈ (W : Set G) * (Q (family P) b : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right W (Q (family P) b) hn]
    exact huH
  obtain ⟨w,hw,z,hz,he⟩ := hu'
  have hza : z • a = a := ((source_Z_Q_U h b).2.trans
    ((ballKernel_one_le_edge _ hab.symm).trans inf_le_right)) hz
  refine ⟨w,hw,?_⟩
  change w*z = ((u : K) : G) at he
  rw [←he,mul_smul,hza] at hua
  exact hua

/-- The actual center pair is transitive for every Suzuki parameter, including Sz(2). -/
theorem source_suzuki_center_pair_transitive
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (m : ℕ) (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SuzukiMatrixGroup m) :
    ∀ v, (graph (family P)).Adj b v →
      ∃ t ∈ Z (family P) a ⊔ Z (family P) c, t • a = v := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact small_center_pair_transitive h hB d hc hb hbc hac eb
  · exact nonbinary_center_pair_transitive h hB d hc hb hbc hac hm eb

/-- The two alpha cores already give the complete neighboring-core intersection
in the Suzuki row. No center or core order is assumed. -/
theorem source_suzuki_core_pair_eq_neighbor_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (m : ℕ) (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SuzukiMatrixGroup m) :
    Q (family P) a ⊓ Q (family P) c = neighborCoreIntersection (family P) b :=
  source_core_pair_eq_neighbor_intersection_of_center_pair_transitive h
    (source_critical_one_adjacent hc hb) hbc
    (source_suzuki_center_pair_transitive h hB d hc hb hbc hac m eb)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
