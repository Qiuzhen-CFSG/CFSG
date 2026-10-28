module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryEndingBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RankOneEndingCommutator
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PairedIndexGeometry

/-!
# Both paired estimates and DGS 8.3 for unitary endings

For a large full-neighborhood actor, the critical-center constituent gives a
field-square lower bound. The ending two-rank and the original core-intersection
product give the first paired estimate. An actor of order at most two satisfies
it directly. Reciprocal escape supplies the reverse critical configuration,
where the same argument gives the second estimate with no reverse failure
hypothesis. The terminal source argument then proves 8.3. The final application
constructs the moving neighbor and edge Sylow and includes both field-two rows.

The earlier 6.5 obstruction and full source quotient catalogue remain explicit.
Source: DGS85, Groups and Graphs, (8.2) and (8.3)(2), pp.134–137.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CommutingTrivial Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem index_product (U Q K : Subgroup G) (h : U ⊓ Q ≤ K) :
    K.relIndex U * Q.relIndex (U ⊓ K) = Q.relIndex U := by
  rw [Nat.mul_comm,inf_comm U K,relIndex_inf_mul_relIndex]
  rw [←inf_relIndex_right (Q ⊓ K) U,←inf_relIndex_right Q U]
  congr 1
  ext x
  exact ⟨fun hx => ⟨hx.1.1,hx.2⟩,fun hx => ⟨⟨hx.1,h ⟨hx.2,hx.1⟩⟩,hx.2⟩⟩

private theorem elementary_index_of_rank (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup v)
    (n : ℕ) (hr : primeRank 2 (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≤ n) :
    (Q (family P) v).relIndex A ≤ 2^n := by
  let := finite_endpoints h
  let L := d.localGroup v
  let : Finite L := Finite.of_injective (inclusion (d.local_le v)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 L)
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hi := Representation.BinaryConjugationSection.actor_image_card_eq_relIndex L
    (Q (family P) v) A q (local_quotient_kernel (family P) d v (MulEquiv.refl _)) hAL
  exact hi ▸ (primeRank_le_iff_elementary_card_le _).mp hr _ inferInstance

private theorem elementary_index_at_same_type (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) {v w : Vertex (family P)}
    (ht : v.type = w.type) (n : ℕ)
    (hr : primeRank 2 (d.localGroup w ⧸ pCore 2 (d.localGroup w)) ≤ n)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup v) :
    (Q (family P) v).relIndex A ≤ 2^n := by
  let := finite_endpoints h
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) v w).mpr ht
  let e := MulAut.conj g
  let E := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hEL : E ≤ d.localGroup (g • v) := by rw [d.conjugate]; exact map_mono hAL
  have hh := elementary_index_of_rank h d (g • v) E hEL n hr
  rw [Q_translate,relIndex_map_map_of_injective _ _ e.injective] at hh
  exact hh

private theorem paired_square_of_field_bound (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' w : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (M : IsRankOneModel (d.localGroup beta ⧸ pCore 2 (d.localGroup beta)))
    (k m : ℕ)
    (hr : primeRank 2 (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) ≤ k)
    (hrw : primeRank 2 (d.localGroup w ⧸ pCore 2 (d.localGroup w)) ≤ m)
    (htype : a.type = w.type)
    (hlower : (2^k)^2 ≤ (centralizer (Z (family P) a : Set G)).relIndex (V (family P) a' 1)) :
    (Q (family P) a').relIndex (V (family P) beta 1)^2 ≤
      (Q (family P) beta).relIndex (V (family P) a' 1) * 2^m := by
  let := finite_endpoints h
  let F := family P
  have hb3 : 3 ≤ b F := (source_critical_geometry h d hc hab hd hb hcomm).2.1
  let : IsElementaryAbelian 2 (V F a' 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) a'
  let A := V F a' 1 ⊓ Q F beta
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hAL : A ≤ d.localGroup a := pGroup_le_localGroup F d a A
    (IsElementaryAbelian.isPGroup 2 A)
    (inf_le_right.trans ((source_Z_Q_U h beta).2.trans
      ((ballKernel_one_le_edge F hab.symm).trans inf_le_right)))
  have hsecondary := elementary_index_at_same_type h d htype m hrw A hAL
  have hfinite : V F a' 1 ≤ stabilizer F a' :=
    V_le_stabilizer_of_dist_add_le_b F h.generate a' a' 1
      (by simp only [SimpleGraph.dist_self,zero_add]; exact hb.le)
  let : Finite (V F a' 1) := Finite.of_injective (inclusion hfinite) (inclusion_injective _)
  have hcentral := relIndex_le_of_le_left
    (le_centralizer_iff.mp (Z_centralizes_Q F a (source_Z_Q_U h a).1))
    (((Q F a).subgroupOf (V F a' 1)).index_ne_zero_of_finite)
  have hproduct := index_product (V F a' 1) (Q F a) (Q F beta)
    (source_reverse_core_intersection h hB d hc hab hd hb hcomm M)
  obtain ⟨hactor,_⟩ := source_ending_rank_actor_bounds h d hc hab hd hb hcomm k hr
  calc
    (Q F a').relIndex (V F beta 1)^2 ≤ (2^k)^2 := Nat.pow_le_pow_left hactor 2
    _ ≤ (centralizer (Z F a : Set G)).relIndex (V F a' 1) := hlower
    _ ≤ (Q F a).relIndex (V F a' 1) := hcentral
    _ = (Q F beta).relIndex (V F a' 1) * (Q F a).relIndex A := hproduct.symm
    _ ≤ (Q F beta).relIndex (V F a' 1) * 2^m := Nat.mul_le_mul_left _ hsecondary

private theorem unitary_rank {D : Type*} [Group D] [Finite D] {n : ℕ}
    (hn : 2 ≤ n) (hu : ClassicalGroup.IsPSU D 3 (2^n) ∨ IsSU D 3 (2^n)) :
    primeRank 2 D ≤ n := by
  rcases hu with hu | hu
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e]
    exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le
  · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    rw [primeRank_congr 2 e,primeRank_eq_of_surjective_of_coprime 2 J.specialToProjective
      J.specialToProjective_surjective J.odd_card_specialToProjective_ker.coprime_two_left]
    exact (HermitianForm.EvenTwoRank.two_rank J (by omega) hK hconj).le

private theorem unitary_first_paired_square
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (k : ℕ) (hk : 2 ≤ k)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^k) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^k))
    (w : Vertex (Reduction.reducedFamily L S₀))
    (haw : a.type = w.type)
    (m : ℕ) (hm : 2 ≤ m)
    (hrw : primeRank 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w)) ≤ m) :
    let F := Reduction.reducedFamily L S₀
    (Q F a').relIndex (V F beta 1)^2 ≤ (Q F beta).relIndex (V F a' 1) * 2^m := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : Finite (graphLocalGroup F a') :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hr : primeRank 2 (d.localGroup a' ⧸ pCore 2 (d.localGroup a')) ≤ k := by
    change primeRank 2 (graphLocalGroup F a' ⧸ pCore 2 (graphLocalGroup F a')) ≤ k
    exact unitary_rank hk hu
  let x := (Q F a').relIndex (V F beta 1)
  let y := (Q F beta).relIndex (V F a' 1)
  have hVP : V F a' 1 ≤ stabilizer F a' :=
    V_le_stabilizer_of_dist_add_le_b F ht.generate a' a' 1
      (by simp only [SimpleGraph.dist_self,zero_add]; exact hb.le)
  let : Finite (V F a' 1) := Finite.of_injective (inclusion hVP) (inclusion_injective _)
  have hy : 0 < y := Nat.pos_of_ne_zero (((Q F beta).subgroupOf (V F a' 1)).index_ne_zero_of_finite)
  by_cases hsmall : x ≤ 2
  · have hq4 : 4 ≤ 2^m := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hm
    change x^2 ≤ y * 2^m
    nlinarith
  have hlarge : 4 ≤ x := by
    have hb2 : 2 < b F := by
      have hh := (source_critical_geometry ht d hc hab hd hb hcomm).2.1
      change 3 ≤ b F at hh
      omega
    let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F ht.generate
      (fun v => (source_Z_Q_U ht v).1) d.kernel_sylow hb2 beta
    have hVL : V F beta 1 ≤ d.localGroup a' :=
      neighbor_le_graphLocalGroup ht (Reduction.reduced_kernel_sylow h) beta a' hb hd.le
    let H := d.localGroup a'
    let q := QuotientGroup.mk' (pCore 2 H)
    let A := ((V F beta 1).subgroupOf H).map q
    let : Finite H := Finite.of_injective (inclusion (d.local_le a')) (inclusion_injective _)
    let : IsElementaryAbelian 2 ((V F beta 1).subgroupOf H) := IsElementaryAbelian.subgroupOf hVL
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
    have hcA : Nat.card A = x := BinaryConjugationSection.actor_image_card_eq_relIndex H
      (Q F a') (V F beta 1) q (local_quotient_kernel F d a' (MulEquiv.refl _)) hVL
    obtain ⟨r,hr⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have hx : x = 2^r := hcA.symm.trans hr
    have hr2 : 2 ≤ r := by
      by_contra! hh
      have hh' : r = 0 ∨ r = 1 := by omega
      rcases hh' with rfl | rfl <;> simp only [pow_zero,pow_one] at hx <;> omega
    rw [hx]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hr2
  exact paired_square_of_field_bound ht (Reduction.reduced_borel_core_sylow h) d
    hc hab hd hb hcomm (models beta) k m hr hrw haw
    (reduced_ending_unitary_large_actor_field_square h hc hab hd hb hcomm hk hu hlarge)

/-- The two original paired square estimates for every large unitary ending.
Neither orientation assumes failure of the desired omega commutator bound. -/
theorem reduced_unitary_paired_square
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',V (Reduction.reducedFamily L S₀) a' 1⁆ ≠ ⊥)
    (k : ℕ) (hk : 2 ≤ k)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^k) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^k))
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (m : ℕ) (hm : 2 ≤ m)
    (hrw : primeRank 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)) ≤ m) :
    let F := Reduction.reducedFamily L S₀
    (Q F a').relIndex (V F beta 1)^2 ≤ (Q F beta).relIndex (V F a' 1) * 2^m ∧
      (Q F beta).relIndex (V F a' 1)^2 ≤ (Q F a').relIndex (V F beta 1) * 2^m := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have haw : a.type = w.val.type := by
    have hodd := (source_critical_geometry ht d hc hab hd hb hcomm).1
    have hne : a.type ≠ a'.type := by
      intro he
      have heven := (even_dist_iff F ht.generate a a').mpr he
      rw [hc.1] at heven
      exact (Nat.not_even_iff_odd.mpr hodd) heven
    have hw := w.property.1
    cases hat : a.type <;> cases hwt : w.val.type <;> cases het : a'.type <;> simp_all
  have hfirst := unitary_first_paired_square h hob models hc hab hd hb hcomm k hk hu w.val haw m hm hrw
  obtain ⟨_,z,hz,hzc,hd',hzcomm,_⟩ := reduced_reciprocal_critical_configuration h hob models
    hc hab hd hb hcomm hne
  obtain ⟨_,_,f,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have hu' : ClassicalGroup.IsPSU (graphLocalGroup F beta ⧸ pCore 2 (graphLocalGroup F beta)) 3 (2^k) ∨
      IsSU (graphLocalGroup F beta ⧸ pCore 2 (graphLocalGroup F beta)) 3 (2^k) := by
    rcases hu with hu | hu
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      exact Or.inl ⟨K,inferInstance,inferInstance,J,hK,hconj,⟨f.symm.trans e⟩⟩
    · obtain ⟨K,_,_,J,hK,hconj,⟨e⟩⟩ := hu
      exact Or.inr ⟨K,inferInstance,inferInstance,J,hK,hconj,⟨f.symm.trans e⟩⟩
  have hzw : z.type = w.val.type := by
    have hz' := hz.1
    have hw := w.property.1
    cases hzt : z.type <;> cases hwt : w.val.type <;> cases het : a'.type <;> simp_all
  exact ⟨hfirst,unitary_first_paired_square h hob models hzc hz hd' hb hzcomm k hk hu' w.val hzw m hm hrw⟩

/-- Source 8.3 at any specified moving neighbor for a large unitary
ending. Both paired estimates are discharged on the original configuration. -/
theorem reduced_unitary_moving_omega_commutator
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily L S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily L S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily L S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily L S₀) w.val).subtype =
        (stabilizer (Reduction.reducedFamily L S₀) w.val ⊓ stabilizer (Reduction.reducedFamily L S₀) a').pCoreIn 2)
    (k : ℕ) (hk : 2 ≤ k)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^k) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^k)) :
    ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily L S₀) w.val) R,
      Z (Reduction.reducedFamily L S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
          V (Reduction.reducedFamily L S₀) a' 1⁆ := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  have hne : ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V F w.property)).trans hz.le))
  apply source_omega_commutator_of_paired_indices ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm R hR
  intro m hm2 hu₀
  change ClassicalGroup.IsPSU (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) 3 (2^m) ∨
    IsSU (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) 3 (2^m) at hu₀
  apply reduced_unitary_paired_square h hob models hc hab hd hb hcomm hne k hk hu w m hm2
  let : Finite (graphLocalGroup F w.val) :=
    Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  exact unitary_rank hm2 hu₀

/-- Literal reduced-F1.11 application for every special or projective unitary ending,
including field order two, with the moving neighbor and its full-edge Sylow constructed. -/
theorem reduced_ending_unitary_omega_commutator
    (h : HypothesisF11 L S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓ Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',V (Reduction.reducedFamily L S₀) a' 1⁆ ≠ ⊥)
    (k : ℕ) (hk : 0 < k)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^k) ∨
      IsSU (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) 3 (2^k)) :
    let F := Reduction.reducedFamily L S₀
    ¬ V F a' 1 ≤ Q F beta ∧
      ∃ w : (graph F).neighborSet a',
        ⁅V F beta 1 ⊓ Q F a',Z F w.val⁆ ≠ ⊥ ∧
        ∃ R : Sylow 2 (graphLocalGroup F w.val),
          (R : Subgroup (graphLocalGroup F w.val)).map (graphLocalGroup F w.val).subtype =
            (stabilizer F w.val ⊓ stabilizer F a').pCoreIn 2 ∧
          ⁅quotientSylowOmegaPreimage (graphLocalGroup F w.val) R,Z F w.val⁆ ≤
            ⁅V F beta 1 ⊓ Q F a',V F a' 1⁆ := by
  by_cases hk1 : k = 1
  · subst k
    exact reduced_ending_binary_models_omega_commutator h hob models hc hab hd hb hcomm hne
      (Or.inr (Or.inr (by simpa only [pow_one] using hu)))
  have hk2 : 2 ≤ k := by omega
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily L S₀
  let d := Reduction.reducedEarlierLocalTheorems h hob
  have he := reduced_reciprocal_escape h hob models hc hab hd hb hcomm hne
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor F (fun v => (source_Z_Q_U ht v).1) beta a' hne
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht (Reduction.reduced_borel_core_sylow h) d w.property.symm
  exact ⟨he,w,hm,R,hR,reduced_unitary_moving_omega_commutator h hob models
    hc hab hd hb hcomm w hm R hR k hk2 hu⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
