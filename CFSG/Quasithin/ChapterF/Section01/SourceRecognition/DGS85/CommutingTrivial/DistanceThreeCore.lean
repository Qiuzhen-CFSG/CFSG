module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CommutatorBound
public import Theory.GroupTheory.Commutator.NormalSpan
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent

/-!
# The middle core section at distance three

For the path (alpha,beta,x,alpha-prime), the whole-span identity and
faithfulness on the two centers identify Q_alpha intersect Q_x with
C_{Q_beta}(V_beta). This proves normality under the full beta stabilizer.
The middle-core product and the two actual neighboring SL2 markings give
an elementary quotient of order q^2.

Saturating Q_beta intersect Q_x by V_beta bounds its commutator with
V_alpha-prime by Z_x. The opposite span has a full Sylow image, so its
normal closure contains O^2(L_beta). Relative normality then gives the
source bound [Q_alpha intersect Q_x,O^2(L_beta)] <= V_beta.

The original reduced-graph application is in DistanceThreeCoreSection.
These statements prepare the new natural quotient in 9.10(1)(b); neither
its naturality nor the final field-two conclusion is assumed or asserted.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.10, opening paragraph and (1)(a), printed p.147; 9.6 and 9.8, pp.144--146.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- A faithful action on the actual center identifies its local centralizer with the core. -/
theorem faithful_center_local_centralizer
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    {F : Type*} [Field F]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    letI := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
    let H := graphLocalGroup (family P) v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    ∀ ρ : Representation (ZMod 2) SL(2,F) (Additive (Z (family P) v)),
      (∀ (l : H) (z : Additive (Z (family P) v)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      Function.Injective ρ →
      H ⊓ centralizer (Z (family P) v : Set G) = Q (family P) v := by
  let := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
  let Γ := family P
  let H := graphLocalGroup Γ v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  dsimp only
  intro ρ hact hf
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    let l : H := ⟨x,hx⟩
    have he : ρ (q l) = 1 := by
      apply LinearMap.ext
      intro z
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [hact]
      exact mul_inv_eq_iff_eq_mul.mpr (hc z.toMul z.toMul.property).symm
    have hq : q l = 1 := hf (he.trans ρ.map_one.symm)
    have hk : l ∈ pCore 2 H := (QuotientGroup.eq_one_iff l).mp
      (e.injective (hq.trans e.map_one.symm))
    exact (graphLocalGroup_core h v).le (mem_map_of_mem H.subtype hk)
  · exact le_inf (core_le_graphLocalGroup h v)
      (le_centralizer_iff.mp (CommutingNontrivial.Z_centralizes_Q Γ v (source_Z_Q_U h v).1))

/-- The two-center product identifies the literal core intersection and its full normalizer. -/
theorem middle_core_intersection_centralizer
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w x : Vertex (family P)}
    (hvw : (graph (family P)).Adj v w) (hwx : (graph (family P)).Adj w x)
    (hspan : V (family P) w 1 = Z (family P) v ⊔ Z (family P) x)
    (hv : graphLocalGroup (family P) v ⊓ centralizer (Z (family P) v : Set G) = Q (family P) v)
    (hx : graphLocalGroup (family P) x ⊓ centralizer (Z (family P) x : Set G) = Q (family P) x) :
    let Γ := family P
    Q Γ v ⊓ Q Γ x = Q Γ w ⊓ centralizer (V Γ w 1 : Set G) ∧
      Q Γ v ⊓ Q Γ x ≤ Q Γ w ∧
      stabilizer Γ w ≤ normalizer ((Q Γ v ⊓ Q Γ x : Subgroup G) : Set G) := by
  let := finite_endpoints h
  let Γ := family P
  let N := Q Γ v ⊓ Q Γ x
  have hNC : N ≤ centralizer (V Γ w 1 : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hspan]
    exact sup_le
      ((CommutingNontrivial.Z_centralizes_Q Γ v (source_Z_Q_U h v).1).trans
        (centralizer_le inf_le_left))
      ((CommutingNontrivial.Z_centralizes_Q Γ x (source_Z_Q_U h x).1).trans
        (centralizer_le inf_le_right))
  have hNw : N ≤ stabilizer Γ w := inf_le_left.trans
    ((source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge Γ hvw).trans inf_le_right))
  have hNQ : N ≤ Q Γ w := two_subgroup_le_Q Γ w (source_kernel_sylow h hB hS w)
    ((isPGroup_pCoreIn 2 (stabilizer Γ v)).to_le inf_le_left)
    ((le_inf hNw hNC).trans (neighborhood_centralizer_le_U h w))
  have he : N = Q Γ w ⊓ centralizer (V Γ w 1 : Set G) := by
    apply le_antisymm (le_inf hNQ hNC)
    apply le_inf
    · rw [←hv]
      exact le_inf (inf_le_left.trans (neighbor_core_le_localGroup h hB hS hvw))
        (inf_le_right.trans (centralizer_le (CommutingNontrivial.Z_neighbor_le_V Γ hvw.symm)))
    · rw [←hx]
      exact le_inf (inf_le_left.trans (neighbor_core_le_localGroup h hB hS hwx.symm))
        (inf_le_right.trans (centralizer_le (CommutingNontrivial.Z_neighbor_le_V Γ hwx)))
  refine ⟨he,hNQ,?_⟩
  change stabilizer Γ w ≤ normalizer (N : Set G)
  rw [he]
  exact (le_inf (stabilizer_normalizes_Q Γ w)
    ((stabilizer_normalizes_V Γ w 1).trans (normalizer_le_normalizer_centralizer _))).trans
    inf_normalizer_le_normalizer_inf

/-- The noncontained neighboring core has the full defining-field index. -/
theorem linear_adjacent_core_index
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hw : (graph (family P)).Adj v w)
    (he : ¬ Q (family P) w ≤ Q (family P) v)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    (Q (family P) v).relIndex (Q (family P) w) = Nat.card F := by
  let H := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkmap : q.ker.map H.subtype = Q (family P) v := hk ▸ graphLocalGroup_core h v
  obtain ⟨T,hT,_⟩ := linear_neighbor_core_sylow_image h hB hS hw he e
  have hh := relIndex_ker ((Q (family P) w).subgroupOf H) q
  rw [←relIndex_map_map_of_injective _ _ H.subtype_injective,hkmap,
    map_subgroupOf_eq_of_le (neighbor_core_le_localGroup h hB hS hw),hT] at hh
  exact hh.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv)

private theorem local_two_subgroup_square
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (A : Subgroup G) (hp : IsPGroup 2 A) (hA : A ≤ graphLocalGroup (family P) v)
    {a : G} (ha : a ∈ A) : a^2 ∈ Q (family P) v := by
  let H := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let I := (A.subgroupOf H).map q
  let l : H := ⟨a,hA ha⟩
  have hm : q l ∈ I := mem_map_of_mem q ha
  have he := congrArg Subtype.val
    (Matrix.SpecialLinearGroup.twoSubgroup_pow_two I (hp.comap_subtype.map q) ⟨q l,hm⟩)
  have hq : q (l^2) = 1 := (map_pow q l 2).trans he
  have hk : l^2 ∈ pCore 2 H := (QuotientGroup.eq_one_iff (l^2)).mp
    (e.injective (hq.trans e.map_one.symm))
  exact (graphLocalGroup_core h v).le (mem_map_of_mem H.subtype hk)

private theorem inter_index_of_core_product (A C Q₀ : Subgroup G)
    (hprod : Q₀ = (A ⊓ Q₀) ⊔ (C ⊓ Q₀))
    (hn : Q₀ ≤ normalizer (A : Set G)) :
    (A ⊓ C).relIndex Q₀ = A.relIndex Q₀ * C.relIndex Q₀ := by
  let I := A.subgroupOf Q₀
  let J := C.subgroupOf Q₀
  let : I.Normal := normal_subgroupOf_of_le_normalizer hn
  have hp : I ⊔ J = ⊤ := by
    apply Subgroup.map_injective Q₀.subtype_injective
    rw [Subgroup.map_sup,subgroupOf_map_subtype,subgroupOf_map_subtype,
      ←MonoidHom.range_eq_map,range_subtype,←hprod]
  have hi := relIndex_sup_left J I
  rw [hp,relIndex_top_right] at hi
  have he : A.relIndex (C ⊓ Q₀) = A.relIndex Q₀ := by
    calc
      A.relIndex (C ⊓ Q₀) = I.relIndex J := by
        simpa only [inf_subgroupOf_right] using
          (relIndex_subgroupOf (H := A) (K := C ⊓ Q₀) inf_le_right).symm
      _ = I.index := hi.symm
      _ = A.relIndex Q₀ := rfl
  rw [←relIndex_inf_mul_relIndex,he]

/-- The original middle-core quotient is elementary and has the square field order. -/
theorem middle_core_quotient_elementary_order
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hob : ∀ v w : Vertex (family P), (graph (family P)).Adj v w →
      ¬ stabilizer (family P) v ≤ normalizer ((Q (family P) w ⊓ Q (family P) v : Subgroup G) : Set G))
    {v w x : Vertex (family P)}
    (hvw : (graph (family P)).Adj v w) (hwx : (graph (family P)).Adj w x) (hne : v ≠ x)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (ew : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    (ev : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,K))
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,K)) :
    let Γ := family P
    let N := Q Γ v ⊓ Q Γ x
    ∃ _hN : (N.subgroupOf (Q Γ w)).Normal,
      IsElementaryAbelian 2 (Q Γ w ⧸ N.subgroupOf (Q Γ w)) ∧
      Nat.card (Q Γ w ⧸ N.subgroupOf (Q Γ w)) = Nat.card K ^ 2 := by
  let Γ := family P
  have hfix {a b : Vertex Γ} (hab : (graph Γ).Adj a b) :
      Q Γ a ≤ stabilizer Γ b :=
    (source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge Γ hab).trans inf_le_right)
  have hvN : Q Γ w ≤ normalizer (Q Γ v : Set G) :=
    (hfix hvw.symm).trans (stabilizer_normalizes_Q Γ v)
  have hxN : Q Γ w ≤ normalizer (Q Γ x : Set G) :=
    (hfix hwx).trans (stabilizer_normalizes_Q Γ x)
  let hN : ((Q Γ v ⊓ Q Γ x).subgroupOf (Q Γ w)).Normal :=
    normal_subgroupOf_of_le_normalizer ((le_inf hvN hxN).trans inf_normalizer_le_normalizer_inf)
  refine ⟨hN,?_,?_⟩
  · have hs : ∀ z : Q Γ w ⧸ (Q Γ v ⊓ Q Γ x).subgroupOf (Q Γ w), z^2 = 1 := by
      intro z
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective ((Q Γ v ⊓ Q Γ x).subgroupOf (Q Γ w)) z
      rw [←map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨local_two_subgroup_square h v ev (Q Γ w) (isPGroup_pCoreIn 2 _)
        (neighbor_core_le_localGroup h hB hS hvw) a.property,
        local_two_subgroup_square h x ex (Q Γ w) (isPGroup_pCoreIn 2 _)
          (neighbor_core_le_localGroup h hB hS hwx.symm) a.property⟩
    have hi (z : Q Γ w ⧸ (Q Γ v ⊓ Q Γ x).subgroupOf (Q Γ w)) : z⁻¹ = z :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs z)
    let : IsMulCommutative (Q Γ w ⧸ (Q Γ v ⊓ Q Γ x).subgroupOf (Q Γ w)) :=
      ⟨⟨fun a b => by rw [←hi (a*b),mul_inv_rev,hi,hi]⟩⟩
    exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs⟩
  · change (Q Γ v ⊓ Q Γ x).relIndex (Q Γ w) = _
    rw [inter_index_of_core_product _ _ _
      (linear_middle_core_product h hB hS hob hvw.symm hwx hne ew ev) hvN,
      linear_adjacent_core_index h hB hS hvw
        (core_escape_of_intersection_obstruction Γ (hob w v hvw.symm)) ev,
      linear_adjacent_core_index h hB hS hwx.symm
        (core_escape_of_intersection_obstruction Γ (hob w x hwx)) ex,pow_two]

private theorem linear_residual_le_actor_span
    (h : LocallyRankOneTriple P B) (v : Vertex (family P))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (A : Subgroup G) (hp : IsPGroup 2 A) (hA : A ≤ graphLocalGroup (family P) v)
    (hi : (Q (family P) v).relIndex A = Nat.card F) :
    (pResidual 2 (graphLocalGroup (family P) v)).map (graphLocalGroup (family P) v).subtype ≤
      conjugateSpanBy A (graphLocalGroup (family P) v) := by
  let := finite_endpoints h
  let H := graphLocalGroup (family P) v
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let I := (A.subgroupOf H).map q
  obtain ⟨T,hT⟩ := (hp.comap_subtype.map q).exists_le_sylow
  have hkmap : q.ker.map H.subtype = Q (family P) v := hk ▸ graphLocalGroup_core h v
  have hcard : Nat.card I = Nat.card F := by
    rw [←relIndex_ker,←relIndex_map_map_of_injective _ _ H.subtype_injective,
      hkmap,map_subgroupOf_eq_of_le hA,hi]
  have hTI : I = T := eq_of_le_of_card_ge hT (by
    rw [hcard]
    exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).toEquiv).ge)
  let X := normalClosure (A.subgroupOf H : Set H)
  let : (X.map q).Normal := (inferInstance : X.Normal).map q hq
  have hTX : (T : Subgroup SL(2,F)) ≤ X.map q := hTI ▸ map_mono
    (show A.subgroupOf H ≤ X from le_normalClosure)
  obtain ⟨g,_,hg⟩ := Matrix.SpecialLinearGroup.exists_residual_conjugate_sylow_image_sup_eq_top
    T (MonoidHom.id SL(2,F)) Function.surjective_id
  simp only [Subgroup.map_id] at hg
  have hmap : X.map q = ⊤ := by
    apply top_unique
    rw [←hg]
    refine sup_le hTX ?_
    rintro _ ⟨x,hx,rfl⟩
    exact (inferInstance : (X.map q).Normal).conj_mem x (hTX hx) g
  have hsup : X ⊔ q.ker = ⊤ := by
    simpa only [comap_map_eq,comap_top] using congrArg (Subgroup.comap q) hmap
  have hr : pResidual 2 H ≤ X :=
    sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top X q.ker (hk ▸ pCore_isPGroup) hsup⟩
  have hm := map_mono (f := H.subtype) hr
  rw [map_normalClosure_eq_conjugateSpanBy_range,range_subtype,
    map_subgroupOf_eq_of_le hA] at hm
  exact hm

/-- At critical distance three, every neighborhood span lies in each adjacent core. -/
theorem distance_three_neighbor_span_le_core
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b (family P) = 3) {v w : Vertex (family P)}
    (hvw : (graph (family P)).Adj v w) : V (family P) v 1 ≤ Q (family P) w := by
  let := finite_endpoints h
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  apply Z_le_Q_of_dist_lt_b (family P) (fun x => (source_Z_Q_U h x).1)
    (source_kernel_sylow h hB hS) z w
  have hh := (connected (family P) h.generate).dist_triangle (u := z) (v := v) (w := w)
  have hdist := (mem_ball_iff (family P) h.generate v z 1).mp hz
  rw [SimpleGraph.dist_comm (u := z) (v := v),SimpleGraph.dist_eq_one_iff_adj.mpr hvw] at hh
  omega

/-- Source 9.10(1)(a), with the actual opposite span and the original two-residual. -/
theorem distance_three_core_intersection_residual_bound
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta x a' : Vertex (family P)}
    (hab : (graph (family P)).Adj a beta)
    (hbx : (graph (family P)).Adj beta x) (hxa' : (graph (family P)).Adj x a')
    (hb : b (family P) = 3)
    (hN : stabilizer (family P) beta ≤ normalizer ((Q (family P) a ⊓ Q (family P) x : Subgroup G) : Set G))
    (hNQ : Q (family P) a ⊓ Q (family P) x ≤ Q (family P) beta)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (e' : (graphLocalGroup (family P) a' ⧸ pCore 2 (graphLocalGroup (family P) a')) ≃* SL(2,F))
    (hi : (Q (family P) a').relIndex (V (family P) beta 1) = Nat.card F)
    (hi' : (Q (family P) beta).relIndex (V (family P) a' 1) = Nat.card F)
    (hc' : ⁅Q (family P) a',V (family P) a' 1⁆ = Z (family P) a')
    (hω' : Z (family P) a' = omegaCenterIn (graphLocalGroup (family P) a'))
    (hcomm : ⁅V (family P) beta 1,V (family P) a' 1⁆ ≤ Z (family P) x) :
    let Γ := family P
    V Γ beta 1 ≤ Q Γ a ⊓ Q Γ x ∧
    ⁅Q Γ beta ⊓ Q Γ x,V Γ a' 1⁆ ≤ Z Γ x ∧
      ⁅Q Γ a ⊓ Q Γ x,(pResidual 2 (graphLocalGroup Γ beta)).map
        (graphLocalGroup Γ beta).subtype⁆ ≤ V Γ beta 1 := by
  let := finite_endpoints h
  let Γ := family P
  change b Γ = 3 at hb
  let D := Q Γ beta ⊓ Q Γ x
  let N := Q Γ a ⊓ Q Γ x
  have hZ := fun v => (source_Z_Q_U h v).1
  have hSyl := source_kernel_sylow h hB hS
  have hVD : V Γ beta 1 ≤ D := le_inf
    (V_le_Q Γ h.generate hZ hSyl beta (by omega : 1 < b Γ))
    (distance_three_neighbor_span_le_core h hB hS hb hbx)
  have hDH : D ≤ graphLocalGroup Γ a' := inf_le_right.trans
    (neighbor_core_le_localGroup h hB hS hxa'.symm)
  have hprod : D = V Γ beta 1 ⊔ (D ⊓ Q Γ a') :=
    linear_local_pgroup_saturation h a' e' (V Γ beta 1) D hVD hDH
      ((isPGroup_pCoreIn 2 _).to_le inf_le_left) hi
  have hZ'x : Z Γ a' ≤ Z Γ x := hω' ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hxa'.symm
  have hDx : ⁅D,V Γ a' 1⁆ ≤ Z Γ x := by
    rw [hprod]
    apply commutator_sup_le_of_relative_normal (Q Γ x) _ _ _ _
      ((Q_le_stabilizer Γ x).trans (CommutingNontrivial.stabilizer_normalizes_Z Γ x))
      (hVD.trans inf_le_right) (inf_le_left.trans inf_le_right) hcomm
    exact ((commutator_mono inf_le_right le_rfl).trans hc'.le).trans hZ'x
  refine ⟨le_inf (distance_three_neighbor_span_le_core h hB hS hb hab.symm)
    (distance_three_neighbor_span_le_core h hB hS hb hbx),hDx,?_⟩
  have hAH : V Γ a' 1 ≤ graphLocalGroup Γ beta :=
    (distance_three_neighbor_span_le_core h hB hS hb hxa'.symm).trans
      (neighbor_core_le_localGroup h hB hS hbx)
  have hpA : IsPGroup 2 (V Γ a' 1) := (isPGroup_pCoreIn 2 _).to_le
    (V_le_Q Γ h.generate hZ hSyl a' (by omega : 1 < b Γ))
  have hgen := linear_residual_le_actor_span h beta eβ (V Γ a' 1) hpA hAH hi'
  rw [commutator_comm]
  apply (commutator_mono hgen le_rfl).trans
  rw [commutator_conjugateSpanBy_of_normalized_right _ _ _ hAH ((sylowGenerated_le _).trans hN)]
  apply conjugateSpanBy_le
  · rw [commutator_comm]
    exact ((commutator_mono (le_inf hNQ inf_le_right) le_rfl).trans hDx).trans
      (CommutingNontrivial.Z_neighbor_le_V Γ hbx)
  · exact (sylowGenerated_le _).trans (stabilizer_normalizes_V Γ beta 1)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
