module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedTerminal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedRadius
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.TorusKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CartanFixedGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCoreFixed

/-!
# The common fixed subgroup and the source order bound

The literal fixed group of the full Cartan propagates from the terminal
radius-two kernel back along the original path. The odd Cartan factor
and the original full-kernel exclusions force each core containment.
The order bound compares the conjugate intrinsic radius-two kernels.
For the final commutator step, coprime generation places the moved
beta-core part inside the local two-residual, whose displacement of
the common kernel is already bounded by the original span.

Source: DGS, *Groups and Graphs* (1985), 9.10(4)--(5), pp.148--149.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The full Cartan fixed subgroup belongs to all five other original path cores. -/
theorem graph_cartan_common_fixed_cores
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {l a beta x a' r : Vertex (family P)}
    (hal : (graph (family P)).Adj a l) (hab : (graph (family P)).Adj a beta)
    (hbx : (graph (family P)).Adj beta x) (hxd : (graph (family P)).Adj x a')
    (hdr : (graph (family P)).Adj a' r)
    (ht : ∀ v : Vertex (family P), RootPathTransitive (graph (family P)) G v 2)
    {F K : Type*} [Field F] [Finite F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (el : (graphLocalGroup (family P) l ⧸ pCore 2 (graphLocalGroup (family P) l)) ≃* SL(2,F))
    (ea : (graphLocalGroup (family P) a ⧸ pCore 2 (graphLocalGroup (family P) a)) ≃* SL(2,K))
    (hF : 4 ≤ Nat.card F)
    (C : Subgroup G) [IsMulCommutative C]
    (hCl : C ≤ stabilizer (family P) l)
    (hCE : C ≤ stabilizer (family P) a ⊓ stabilizer (family P) beta)
    (hCx : C ≤ stabilizer (family P) x)
    (ho : Odd (Nat.card C))
    (hd : Disjoint C ((stabilizer (family P) a ⊓ stabilizer (family P) beta : Subgroup G).pCoreIn 2))
    (hg : C ⊔ (stabilizer (family P) a ⊓ stabilizer (family P) beta : Subgroup G).pCoreIn 2 =
      stabilizer (family P) a ⊓ stabilizer (family P) beta)
    (hne : C ⊓ graphLocalGroup (family P) l ≠ ⊥)
    (hTa : Disjoint (C ⊓ graphLocalGroup (family P) l) (ballKernel (family P) a 1))
    (hTb : Disjoint (C ⊓ graphLocalGroup (family P) l) (ballKernel (family P) beta 1))
    (hfixd : Q (family P) a' ⊓ centralizer (C ⊓ graphLocalGroup (family P) a' : Set G) ≤
      ballKernel (family P) a' 2) :
    Q (family P) a' ⊓ centralizer (C : Set G) ≤
      Q (family P) l ⊓ Q (family P) a ⊓ Q (family P) beta ⊓ Q (family P) x ⊓ Q (family P) r := by
  let := finite_endpoints h
  let Γ := family P
  let A := Q Γ a' ⊓ centralizer (C : Set G)
  let T := C ⊓ graphLocalGroup Γ l
  have hAK : A ≤ ballKernel Γ a' 2 :=
    (le_inf inf_le_left (inf_le_right.trans (centralizer_le inf_le_left))).trans hfixd
  have hp : IsPGroup 2 A := (isPGroup_pCoreIn 2 _).to_le inf_le_left
  have hAx : A ≤ Q Γ x := two_subgroup_le_Q Γ x (source_kernel_sylow h hB hS x) hp
    (hAK.trans (ballKernel_succ_le Γ hxd.symm 1))
  have hAr : A ≤ Q Γ r := two_subgroup_le_Q Γ r (source_kernel_sylow h hB hS r) hp
    (hAK.trans (ballKernel_succ_le Γ hdr 1))
  have hCA : C ≤ normalizer (A : Set G) :=
    (le_centralizer_iff.mp (show A ≤ centralizer (C : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hTA : T ≤ centralizer (A : Set G) := inf_le_left.trans
    (le_centralizer_iff.mp (show A ≤ centralizer (C : Set G) from inf_le_right))
  have hCxb := le_inf hCx (hCE.trans inf_le_right)
  obtain ⟨hdxb,hgxb⟩ := path_cartan_complement_at_edge h hab hbx.symm C hCE hCxb ho hd hg
  have hAb : A ≤ Q Γ beta := cartan_centralizer_le_neighbor_core h hB hS hbx.symm (ht x)
    eb C A T hCxb hdxb hgxb hAx hCA inf_le_left hne hTA hTb
  have hAa : A ≤ Q Γ a := cartan_centralizer_le_neighbor_core h hB hS hab.symm (ht beta)
    ea C A T (hCE.trans (inf_comm _ _).le) (by simpa only [inf_comm] using hd)
    (by simpa only [inf_comm] using hg) hAb hCA inf_le_left hne hTA hTa
  have hCal := le_inf (hCE.trans inf_le_left) hCl
  obtain ⟨hdal,hgal⟩ := path_cartan_complement_at_edge h hab hal C hCE hCal ho hd hg
  have hTl := nonbinary_odd_torus_disjoint_kernel h hB hS hal.symm el hF C ho
  have hAl : A ≤ Q Γ l := cartan_centralizer_le_neighbor_core h hB hS hal (ht a)
    el C A T hCal hdal hgal hAa hCA inf_le_left hne hTA hTl
  exact le_inf (le_inf (le_inf (le_inf hAl hAa) hAb) hAx) hAr

private theorem normalized_join_card_le (A B : Subgroup G) [Finite A] [Finite B]
    (hn : B ≤ normalizer (A : Set G)) : Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  let f : A × B → (A ⊔ B : Subgroup G) := fun p =>
    ⟨(p.1 : G) * p.2,mul_mem_sup p.1.property p.2.property⟩
  have hs : Function.Surjective f := by
    intro x
    have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left A B hn]
      exact x.property
    obtain ⟨a,ha,b,hb,he⟩ := hx
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),Subtype.ext he⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hs

/-- The source radius-two product supplies the required upper order bound at every conjugate vertex. -/
theorem graph_radius_order_bound
    (h : LocallyRankOneTriple P B) {l d : Vertex (family P)} (htype : l.type = d.type)
    (Q₀ : Subgroup G)
    (hprod : Q (family P) l ⊓ ballKernel (family P) l 2 = V (family P) l 1 ⊔ Q₀)
    (hcentral : Q (family P) l ⊓ ballKernel (family P) l 2 ≤
      centralizer (V (family P) l 1 : Set G)) :
    Nat.card (Q (family P) d ⊓ ballKernel (family P) d 2 : Subgroup G) ≤
      Nat.card Q₀ * Nat.card (V (family P) d 1) := by
  let := finite_endpoints h
  let Γ := family P
  have hQJ : Q₀ ≤ Q Γ l ⊓ ballKernel Γ l 2 := hprod ▸ le_sup_right
  have hVJ : V Γ l 1 ≤ Q Γ l ⊓ ballKernel Γ l 2 := hprod ▸ le_sup_left
  let : Finite Q₀ := Finite.of_injective (inclusion (hQJ.trans (inf_le_left.trans (Q_le_stabilizer Γ l))))
    (inclusion_injective _)
  let : Finite (V Γ l 1) := Finite.of_injective
    (inclusion (hVJ.trans (inf_le_left.trans (Q_le_stabilizer Γ l)))) (inclusion_injective _)
  obtain ⟨g,hg⟩ := (same_orbit_iff Γ l d).mpr htype
  have hJcard : Nat.card (Q Γ d ⊓ ballKernel Γ d 2 : Subgroup G) =
      Nat.card (Q Γ l ⊓ ballKernel Γ l 2 : Subgroup G) := by
    rw [←hg,Q_translate,ballKernel_translate,←map_inf _ _ _ (MulAut.conj g).injective,
      card_map_of_injective (MulAut.conj g).injective]
  have hVcard : Nat.card (V Γ d 1) = Nat.card (V Γ l 1) := by
    rw [←hg,V_translate,card_map_of_injective (MulAut.conj g).injective]
  rw [hJcard,hVcard,hprod,Nat.mul_comm]
  exact normalized_join_card_le (V Γ l 1) Q₀
    ((hQJ.trans hcentral).trans (Subgroup.centralizer_le_normalizer _))

/-- The original residual bound controls the beta-core commutator after its kernel centralizes the fixed subgroup. -/
theorem graph_core_fixed_commutator_le_span
    (h : LocallyRankOneTriple P B) {a beta x : Vertex (family P)}
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eb : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (hsec : CoreQuotientSection (family P) a beta x F eb)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hNQ : Q (family P) a ⊓ Q (family P) x ≤ Q (family P) beta)
    (hres : ⁅Q (family P) a ⊓ Q (family P) x,
      (pResidual 2 (graphLocalGroup (family P) beta)).map
        (graphLocalGroup (family P) beta).subtype⁆ ≤ V (family P) beta 1)
    (T Q₀ : Subgroup G) (hTH : T ≤ graphLocalGroup (family P) beta)
    (ho : Odd (Nat.card T)) (hne : T ≠ ⊥)
    (hQ₀N : Q₀ ≤ Q (family P) a ⊓ Q (family P) x)
    (hQN : ⁅Q₀,Q (family P) a ⊓ Q (family P) x⁆ = ⊥) :
    ⁅Q (family P) beta,Q₀⁆ ≤ V (family P) beta 1 := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ beta
  let N := Q Γ a ⊓ Q Γ x
  let R := (pResidual 2 H).map H.subtype
  let : Finite (Q Γ beta) := Finite.of_injective (inclusion (Q_le_stabilizer Γ beta))
    (inclusion_injective _)
  let : Finite T := Finite.of_injective (inclusion (hTH.trans (sylowGenerated_le _)))
    (inclusion_injective _)
  have hgen : Q Γ beta = N ⊔ ⁅Q Γ beta,T⁆ := by
    have hfixed := (core_section_odd_centralizer eb hsec hn hF T hTH ho hne).le.trans inf_le_left
    have hh := sup_eq_commutator_sup_of_fixed_le (Q Γ beta) N T (isPGroup_pCoreIn 2 _) ho
      ((hTH.trans (sylowGenerated_le _)).trans (stabilizer_normalizes_Q Γ beta)) hfixed
    rwa [sup_eq_left.mpr hNQ,sup_comm] at hh
  have hTR : T ≤ R := by
    intro t ht
    let u : H := ⟨t,hTH ht⟩
    change H.subtype u ∈ (pResidual 2 H).map H.subtype
    apply mem_map_of_mem H.subtype
    apply mem_pResidual_of_orderOf_coprime
    have htodd : Odd (orderOf u) := by
      rw [Subgroup.orderOf_mk]
      simpa only [Subgroup.orderOf_mk] using ho.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨t,ht⟩ : T))
    exact htodd.coprime_two_left
  have hHR : H ≤ normalizer (R : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hdispR : ⁅Q Γ beta,T⁆ ≤ R :=
    (commutator_mono le_rfl hTR).trans
      (le_normalizer_iff_commutator_le_right.mp ((core_le_graphLocalGroup h beta).trans hHR))
  have hdispQ : ⁅Q Γ beta,T⁆ ≤ Q Γ beta := le_normalizer_iff_commutator_le_left.mp
    ((hTH.trans (sylowGenerated_le _)).trans (stabilizer_normalizes_Q Γ beta))
  rw [hgen]
  apply commutator_sup_le_of_relative_normal (Q Γ beta) N ⁅Q Γ beta,T⁆ Q₀ (V Γ beta 1)
    ((Q_le_stabilizer Γ beta).trans (stabilizer_normalizes_V Γ beta 1)) hNQ hdispQ
  · rw [commutator_comm,hQN]
    exact bot_le
  · rw [commutator_comm]
    exact (commutator_mono hQ₀N hdispR).trans hres

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
