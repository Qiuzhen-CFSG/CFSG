module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdaptedPairTerminal

/-!
# The nonbinary contradiction from the original adapted core layers

The two original natural layers and the preceding Cartan collapse construct
M, with no complement or adapted subgroup assumed. Its natural quotient and
the natural center force fixed-point-free action of the middle Cartan factor.
The terminal full-kernel escape places its core centralizer in Q_r, identifies
Q_beta ∩ Q_d with V_d, and contradicts the normal-edge graph obstruction.

The two local fields, their markings, the full path Cartan, and the literal
quotient and center coordinates remain unchanged. The collapse input is the
specific output of 9.10(4)–(5). Source: DGS, *Groups and Graphs* (1985),
printed pp.149–150, the end of the nonbinary branch of 9.10.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original nonbinary source core layers, Cartan and center coordinates
contradict the final graph normal-subgroup obstruction after the source collapse. -/
theorem reduced_adapted_pair_nonbinary_contradiction
    (h : HypothesisF11 L S)
    {x beta d r : Vertex (Reduction.reducedFamily L S)}
    (hb : (graph (Reduction.reducedFamily L S)).Adj x beta)
    (hd : (graph (Reduction.reducedFamily L S)).Adj x d) (hne : beta ≠ d)
    (hb3 : b (Reduction.reducedFamily L S) = 3)
    {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2]
    (ex : (graphLocalGroup (Reduction.reducedFamily L S) x ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) x)) ≃* SL(2,K))
    (ed : (graphLocalGroup (Reduction.reducedFamily L S) d ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) d)) ≃* SL(2,F))
    (hKF : Nat.card K = Nat.card F)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hres : NaturalResidualSection h d ed n)
    (hsec : CoreQuotientSection (Reduction.reducedFamily L S) r d x F ed)
    (hNspan : Q (Reduction.reducedFamily L S) r ⊓ Q (Reduction.reducedFamily L S) x =
      V (Reduction.reducedFamily L S) d 1)
    (hωd : Z (Reduction.reducedFamily L S) d =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) d))
    (hc : ⁅Q (Reduction.reducedFamily L S) d,V (Reduction.reducedFamily L S) d 1⁆ ≤
      Z (Reduction.reducedFamily L S) d)
    (hVcard : Nat.card (V (Reduction.reducedFamily L S) d 1) = Nat.card F ^ 3)
    (hZcard : Nat.card (Z (Reduction.reducedFamily L S) d) = Nat.card F)
    (hZspan : Z (Reduction.reducedFamily L S) x =
      Z (Reduction.reducedFamily L S) beta ⊔ Z (Reduction.reducedFamily L S) d)
    (hZxcard : Nat.card (Z (Reduction.reducedFamily L S) x) = Nat.card K ^ 2)
    (hdr : (graph (Reduction.reducedFamily L S)).Adj d r)
    (hpath : RootPathTransitive (graph (Reduction.reducedFamily L S)) (Reduction.G₀ L S) d 2)
    (er : (graphLocalGroup (Reduction.reducedFamily L S) r ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) r)) ≃* SL(2,K))
    (C : Subgroup (Reduction.G₀ L S)) [IsMulCommutative C]
    (hCx : C ≤ stabilizer (Reduction.reducedFamily L S) x)
    (hCE : C ≤ stabilizer (Reduction.reducedFamily L S) d ⊓ stabilizer (Reduction.reducedFamily L S) r)
    (ho : Odd (Nat.card C))
    (hdis : Disjoint C ((stabilizer (Reduction.reducedFamily L S) d ⊓
      stabilizer (Reduction.reducedFamily L S) r : Subgroup (Reduction.G₀ L S)).pCoreIn 2))
    (hsup : C ⊔ (stabilizer (Reduction.reducedFamily L S) d ⊓
      stabilizer (Reduction.reducedFamily L S) r : Subgroup (Reduction.G₀ L S)).pCoreIn 2 =
      stabilizer (Reduction.reducedFamily L S) d ⊓ stabilizer (Reduction.reducedFamily L S) r)
    (hTorus : Nonempty ((C ⊓ graphLocalGroup (Reduction.reducedFamily L S) x :
      Subgroup (Reduction.G₀ L S)) ≃* Kˣ))
    (cZ : letI : Algebra (ZMod 2) K := ZMod.algebra K 2
      BinaryConjugationSection (graphLocalGroup (Reduction.reducedFamily L S) x)
        (Z (Reduction.reducedFamily L S) x) ⊥
        (((specialLinearNatural (k := K) 2).restrictScalars (k := ZMod 2)).comp
          (ex.toMonoidHom.comp (QuotientGroup.mk' (pCore 2
            (graphLocalGroup (Reduction.reducedFamily L S) x)))))) : False := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Finite C := Finite.of_injective (inclusion hCx) (inclusion_injective _)
  let T := C ⊓ graphLocalGroup Γ x
  let R := Q Γ x ⊓ centralizer (T : Set (Reduction.G₀ L S))
  let N := Q Γ beta ⊓ Q Γ d
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hK : Nat.card K = 2^n := hKF.trans hF
  have hKfour : 4 ≤ Nat.card K := by
    rw [hK]
    exact (show 2^2 ≤ 2^n from Nat.pow_le_pow_right (by decide) (by omega))
  have hTo : Odd (Nat.card T) := ho.of_dvd_nat (card_dvd_of_le (show T ≤ C from inf_le_left))
  have hTne : T ≠ ⊥ := by
    intro he
    obtain ⟨e⟩ := hTorus
    have hh : Nat.card T = Nat.card K - 1 := (Nat.card_congr e.toEquiv).trans (Nat.card_units K)
    rw [he,card_bot] at hh
    omega
  obtain ⟨hdd,hNcard,hNQ,hNN,hsection,M,hMQ,hMN,_,_,_,⟨cM⟩,hMesc⟩ :=
    reduced_core_adapted_natural_pair h hb hd hne hb3 ex ed hKF hn hF hres hsec hNspan
      hωd hc hVcard hZcard hZspan hZxcard
  have hZN : Z Γ x ≤ N := by
    apply le_inf
    · exact Z_le_Q_of_dist_lt_b Γ (fun v => (source_Z_Q_U ht v).1) (source_kernel_sylow ht hB hS)
        x beta (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hb,hb3]; decide)
    · exact Z_le_Q_of_dist_lt_b Γ (fun v => (source_Z_Q_U ht v).1) (source_kernel_sylow ht hB hS)
        x d (by rw [SimpleGraph.dist_eq_one_iff_adj.mpr hd,hb3]; decide)
  have hcomm : ⁅N,T⁆ ≤ Z Γ x := adjacent_core_odd_commutator ht hB hS hd
    (core_escape_of_intersection_obstruction Γ (Reduction.reduced_graph_core_obstruction h d x hd.symm))
    ex hNN hdd (hZspan ▸ le_sup_right) T inf_le_right hTo
  obtain ⟨hRN,hNR,hMfix⟩ := adjacent_core_odd_fixed_decomposition ht ex hn hK hsection
    hNQ hNN hZN M T inf_le_right hTo hTne hcomm cZ cM
  have hTesc : ¬ T ≤ ballKernel Γ r 1 := adapted_actor_not_le_remote_kernel ht hB hS hdr er hKfour
    M T hMQ (inf_le_right.trans hMN) (inf_le_left.trans (hCE.trans inf_le_left)) hTo hMfix hMesc
  have hnT : C ≤ normalizer (T : Set (Reduction.G₀ L S)) :=
    ((le_centralizer C).trans (centralizer_le inf_le_left)).trans (centralizer_le_normalizer _)
  have hnR : C ≤ normalizer (R : Set (Reduction.G₀ L S)) :=
    (le_inf (hCx.trans (stabilizer_normalizes_Q Γ x))
      (hnT.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hRr : R ≤ Q Γ r := adapted_fixed_le_remote_core ht hB hS hdr hpath er C R T hCE hdis hsup
    (hRN.trans inf_le_right) hnR inf_le_left
    (le_centralizer_iff.mp (show R ≤ centralizer (T : Set (Reduction.G₀ L S)) from inf_le_right)) hTesc
  change N = R ⊔ Z Γ x at hNR
  have hbpos : 1 ≤ b Γ := by rw [hb3]; decide
  have hNV : N ≤ V Γ d 1 := by
    rw [←hNspan]
    refine le_inf ?_ hNQ
    rw [hNR]
    exact sup_le hRr ((CommutingNontrivial.Z_neighbor_le_V Γ hd.symm).trans (hNspan ▸ inf_le_left))
  exact adapted_intersection_span_contradiction ht hB hS hd hbpos N hNV hNN (hNspan ▸ inf_le_right)
    (Nat.card K) (by omega) hNcard (by rw [hKF]; exact hVcard)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
