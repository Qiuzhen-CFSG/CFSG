module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionCoreCollapse
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.ResidualFusion
public import Theory.GroupTheory.FixedPointFreeCyclicJoin
public import Theory.SpecificGroups.SL2.ThreeResidualCore

/-!
# The original RQ marking in the opposite centralizer

The cubic actor puts C_R(w) in the global centralizer's derived subgroup.
Since X=C_R(w)⟨w⟩, every index-two subgroup containing w contains X. The
marked C₄*SL₂(3) residual centralizer also lies in every such subgroup:
its cyclic factor lies in X and its SL₂(3) factor is two-perfect.

The subgroup C_U(w) is nonabelian, so X C_U(w) has at least 64 elements.
The original Sylow factorization T=R C_T(w) and [T:RQ]=2 bound
C_T(w)∩RQ by 64. This proves their equality and the required containment
in J=⟨w⟩L_w. The Sylow index argument upgrades containment to the exact
source equality C_T(w)∩J=C_T(w)∩RQ.

The application uses the proved perfect-residual product, not a splitting
of the entire centralizer. The concrete G₂(2) quotient remains explicit;
its construction and final core collapse belong to qt-e-14322-core-collapse.

Source: Aschbacher--Smith 14.3.22, printed p.999, with the residual-cover
correction in docs/quasithin-proof-basis.md.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs

include hc s

/-- The cubic actor puts the whole parabolic core centralizer in C_G(w)'. -/
theorem source_triple_core_centralizer_le_commutator :
    (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ centralizer ({tripleProduct d a} : Set G) ≤
      ⁅centralizer ({tripleProduct d a} : Set G), centralizer ({tripleProduct d a} : Set G)⁆ := by
  classical
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let C := centralizer ({tripleProduct d a} : Set G)
  have hcore : (sourceResidual M Mc).pCoreIn 2 = R :=
    (source_parabolic_residual_core_structure_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2.2.1
  have haR : a ∈ normalizer (R : Set G) := by
    rw [← hcore]
    exact (sourceResidual M Mc).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ _) s.actor_mem
  apply le_commutator_of_fixedPointFree (R ⊓ C) C inf_le_right a
    (inf_normalizer_le_normalizer_inf ⟨haR, C.le_normalizer (s.actor_centralizes_product hc)⟩)
    (s.actor_centralizes_product hc)
  intro x hx hxa
  exact mem_bot.mp (s.actor_fixed ▸ ⟨hx.1, mem_centralizer_singleton_iff.mpr hxa.symm.eq⟩)

/-- The source abelian span is C_R(w) times the marked involution. -/
theorem source_triple_span_eq_core_centralizer_sup
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    span F = ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓
      centralizer ({tripleProduct d a} : Set G)) ⊔ zpowers (tripleProduct d a) := by
  classical
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let X := span F
  let w := tripleProduct d a
  let A := R ⊓ centralizer ({w} : Set G)
  let W := zpowers w
  let := hc.abelian
  have hAX : A ≤ X := (source_triple_core_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s).1.le.trans inf_le_left
  have hWX : W ≤ X := zpowers_le.mpr (s.product_mem_span hc)
  have hwR : w ∉ R := by
    intro hw
    exact source_triple_outside_transfer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
      (mem_sup_right hw)
  have hw2 := (source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).involution
  have hdis : Disjoint A W := by
    apply Subgroup.disjoint_def.mpr
    intro x hxA hxW
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hxW)
    rw [Finset.mem_range, hw2] at hn
    interval_cases n
    · simpa using he.symm
    · have hx : x = w := by simpa using he.symm
      exact (hwR (hx ▸ hxA.1)).elim
  have hnorm : W ≤ normalizer (A : Set G) :=
    (show W ≤ centralizer (A : Set G) from fun x hx y hy =>
      congrArg Subtype.val (mul_comm' (⟨y,hAX hy⟩ : X) ⟨x,hWX hx⟩)).trans
        (Subgroup.centralizer_le_normalizer _)
  have hAc : Nat.card A = 16 := (source_triple_core_orbit_and_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s).2
  have hXc : Nat.card X = 32 := by
    obtain ⟨ee⟩ := source_triple_span_model hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
    rw [Nat.card_congr ee.toEquiv, Nat.card_prod, Nat.card_prod]
    change Nat.card (ZMod 4) * Nat.card (ZMod 4) * Nat.card (ZMod 2) = 32
    norm_num [Nat.card_zmod]
  symm
  apply eq_of_le_of_card_ge (sup_le hAX hWX)
  rw [card_sup_of_disjoint_of_normalizes A W hdis hnorm, hAc, Nat.card_zpowers, hw2, hXc]

/-- An index-two subgroup of the opposite centralizer containing w contains X. -/
theorem source_triple_span_le_index_two
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (J : Subgroup G) (hJC : J ≤ centralizer ({tripleProduct d a} : Set G))
    (hi : J.relIndex (centralizer ({tripleProduct d a} : Set G)) = 2)
    (hw : tripleProduct d a ∈ J) : span F ≤ J := by
  let C := centralizer ({tripleProduct d a} : Set G)
  let N := J.subgroupOf C
  let : N.Normal := Subgroup.normal_of_index_eq_two hi
  let : IsCyclic (C ⧸ N) := isCyclic_of_prime_card (show Nat.card (C ⧸ N) = 2 from hi)
  have hD : ⁅C,C⁆ ≤ J := by
    rw [← C.map_subtype_commutator]
    have hcomm : _root_.commutator C ≤ N :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    have hh := map_mono (f := C.subtype) hcomm
    rwa [map_subgroupOf_eq_of_le hJC] at hh
  rw [source_triple_span_eq_core_centralizer_sup hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself]
  exact sup_le ((source_triple_core_centralizer_le_commutator hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s).trans hD)
    (zpowers_le.mpr hw)

/-- The marked C₄*SL₂(3) centralizer is contained in every such index-two subgroup. -/
theorem source_triple_residual_centralizer_le_index_two
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (J : Subgroup G) (hJC : J ≤ centralizer ({tripleProduct d a} : Set G))
    (hi : J.relIndex (centralizer ({tripleProduct d a} : Set G)) = 2)
    (hw : tripleProduct d a ∈ J) :
    localResidual F ⊓ centralizer ({tripleProduct d a} : Set G) ≤ J := by
  let C := centralizer ({tripleProduct d a} : Set G)
  let N := J.subgroupOf C
  let : N.Normal := Subgroup.normal_of_index_eq_two hi
  have hp : IsPGroup 2 (C ⧸ N) := IsPGroup.of_card (n := 1) (by simpa only [Subgroup.relIndex, Subgroup.index_eq_card, Nat.pow_one] using hi)
  obtain ⟨B,_,⟨eB⟩,_,_,hgen⟩ := source_triple_residual_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  have hBC : B ≤ C := (hgen ▸ le_sup_right).trans inf_le_right
  have hBperf : IsPPerfect 2 B := GLS3.Chapter5.SchurPresentation.sl23_twoPerfect.of_surjective
    eB.symm.toMonoidHom eB.symm.surjective
  have hBJ : B ≤ J := by
    let f := (QuotientGroup.mk' N).comp (inclusion hBC)
    have hf := hBperf.hom_eq_one_of_isPGroup hp f
    intro b hb
    exact (QuotientGroup.eq_one_iff (inclusion hBC ⟨b,hb⟩)).mp
      (DFunLike.congr_fun hf ⟨b,hb⟩)
  rw [← hgen]
  apply sup_le _ hBJ
  apply (zpowers_le.mpr ?_).trans
    (source_triple_span_le_index_two hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself J hJC hi hw)
  obtain ⟨_,h1,h2⟩ := s.factors_mem_span hc
  exact (span F).mul_mem h1 h2

/-- The fixed subgroup in U is nonabelian; its double centralizer has order four. -/
theorem source_triple_U_centralizer_nonabelian :
    ¬ IsMulCommutative (F.U ⊓ centralizer ({tripleProduct d a} : Set G) : Subgroup G) := by
  intro hab
  let P := F.U ⊓ centralizer ({tripleProduct d a} : Set G)
  let := hab
  have hP : P ≤ F.U ⊓ centralizer (P : Set G) := le_inf inf_le_left P.le_centralizer
  rw [source_triple_U_double_centralizer
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s] at hP
  have hh := card_le_of_le hP
  rw [Nat.card_zpowers,
    (source_triple_pair_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s).2.2.1] at hh
  have hp := (source_triple_residual_centralizer_sylow
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s).1
  change Nat.card P = 16 at hp
  omega

/-- The original RQ intersection is generated by X and C_U(w), and has order 64. -/
theorem source_triple_RQ_generation_and_card
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let B := ((T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G)) ⊓
      ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2)
    B = span F ⊔ (F.U ⊓ centralizer ({tripleProduct d a} : Set G)) ∧
      Nat.card B = 64 := by
  dsimp only
  classical
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let Q := F.H.pCoreIn 2
  let C := centralizer ({tripleProduct d a} : Set G)
  let S := (T : Subgroup G) ⊓ C
  let B := S ⊓ (R ⊔ Q)
  let P := F.U ⊓ C
  let X := span F
  let K := X ⊔ P
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have dg := rankTwo_closure_geometry h F hne
  have hUQ : F.U ≤ Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    change Q ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hh hx
    exact hy
  have hRQT := source_parabolic_core_sylow_index_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hXB : X ≤ B := by
    apply le_inf
    · apply le_inf (conjugateSubgroupClosure_le_self _ _)
      let := hc.abelian
      intro x hx
      exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (mul_comm' (⟨x,hx⟩ : X) ⟨_,s.product_mem_span hc⟩))
    · change span F ≤ R ⊔ Q
      rw [source_triple_span_eq_core_centralizer_sup
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself]
      exact sup_le (inf_le_left.trans le_sup_left)
        ((zpowers_le.mpr (source_triple_residual_centralizer_reduction
          hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s).1).trans le_sup_right)
  have hPB : P ≤ B :=
    le_inf (le_inf (inf_le_left.trans (hUQ.trans hQT)) inf_le_right)
      (inf_le_left.trans (hUQ.trans le_sup_right))
  have hKB : K ≤ B := sup_le hXB hPB
  have hXc : Nat.card X = 32 := by
    obtain ⟨ee⟩ := source_triple_span_model
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
    rw [Nat.card_congr ee.toEquiv, Nat.card_prod, Nat.card_prod]
    change Nat.card (ZMod 4) * Nat.card (ZMod 4) * Nat.card (ZMod 2) = 32
    norm_num [Nat.card_zmod]
  have hXK : X ≤ K := le_sup_left
  have hXne : X ≠ K := by
    intro heq
    have hPX : P ≤ X := heq ▸ le_sup_right
    let := hc.abelian
    exact source_triple_U_centralizer_nonabelian
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
      (IsMulCommutative.of_comm (fun x y : P => Subtype.ext
        (congrArg (fun k : X => (k : G))
          (mul_comm' (⟨x,hPX x.property⟩ : X) ⟨y,hPX y.property⟩))))
  have hKi : 2 ≤ X.relIndex K := by
    have hp := (X.subgroupOf K).index_ne_zero_of_finite
    have hn : X.relIndex K ≠ 1 := fun hh =>
      hXne (le_antisymm hXK (relIndex_eq_one.mp hh))
    change X.relIndex K ≠ 0 at hp
    omega
  have hKc : 64 ≤ Nat.card K := by
    have hh := relIndex_mul_card_of_le hXK
    rw [hXc] at hh
    omega
  have hSne : B ≠ S := by
    intro heq
    have hSRQ : S ≤ R ⊔ Q := heq ▸ inf_le_right
    have hTRQ : (T : Subgroup G) ≤ R ⊔ Q := by
      rw [source_triple_sylow_frattini
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself]
      exact sup_le le_sup_left hSRQ
    have he : R ⊔ Q = (T : Subgroup G) := le_antisymm (sup_le hRQT.1 hQT) hTRQ
    have hh := hRQT.2
    rw [he, relIndex_self] at hh
    contradiction
  have hBi : 2 ≤ B.relIndex S := by
    have hp := (B.subgroupOf S).index_ne_zero_of_finite
    have hn : B.relIndex S ≠ 1 := fun hh =>
      hSne (le_antisymm inf_le_left (relIndex_eq_one.mp hh))
    change B.relIndex S ≠ 0 at hp
    omega
  have hBc : Nat.card B ≤ 64 := by
    have hh := relIndex_mul_card_of_le (show B ≤ S from inf_le_left)
    rw [source_triple_sylow_centralizer_card
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself] at hh
    nlinarith
  have heq : K = B := eq_of_le_of_card_ge hKB (hBc.trans hKc)
  exact ⟨heq.symm, le_antisymm hBc (hKc.trans (card_le_of_le hKB))⟩

/-- Any index-two subgroup containing the opposite involution contains the
literal RQ intersection of the original Sylow centralizer. -/
theorem source_triple_RQ_le_index_two
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (J : Subgroup G) (hJC : J ≤ centralizer ({tripleProduct d a} : Set G))
    (hi : J.relIndex (centralizer ({tripleProduct d a} : Set G)) = 2)
    (hw : tripleProduct d a ∈ J) :
    ((T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G)) ⊓
      ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2) ≤ J := by
  rw [(source_triple_RQ_generation_and_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).1]
  apply sup_le
  · exact source_triple_span_le_index_two
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself J hJC hi hw
  · have hUK : F.U ≤ localResidual F := by
      let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
      obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
      let := he
      have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
      have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
      exact U_le_embedded_twoResidual_of_full_orthogonal F dg hZ hne hr
    exact (inf_le_inf_right _ hUK).trans (source_triple_residual_centralizer_le_index_two
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself J hJC hi hw)

/-- The genuine residual product supplies the source RQ containment. Its only
recognition premise is the quotient by the literal cyclic subgroup. -/
theorem source_triple_RQ_le_residual_product
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (ew : (ResidualFusion.C (tripleProduct d a) ⧸ ResidualFusion.W (tripleProduct d a)) ≃*
      Atlas.G2.Model (ZMod 2)) :
    ((T : Subgroup G) ⊓ ResidualFusion.C (tripleProduct d a)) ⊓
      ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2) ≤
        ResidualFusion.J (tripleProduct d a) :=
  source_triple_RQ_le_index_two hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
    (ResidualFusion.J (tripleProduct d a)) (ResidualFusion.J_le_C _)
    (ResidualFusion.join_index _ ew) (mem_sup_left (mem_zpowers _))

/-- The exact source marking: both index-two intersections in the original
Sylow centralizer agree. No splitting of the full centralizer is used. -/
theorem source_triple_RQ_eq_residual_product_intersection
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (ew : (ResidualFusion.C (tripleProduct d a) ⧸ ResidualFusion.W (tripleProduct d a)) ≃*
      Atlas.G2.Model (ZMod 2)) :
    ((T : Subgroup G) ⊓ ResidualFusion.C (tripleProduct d a)) ⊓
        ResidualFusion.J (tripleProduct d a) =
      ((T : Subgroup G) ⊓ ResidualFusion.C (tripleProduct d a)) ⊓
        ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2) := by
  let C := ResidualFusion.C (tripleProduct d a)
  let S := (T : Subgroup G) ⊓ C
  let J := ResidualFusion.J (tripleProduct d a)
  let B := S ⊓ ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2)
  have hBJ : B ≤ S ⊓ J := le_inf inf_le_left (source_triple_RQ_le_residual_product
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself ew)
  have hneJ : S ⊓ J ≠ S := by
    intro hh
    have hSJ : S ≤ J := hh ▸ inf_le_right
    obtain ⟨P,hP⟩ := source_triple_global_sylow
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
    have hp : (P : Subgroup C) ≤ J.subgroupOf C := by
      intro x hx
      apply hSJ
      change (x : G) ∈ (T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G)
      rw [← hP]
      exact mem_map_of_mem C.subtype hx
    have hd := index_dvd_of_le hp
    change J.relIndex C ∣ (P : Subgroup C).index at hd
    rw [ResidualFusion.join_index _ ew] at hd
    exact P.not_dvd_index hd
  have hi : 2 ≤ (S ⊓ J).relIndex S := by
    have hp := ((S ⊓ J).subgroupOf S).index_ne_zero_of_finite
    have hn : (S ⊓ J).relIndex S ≠ 1 := fun hh =>
      hneJ (le_antisymm inf_le_left (relIndex_eq_one.mp hh))
    change (S ⊓ J).relIndex S ≠ 0 at hp
    omega
  have hcS : Nat.card S = 128 := source_triple_sylow_centralizer_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hcB : Nat.card B = 64 := (source_triple_RQ_generation_and_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).2
  symm
  apply eq_of_le_of_card_ge hBJ
  have hh := relIndex_mul_card_of_le (show S ⊓ J ≤ S from inf_le_left)
  rw [hcS] at hh
  rw [hcB]
  nlinarith

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
