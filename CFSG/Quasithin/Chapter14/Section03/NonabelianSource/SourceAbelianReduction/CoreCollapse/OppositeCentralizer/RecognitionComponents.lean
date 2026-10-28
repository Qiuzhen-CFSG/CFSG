module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.RecognitionCoreCollapse
public import CFSG.Quasithin.Chapter1.Section02.ComponentDichotomy.OddCore
public import Theory.GroupTheory.CComponent.SolvableSupplementInvolution
public import CFSG.Quasithin.Chapter1.Section01
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.ResidualFusion
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# The original marked component and quotient centralizer

The cubic actor lies in the two-residual of the relative normalizer of V.
Its fixed-point-free action gives V=[V,O²(N_C(V))], so the original z
centralizes the odd core of C=C_G(w). It also centralizes the two-core.
The generalized-Fitting argument underlying 1.2.11 now produces an ordinary
component: an empty ordinary layer would put z in O₂(C), contradicting
the proved two-core exclusion. This step requires no unproved membership
of z in a selected C-component.

Apply 1.1.6 and the full known-simple 1.1.5 catalogue with the original
z and T. All six model/action alternatives, including central covers and
sporadic groups, are retained. The selected action has order two, fixes
an actual Sylow subgroup of order dividing 128, and has fixed subgroup
of order dividing 384.

The literal C_H(w) has order 384: its order-48 residual centralizer and
order-128 Sylow subgroup intersect in C_U(w), of order sixteen. The
original nonfusion of z and w, together with w~wz, makes the full
centralizer of the image of z in C/⟨w⟩ lift to C_H(w). Its order is 192.
These are the component and local markings for the remaining G₂(2)
quotient recognition, owned by qt-e-14322-core-collapse.

Source: Aschbacher--Smith 14.3.22, printed p.999, using 1.2.11 and
1.1.5--6, pp.501--503,508; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- The actual cubic actor supplies the full relative-normalizer residual commutator on V. -/
theorem CubicTriple.plane_relative_residual_commutator
    {F : InvariantFlag T V 2} {L : Subgroup G} {z d a : G}
    [IsElementaryAbelian 2 V] (s : CubicTriple F L z d a)
    (hc : CyclicTIInput F L) (hLN : L ≤ normalizer (V : Set G)) :
    ⁅V, (pResidual 2 (centralizer ({tripleProduct d a} : Set G) ⊓
      normalizer (V : Set G) : Subgroup G)).map
        (centralizer ({tripleProduct d a} : Set G) ⊓ normalizer (V : Set G)).subtype⁆ = V := by
  let C := centralizer ({tripleProduct d a} : Set G)
  let N := C ⊓ normalizer (V : Set G)
  have haN : a ∈ N := ⟨s.actor_centralizes_product hc, hLN s.actor_mem⟩
  have haR : a ∈ (pResidual 2 N).map N.subtype := by
    apply mem_map_of_mem N.subtype (x := ⟨a, haN⟩)
    apply mem_pResidual_of_orderOf_coprime
    rw [← orderOf_coe, s.actor_order]
    decide
  have hfix : V ⊓ centralizer (zpowers a : Set G) = ⊥ := by
    apply bot_unique
    intro v hv
    exact s.actor_fixed ▸ (show v ∈ (F.I₂ L).pCoreIn 2 ⊓ centralizer ({a} : Set G) from
      ⟨s.seed_le_core hv.1, centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers a)) hv.2⟩)
  have hcop : Nat.Coprime (Nat.card (zpowers a)) (Nat.card V) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) (zpowers a) V
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, s.actor_order, pow_one]))
      (IsElementaryAbelian.isPGroup 2 V)
  have hmove : ⁅V, zpowers a⁆ = V := by
    have hh := eq_commutator_sup_centralizer_of_solvable_coprime V (zpowers a)
      (zpowers_le.mpr (hLN s.actor_mem))
      (Group.isSolvable_of_comm fun x y => mul_comm' x y) hcop
    simpa only [hfix, sup_bot_eq] using hh.symm
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans inf_le_right)
  · exact hmove.ge.trans (commutator_mono le_rfl (zpowers_le.mpr haR))


/-- The original nonfusion marks force the full quotient centralizer to
lift to C_H(w); no recognition of the quotient is used here. -/
theorem LocalGeometry.quotient_point_centralizer_comap
    {F : InvariantFlag T V 2} {L : Subgroup G} {z w : G}
    (h : LocalGeometry F L z w) (zC : ResidualFusion.C w) (hzC : (zC : G) = z) :
    (centralizer ({QuotientGroup.mk' (ResidualFusion.W w) zC} :
      Set (ResidualFusion.C w ⧸ ResidualFusion.W w))).comap
      (QuotientGroup.mk' (ResidualFusion.W w)) =
        (F.H ⊓ ResidualFusion.C w).subgroupOf (ResidualFusion.C w) := by
  classical
  let C := ResidualFusion.C w
  let W := ResidualFusion.W w
  let q := QuotientGroup.mk' W
  have hcases (x : C) (hx : x ∈ W) : x = 1 ∨ x = ResidualFusion.point w := by
    have ho : orderOf (ResidualFusion.point w) = 2 :=
      (orderOf_coe _).symm.trans h.involution
    change x ∈ zpowers (ResidualFusion.point w) at hx
    rw [mem_zpowers_iff_mem_range_orderOf, ho] at hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hn2 : n < 2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  have hH : F.H = centralizer ({z} : Set G) := F.H_eq_centralizer (by decide) z h.point
  ext x
  change q x ∈ centralizer ({q zC} : Set (C ⧸ W)) ↔ (x : G) ∈ F.H ⊓ C
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hc
    have he : q (x * zC * x⁻¹) = q zC := by
      rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
    have hk : (x * zC * x⁻¹) / zC ∈ W := QuotientGroup.eq_iff_div_mem.mp he
    have hfix : (x : G) * z * (x : G)⁻¹ = z := by
      rcases hcases _ hk with hb | hw
      · have hh := congrArg Subtype.val (div_eq_one.mp hb)
        simpa only [coe_mul, coe_inv, hzC] using hh
      · have hh := congrArg Subtype.val (div_eq_iff_eq_mul.mp hw)
        have hconj : IsConj z (w * z) := isConj_iff.mpr ⟨x, by
          simpa only [coe_mul, coe_inv, hzC, ResidualFusion.point] using hh⟩
        exact (h.nonfusion (hconj.trans h.product_fusion.symm)).elim
    exact ⟨hH.symm ▸ mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp hfix), x.property⟩
  · intro hx
    have hc : x * zC = zC * x := Subtype.ext (by
      simpa only [coe_mul, hzC] using mem_centralizer_singleton_iff.mp (hH ▸ hx.1))
    exact (map_mul q _ _).symm.trans ((congrArg q hc).trans (map_mul q _ _))

open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
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
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs hc s

/-- The original point centralizes the odd core of the actual opposite centralizer. -/
theorem source_triple_point_centralizes_oddCore
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    z ∈ centralizer ((pPrimeCore 2 (centralizer ({tripleProduct d a} : Set G))).map
      (centralizer ({tripleProduct d a} : Set G)).subtype : Set G) := by
  let C := centralizer ({tripleProduct d a} : Set G)
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hsqt : IsStronglyQuasithin C :=
    (hG.twoLocal_sqtk (isTwoLocal_involution_centralizer hlocal.involution)).stronglyQuasithin
  have hLN : sourceResidual M Mc ≤ normalizer (rankTwoSeed T M : Set G) :=
    (sourceResidual_le M Mc).trans RankTwoHypothesis.M_normalizes_seed
  have hzcomm := (s.plane_relative_residual_commutator hc hLN).symm ▸
    (F.le_seed 1 (s.point.symm ▸ mem_zpowers z))
  exact Chapter1.relative_residual_centralizes_oddCore C (rankTwoSeed T M) hsqt
    hlocal.plane_centralizes hzcomm

/-- The generalized-Fitting centralizer argument supplies an ordinary component of C_G(w). -/
theorem source_triple_exists_component
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    ∃ D : Subgroup (centralizer ({tripleProduct d a} : Set G)),
      IsComponent (centralizer ({tripleProduct d a} : Set G)) D := by
  classical
  let C := centralizer ({tripleProduct d a} : Set G)
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hzC : z ∈ C := hlocal.plane_centralizes (F.le_seed 1 (s.point.symm ▸ mem_zpowers z))
  let zC : C := ⟨z, hzC⟩
  have hz2 : orderOf zC = 2 := by
    rw [← orderOf_coe, ← Nat.card_zpowers, ← s.point]
    simpa using F.card 1 (by decide)
  have hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t := by
    intro t ht
    exact mem_centralizer_singleton_iff.mp
      ((F.H_eq_centralizer (by decide) z s.point) ▸ (F.invariant 1 ht))
  obtain ⟨S, hS⟩ := source_triple_global_sylow
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hQT : C.pCoreIn 2 ≤ (T : Subgroup G) :=
    ((pCoreIn_le_sylow C S).trans_eq hS).trans inf_le_left
  have hco := source_triple_point_centralizes_oddCore
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  by_contra! hn
  have hE : componentLayer C = ⊥ := by
    apply bot_unique
    exact sSup_le fun D hD => (hn D hD).elim
  have hzQ : zC ∈ pCore 2 C := involution_mem_twoCore_of_layer_eq_bot hE zC hz2
    (fun x hx => Subtype.ext (hzc x (hQT (mem_map_of_mem C.subtype hx))))
    (fun x hx => Subtype.ext (hco x (mem_map_of_mem C.subtype hx)))
  exact source_triple_point_not_mem_twoCore
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
      (mem_map_of_mem C.subtype hzQ)

/-- The central two-core cannot be self-centralizing, since the original point lies outside it. -/
theorem source_triple_not_characteristicTwo
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    centralizer ({tripleProduct d a} : Set G) ∉ Chapter1.He G := by
  intro hHe
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hzC := hlocal.plane_centralizes (F.le_seed 1 (s.point.symm ▸ mem_zpowers z))
  apply source_triple_point_not_mem_twoCore
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  apply hHe
  refine ⟨hzC, ?_⟩
  rw [source_triple_twoCore_eq hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself,
    zpowers_eq_closure, centralizer_closure]
  exact hzC

/-- Lemma 1.1.6 on the original z and T, with B=⟨w⟩ and the literal global centralizer. -/
theorem source_triple_original_lemma115_setup
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (S : Sylow 2 (centralizer ({tripleProduct d a} : Set G)))
    (hS : (S : Subgroup _).map (centralizer ({tripleProduct d a} : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G)) :
    ∃ M₁ : Subgroup G, IsMaximalTwoLocal M₁ ∧
      Chapter1.Lemma115Hypotheses (centralizer ({tripleProduct d a} : Set G)) S M₁ z := by
  let C := centralizer ({tripleProduct d a} : Set G)
  let W := zpowers (tripleProduct d a)
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← s.point]
    simpa using F.card 1 (by decide)
  have hzT : z ∈ (T : Subgroup G) :=
    hc.supplement_le_sylow (hc.strict.le (s.point.symm ▸ mem_zpowers z))
  have hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t := by
    intro t ht
    exact mem_centralizer_singleton_iff.mp
      ((F.H_eq_centralizer (by decide) z s.point) ▸ (F.invariant 1 ht))
  obtain ⟨M₁, hCM₁, hM₁⟩ := Finite.exists_le_maximal (isTwoLocal_involution_centralizer hz2)
  have hWne : W ≠ ⊥ := zpowers_ne_bot.mpr (by
    intro he
    have hh := hlocal.involution
    rw [he, orderOf_one] at hh
    omega)
  have hW : IsPGroup 2 W := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hlocal.involution, pow_one])
  have hWC : W ≤ C := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCC : centralizer (W : Set G) = C := by
    change centralizer (zpowers (tripleProduct d a) : Set G) = _
    rw [zpowers_eq_closure, centralizer_closure]
  refine ⟨M₁, hM₁, ?_⟩
  apply Chapter1.lemma_1_1_6 hWne hW hWC hCC.le
    (hCC ▸ Subgroup.centralizer_le_normalizer _) S T
    (hS.le.trans inf_le_left) hz2 hzT hzc hM₁ hCM₁
  intro N hN hTN
  exact Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T N hN hTN)

/-- The complete source catalogue on every actual ordinary component, with the original marks. -/
theorem source_triple_component_catalogue
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let C := centralizer ({tripleProduct d a} : Set G)
    ∃ (S : Sylow 2 C) (M₁ : Subgroup G),
      (S : Subgroup C).map C.subtype = (T : Subgroup G) ⊓ C ∧
      Nat.card S = 128 ∧ IsMaximalTwoLocal M₁ ∧
      Chapter1.Lemma115Hypotheses C S M₁ z ∧
      (∃ D : Subgroup C, IsComponent C D) ∧
      ∀ D : Subgroup C, IsComponent C D →
        D.map C.subtype = ⁅D.map C.subtype, zpowers z⁆ ∧
        ¬ D.map C.subtype ≤ M₁ ∧ HasModelAction115 D z := by
  intro C
  obtain ⟨S, hS⟩ := source_triple_global_sylow
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨M₁, hM₁, h115⟩ := source_triple_original_lemma115_setup
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself S hS
  have hcardS : Nat.card S = 128 := by
    have hm := Nat.card_congr ((S : Subgroup C).equivMapOfInjective C.subtype
      C.subtype_injective).toEquiv
    rw [hS] at hm
    exact hm.trans (source_triple_sylow_centralizer_card
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself)
  exact ⟨S, M₁, hS, hcardS, hM₁, h115,
    source_triple_exists_component
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself,
    fun D hD => Chapter1.lemma_1_1_5_three_knownSimple hG C S M₁ z h115 D hD⟩

/-- The original point centralizer has order 384. Its residual centralizer
has order 48, its Sylow subgroup has order 128, and their intersection is
the already constructed order-sixteen subgroup C_U(w). -/
theorem source_triple_point_centralizer_card
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    Nat.card (F.H ⊓ centralizer ({tripleProduct d a} : Set G) : Subgroup G) = 384 := by
  let C := centralizer ({tripleProduct d a} : Set G)
  let H := F.H ⊓ C
  let K := localResidual F ⊓ C
  let P := (T : Subgroup G) ⊓ C
  have hKH : K ≤ H := inf_le_inf_right _ (map_subtype_le _)
  have hPH : P ≤ H := inf_le_inf_right _ (F.invariant 1)
  obtain ⟨S, hS⟩ := source_triple_local_sylow
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hres : (pResidual 2 H).map H.subtype ≤ K := le_inf
    (embedded_pResidual_mono 2 (show H ≤ F.H from inf_le_left))
    ((map_subtype_le _).trans inf_le_right)
  have hsup : K ⊔ P = H := by
    apply le_antisymm (sup_le hKH hPH)
    have he := congrArg (Subgroup.map H.subtype) (pResidual_sup_sylow_eq_top S)
    rw [Subgroup.map_sup, hS, ← MonoidHom.range_eq_map, range_subtype] at he
    exact he.symm.le.trans (sup_le_sup_right hres P)
  have hPN : P ≤ normalizer (K : Set G) :=
    (le_inf ((inf_le_left.trans (F.invariant 1)).trans
      (F.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F.H (pResidual 2 F.H))))
      (inf_le_right.trans C.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hinter : K ⊓ P = F.U ⊓ C := by
    change (localResidual F ⊓ C) ⊓ ((T : Subgroup G) ⊓ C) = _
    rw [inf_inf_inf_comm, inf_idem,
      (source_local_residual_sylow
        hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1]
  have hKcard : Nat.card K = 48 := source_triple_residual_centralizer_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  have hPcard : Nat.card P = 128 := source_triple_sylow_centralizer_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hUcard := (source_triple_residual_centralizer_sylow
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s).1
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes K P hPN
  rw [hKcard, hPcard, hinter, hUcard, hsup] at hh
  change 48 * 128 = 16 * Nat.card (F.H ⊓ centralizer ({tripleProduct d a} : Set G) : Subgroup G) at hh
  omega

/-- The marked involution centralizer has order 192 in the original
quotient C_G(w)/⟨w⟩, before that quotient is recognized. -/
theorem source_triple_quotient_point_centralizer_card
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (zC : ResidualFusion.C (tripleProduct d a)) (hzC : (zC : G) = z) :
    Nat.card (centralizer
      ({QuotientGroup.mk' (ResidualFusion.W (tripleProduct d a)) zC} :
        Set (ResidualFusion.C (tripleProduct d a) ⧸ ResidualFusion.W (tripleProduct d a)))) = 192 := by
  let w := tripleProduct d a
  let C := ResidualFusion.C w
  let W := ResidualFusion.W w
  let H := F.H ⊓ C
  let H' := H.subgroupOf C
  let q := QuotientGroup.mk' W
  let f := q.comp H'.subtype
  have hlocal := source_triple_local_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hWH : W ≤ H' := by
    apply zpowers_le.mpr
    exact ⟨F.invariant 1 hlocal.mem_sylow, mem_centralizer_singleton_iff.mpr rfl⟩
  have hker : f.ker = W.subgroupOf H' := by
    ext x
    exact QuotientGroup.eq_one_iff (x : C)
  have hkc : Nat.card f.ker = 2 := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv]
    change Nat.card (zpowers (ResidualFusion.point w)) = 2
    rw [Nat.card_zpowers, ← orderOf_coe]
    exact hlocal.involution
  have hHc : Nat.card H' = 384 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show H ≤ C from inf_le_right)).toEquiv]
    exact source_triple_point_centralizer_card
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  have hrange : f.range = centralizer ({q zC} : Set (C ⧸ W)) := by
    change (q.comp H'.subtype).range = _
    rw [MonoidHom.range_comp, range_subtype]
    have hcomap : (centralizer ({q zC} : Set (C ⧸ W))).comap q = H' :=
      hlocal.quotient_point_centralizer_comap zC hzC
    rw [← hcomap]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective W) _
  have hh := f.ker.card_mul_index
  rw [hkc, index_ker, hrange, hHc] at hh
  change 2 * Nat.card (centralizer ({q zC} : Set (C ⧸ W))) = 384 at hh
  change Nat.card (centralizer ({q zC} : Set (C ⧸ W))) = 192
  omega

/-- The catalogue is applied to an actual component, retaining its
conjugation action, a fixed Sylow subgroup, and the orders needed for the
two-local model inspection. All six model alternatives are still present. -/
theorem source_triple_marked_component
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    let C := centralizer ({tripleProduct d a} : Set G)
    ∃ (D : Subgroup C) (α : MulAut D) (P : Sylow 2 D),
      IsComponent C D ∧
      (∀ x : D, ((α x : C) : G) = z * (x : G) * z⁻¹) ∧
      ModelAction115 D α ∧ orderOf α = 2 ∧
      Nat.card P ∣ 128 ∧ (∀ x : P, α (x : D) = x) ∧
      Nat.card α.fixedSubgroup ∣ 384 := by
  intro C
  obtain ⟨S, M₁, hS, hSc, hM₁, h115, ⟨D, hD⟩, hmodels⟩ :=
    source_triple_component_catalogue
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  obtain ⟨_, hDout, α, hα, hm⟩ := hmodels D hD
  have hαne : α ≠ 1 := by
    intro he
    apply hDout
    rintro _ ⟨x, hx, rfl⟩
    apply h115.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have hh : z * (x : G) * z⁻¹ = (x : G) := by
      simpa only [he, MulAut.one_apply] using (hα ⟨x, hx⟩).symm
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hαsq : α ^ 2 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change ((α (α x) : C) : G) = (x : G)
    rw [hα, hα]
    have hzsq : z * z = 1 := by
      simpa only [h115.involution, pow_two] using pow_orderOf_eq_one z
    calc
      z * (z * (x : G) * z⁻¹) * z⁻¹ = (z * z) * (x : G) * (z * z)⁻¹ := by group
      _ = (x : G) := by rw [hzsq]; simp
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  have hPS (x : P) : ((x : D) : C) ∈ (S : Subgroup C) := by
    change (x : D) ∈ (S : Subgroup C).subgroupOf D
    rw [← hP]
    exact x.property
  let f : P →* S :=
    { toFun := fun x => ⟨((x : D) : C), hPS x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    have hh : ((x : D) : C) = ((y : D) : C) :=
      congrArg (fun t : S => (t : C)) hxy
    exact Subtype.ext (Subtype.ext hh)
  have hp : Nat.card P ∣ 128 := hSc ▸ card_dvd_of_injective f hf
  have hfix : ∀ x : P, α (x : D) = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rw [hα]
    have hc := h115.central _ (mem_map_of_mem C.subtype (hPS x))
    change ((x : D) : G) * z = z * ((x : D) : G) at hc
    rw [← hc, mul_inv_cancel_right]
  let H := F.H ⊓ C
  have hH : F.H = centralizer ({z} : Set G) := F.H_eq_centralizer (by decide) z s.point
  let j : α.fixedSubgroup →* H :=
    { toFun := fun x => ⟨((x : D) : G), by
        refine ⟨?_, ((x : D) : C).property⟩
        rw [hH]
        apply mem_centralizer_singleton_iff.mpr
        have he : z * ((x : D) : G) * z⁻¹ = ((x : D) : G) :=
          (hα (x : D)).symm.trans
            (congrArg (fun y : D => (y : G)) ((MulAut.mem_fixedSubgroup _ _).mp x.property))
        exact (mul_inv_eq_iff_eq_mul.mp he).symm⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    have hh : ((x : D) : G) = ((y : D) : G) :=
      congrArg (fun t : H => (t : G)) hxy
    exact Subtype.ext (Subtype.ext (Subtype.ext hh))
  have hcH : Nat.card H = 384 := source_triple_point_centralizer_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself
  exact ⟨D, α, P, hD, hα, hm, orderOf_eq_prime hαsq hαne,
    hp, hfix, hcH ▸ card_dvd_of_injective j hj⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
