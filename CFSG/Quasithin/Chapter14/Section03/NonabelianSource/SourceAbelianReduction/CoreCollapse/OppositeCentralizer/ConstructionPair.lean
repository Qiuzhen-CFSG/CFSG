module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.ConstructionTransfer
public import Theory.GroupTheory.PResidual.AutomorphismCentralizer

/-!
# The order-four pair and the opposite involution's local centralizers

Write t=dᵃdᵃ², so the source opposite involution is w=dt. An element of
U moving the seed plane interchanges its two points other than z. Since
H=C_G(z) normalizes D, it also interchanges the corresponding cyclic
four-groups. Normality of U in H then puts t in U, and the three-square
relation gives t²=z. This uses the literal cyclic factors and their original
conjugation convention, without a new six-letter coordinate calculation.

The two-residual of H centralizes D because Aut(D) is a two-group. Thus
C_{O²(H)}(w)=C_{O²(H)}(t), and w lies in Q. The abelian span and the already
proved R-orbit on Vw give T=R C_T(w). Their exact orders yield
[T:C_T(w)]=4 and |C_T(w)|=128 on the supplied T. The final source constructor
discharges the cyclic-TI premise and retains all these literal markings.

The C₄*SL₂(3) recognition of the residual centralizer, local Sylow and
omega-center geometry, and marked global centralizer recognition remain
with qt-e-14322-core-collapse. These local calculations do not assert them.
Source: Aschbacher--Smith, 14.3.22, printed p.999.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Recognition Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

omit [Finite G] in
/-- The original point centralizer normalizes its centralizing supplement. -/
theorem supplement_normalized (F : InvariantFlag T V 2) :
    F.H ≤ normalizer (supplement F : Set G) := by
  apply le_trans _ inf_normalizer_le_normalizer_inf
  exact le_inf (F.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
    ((le_normalizer_conjugateSpanBy V F.H).trans (normalizer_le_normalizer_centralizer F.U))

/-- The two-residual fixes the cyclic supplement pointwise. -/
theorem CyclicTIInput.residual_centralizes {F : InvariantFlag T V 2} {L : Subgroup G}
    (hc : CyclicTIInput F L) : localResidual F ≤ centralizer (supplement F : Set G) := by
  let := hc.cyclic
  apply embedded_pResidual_le_centralizer_of_aut_isPGroup 2 F.H (supplement F)
    (supplement_normalized F)
  apply IsPGroup.of_card (n := 1)
  rw [IsCyclic.card_mulAut, hc.card]
  decide

omit [Finite G] in
/-- The product of the two other cyclic generators has square z. -/
theorem CubicTriple.pair_square {F : InvariantFlag T V 2} {L : Subgroup G}
    {z d a : G} (s : CubicTriple F L z d a) (hc : CyclicTIInput F L) :
    ((MulAut.conj a⁻¹) d * (MulAut.conj (a ^ 2)⁻¹) d) ^ 2 = z := by
  let := hc.abelian
  obtain ⟨_, h1, h2⟩ := s.factors_mem_span hc
  have hcomm : Commute ((MulAut.conj a⁻¹) d) ((MulAut.conj (a ^ 2)⁻¹) d) :=
    congrArg Subtype.val (mul_comm' (⟨_, h1⟩ : span F) ⟨_, h2⟩)
  rw [hcomm.mul_pow, ← map_pow, ← map_pow, s.square]
  have hz2 : z ^ 2 = 1 := by
    have hz : orderOf z = 2 := by
      rw [← Nat.card_zpowers, ← s.point]
      simpa using F.card 1 (by decide)
    exact hz ▸ pow_orderOf_eq_one z
  have hzInv : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hz2)
  exact (eq_inv_of_mul_eq_one_right (by simpa only [mul_assoc] using s.squares)).trans hzInv

omit [Finite G] in
/-- A conjugate cyclic factor is determined by the image of its square. -/
private theorem conjugate_generator_mem_of_square
    {F : InvariantFlag T V 2} {L : Subgroup G} {z d a u : G}
    (s : CubicTriple F L z d a)
    (he : (MulAut.conj u) ((MulAut.conj a⁻¹) z) = (MulAut.conj (a ^ 2)⁻¹) z) :
    (MulAut.conj u) ((MulAut.conj a⁻¹) d) ∈ zpowers ((MulAut.conj (a ^ 2)⁻¹) d) := by
  let b := a ^ 2 * u * a⁻¹
  have hb : b ∈ F.H := by
    rw [F.H_eq_centralizer (by decide) z s.point]
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    have hh := congrArg (MulAut.conj (a ^ 2)) he
    simp only [MulAut.conj_apply, inv_inv] at hh
    change b * z * b⁻¹ = z
    dsimp only [b]
    convert hh using 1 <;> group
  have hd : d ∈ supplement F := s.generator ▸ mem_zpowers d
  have hbd : (MulAut.conj b) d ∈ supplement F :=
    (mem_normalizer_iff.mp (supplement_normalized F hb) d).mp hd
  have hm := mem_map_of_mem (MulAut.conj (a ^ 2)⁻¹).toMonoidHom hbd
  rw [← s.generator, MonoidHom.map_zpowers] at hm
  change (MulAut.conj (a ^ 2)⁻¹) ((MulAut.conj b) d) ∈
    zpowers ((MulAut.conj (a ^ 2)⁻¹) d) at hm
  have heq : (MulAut.conj u) ((MulAut.conj a⁻¹) d) =
      (MulAut.conj (a ^ 2)⁻¹) ((MulAut.conj b) d) := by
    simp only [MulAut.conj_apply, inv_inv, b]
    group
  exact heq ▸ hm

private theorem mul_mem_of_conjugate_four {U : Subgroup G} {x y u : G}
    (hu : u ∈ U) (hxN : x ∈ normalizer (U : Set G))
    (hy4 : orderOf y = 4) (hy2 : y ^ 2 ∈ U)
    (hxy : (MulAut.conj u) x ∈ zpowers y) (hx4 : orderOf x = 4) : x * y ∈ U := by
  classical
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hxy)
  have hi4 : i < 4 := by simpa only [Finset.mem_range, hy4] using hi
  have ho : orderOf ((MulAut.conj u) x) = 4 := ((MulAut.conj u).orderOf_eq x).trans hx4
  have hm : x * ((MulAut.conj u) x)⁻¹ ∈ U := by
    have hconj := (mem_normalizer_iff.mp hxN u).mp hu
    convert U.mul_mem hconj (U.inv_mem hu) using 1
    simp only [MulAut.conj_apply]
    group
  interval_cases i
  · simp only [pow_zero] at he
    rw [← he, orderOf_one] at ho
    contradiction
  · simpa only [pow_one, ← he, pow_two, mul_assoc, inv_mul_cancel_left] using
      U.mul_mem hm hy2
  · rw [← he, orderOf_pow, hy4] at ho
    contradiction
  · have hyfour : y ^ 4 = 1 := hy4 ▸ pow_orderOf_eq_one y
    have hy3 : y ^ 3 = y⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      simpa only [← pow_succ] using hyfour
    rw [hy3] at he
    simpa only [← he, inv_inv] using hm

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

/-- The two other cyclic factors multiply inside the original quaternion closure. -/
theorem source_triple_pair_mem_U :
    (MulAut.conj a⁻¹) d * (MulAut.conj (a ^ 2)⁻¹) d ∈ F.U := by
  let V := rankTwoSeed T M
  let z₁ := (MulAut.conj a⁻¹) z
  let z₂ := (MulAut.conj (a ^ 2)⁻¹) z
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have dg := rankTwo_closure_geometry h F hne
  have hZ := source_center_eq_point_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hUT : F.U ≤ (T : Subgroup G) := normalized_pSubgroup_le_sylow T F.H F.U
    (F.invariant 1) F.U_le_H (le_normalizer_conjugateSpanBy _ _) dg.two
  have hVN : (T : Subgroup G) ≤ normalizer (V : Set G) := by
    simpa only [F.last] using F.invariant 2
  have hzV : z ∈ V := F.le_seed 1 (s.point.symm ▸ mem_zpowers z)
  have hz₁V : z₁ ∈ V := (mem_normalizer_iff.mp
    (h.L_normalizes_seed ((sourceResidual M Mc).inv_mem s.actor_mem)) z).mp hzV
  have hz₂V : z₂ ∈ V := (mem_normalizer_iff.mp
    (h.L_normalizes_seed ((sourceResidual M Mc).inv_mem
      ((sourceResidual M Mc).pow_mem s.actor_mem 2))) z).mp hzV
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← s.point]
    simpa using F.card 1 (by decide)
  have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz2
  have hz₁1 : z₁ ≠ 1 := fun hh => hz1 ((MulAut.conj a⁻¹).injective
    (hh.trans (map_one _).symm))
  have hz₂1 : z₂ ≠ 1 := fun hh => hz1 ((MulAut.conj (a ^ 2)⁻¹).injective
    (hh.trans (map_one _).symm))
  have hVc : Nat.card V = 4 := by simpa [F.last] using F.card 2 (by decide)
  have hset : (V : Set G) = {1, z, z₁, z₂} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact V.one_mem
      · exact hzV
      · exact hz₁V
      · exact hz₂V
    · change Nat.card V ≤ _
      rw [hVc, Set.ncard_eq_four.mpr
        ⟨1,z,z₁,z₂,hz1.symm,hz₁1.symm,hz₂1.symm,
          s.squares_distinct.1,s.squares_distinct.2.1,s.squares_distinct.2.2,rfl⟩]
    · exact Set.toFinite _
  have hnotcent : ¬ F.U ≤ centralizer (V : Set G) := by
    intro hUV
    have hVZ : V ≤ F.Vi 1 := by
      rw [← hZ, ZU, centerIn_eq_inf_centralizer]
      exact le_inf (le_conjugateSpanBy _ _) (le_centralizer_iff.mp hUV)
    have hh := card_le_of_le hVZ
    rw [hVc, show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide)] at hh
    omega
  obtain ⟨u, huU, humove⟩ := SetLike.not_le_iff_exists.mp hnotcent
  have huH := F.U_le_H huU
  have huz : (MulAut.conj u) z = z := by
    have hh := mem_centralizer_singleton_iff.mp
      ((F.H_eq_centralizer (by decide) z s.point) ▸ huH)
    exact mul_inv_eq_iff_eq_mul.mpr hh
  have hz₂prod : z₂ = z * z₁ := by
    have hzpow : z ^ 2 = 1 := hz2 ▸ pow_orderOf_eq_one z
    have hz₁pow : z₁ ^ 2 = 1 := by
      dsimp only [z₁]
      rw [← map_pow,hzpow,map_one]
    have hinv (x : G) (hx : x ^ 2 = 1) : x⁻¹ = x :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx)
    have hcomm : Commute z z₁ :=
      congrArg Subtype.val (mul_comm' (⟨z,hzV⟩ : V) ⟨z₁,hz₁V⟩)
    exact (eq_inv_of_mul_eq_one_right s.squares).trans
      (by rw [mul_inv_rev, hinv z hzpow, hinv z₁ hz₁pow]; exact hcomm.eq.symm)
  have hmove₁ : (MulAut.conj u) z₁ ≠ z₁ := by
    intro he
    apply humove
    intro v hv
    rw [hset] at hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    have hfix₂ : (MulAut.conj u) z₂ = z₂ := by
      rw [hz₂prod,map_mul,huz,he]
    rcases hv with rfl | rfl | rfl | rfl
    · simp
    · exact (mul_inv_eq_iff_eq_mul.mp huz).symm
    · exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · exact (mul_inv_eq_iff_eq_mul.mp hfix₂).symm
  have hswap : (MulAut.conj u) z₁ = z₂ := by
    have hm := (mem_normalizer_iff.mp (hVN (hUT huU)) z₁).mp hz₁V
    change (MulAut.conj u) z₁ ∈ (V : Set G) at hm
    rw [hset] at hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with hm | hm | hm | hm
    · exact False.elim (hz₁1 ((MulAut.conj u).injective (hm.trans (map_one _).symm)))
    · exact False.elim (s.squares_distinct.1
        ((MulAut.conj u).injective (huz.trans hm.symm)))
    · exact False.elim (hmove₁ hm)
    · exact hm
  have hd4 : orderOf d = 4 := by rw [← Nat.card_zpowers,s.generator,hc.card]
  obtain ⟨_, hxX, _⟩ := s.factors_mem_span hc
  apply mul_mem_of_conjugate_four huU
    ((le_normalizer_conjugateSpanBy V F.H) (F.invariant 1
      ((conjugateSubgroupClosure_le_self _ _) hxX)))
    (((MulAut.conj (a ^ 2)⁻¹).orderOf_eq d).trans hd4)
  · rw [← map_pow,s.square]
    exact le_conjugateSpanBy V F.H hz₂V
  · exact conjugate_generator_mem_of_square s hswap
  · exact ((MulAut.conj a⁻¹).orderOf_eq d).trans hd4

/-- The literal pair is an order-four element of U, with the original point as square. -/
theorem source_triple_pair_geometry :
    let t := (MulAut.conj a⁻¹) d * (MulAut.conj (a ^ 2)⁻¹) d
    t ∈ F.U ∧ t ^ 2 = z ∧ orderOf t = 4 ∧ tripleProduct d a = d * t := by
  intro t
  have ht2 : t ^ 2 = z := s.pair_square hc
  have hz2 : orderOf z = 2 := by
    rw [← Nat.card_zpowers, ← s.point]
    simpa using F.card 1 (by decide)
  have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz2
  have ht4 : t ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ht2, ← hz2, pow_orderOf_eq_one]
  exact ⟨source_triple_pair_mem_U hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s,
    ht2, orderOf_eq_four_of_fourth_power ht4 (ht2 ▸ hz1), by simp only [t,tripleProduct,mul_assoc]⟩

/-- The opposite involution lies in Q; its residual centralizer is exactly
the centralizer of the marked order-four pair in the original U. -/
theorem source_triple_residual_centralizer_reduction :
    tripleProduct d a ∈ F.H.pCoreIn 2 ∧
    localResidual F ⊓ centralizer ({tripleProduct d a} : Set G) =
      localResidual F ⊓ centralizer
        ({(MulAut.conj a⁻¹) d * (MulAut.conj (a ^ 2)⁻¹) d} : Set G) := by
  let t := (MulAut.conj a⁻¹) d * (MulAut.conj (a ^ 2)⁻¹) d
  obtain ⟨htU, _, _, hwt⟩ := source_triple_pair_geometry
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  have hdD : d ∈ supplement F := s.generator ▸ mem_zpowers d
  have dg := rankTwo_closure_geometry (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e) F hne
  have hUQ := le_pCoreIn_of_normalizes dg.two F.U_le_H (le_normalizer_conjugateSpanBy _ _)
  refine ⟨hwt.symm ▸ (F.H.pCoreIn 2).mul_mem hdD.1 (hUQ htU), ?_⟩
  ext x
  simp only [mem_inf,mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hx, hxc⟩
    have hxd : Commute x d := (hc.residual_centralizes hx d hdD).symm
    refine ⟨hx, ?_⟩
    have he : x * (d * t) = (d * t) * x := by simpa only [hwt] using hxc
    have hh : d * (x * t) = d * (t * x) := by
      calc
        _ = x * (d * t) := by rw [← mul_assoc, ← hxd.eq, mul_assoc]
        _ = (d * t) * x := he
        _ = _ := mul_assoc _ _ _
    exact mul_left_cancel hh
  · rintro ⟨hx, hxt⟩
    have hxd : Commute x d := (hc.residual_centralizes hx d hdD).symm
    exact ⟨hx, hwt.symm ▸ (hxd.mul_right hxt).eq⟩

/-- The original Sylow subgroup factors through the actual opposite centralizer;
no conjugation or rechoice of T is required for this factorization. -/
theorem source_triple_sylow_frattini
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    (T : Subgroup G) = (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔
      ((T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G)) := by
  let := hc.abelian
  have h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  have hRT := (source_parabolic_core_sylow_index_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1
  have hwV : tripleProduct d a ∉ rankTwoSeed T M := by
    intro hw
    exact source_triple_outside_transfer hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
      (mem_sup_right (s.seed_le_core hw))
  have hw1 : tripleProduct d a ≠ 1 := fun he => hwV (he ▸ (rankTwoSeed T M).one_mem)
  apply eq_sup_centralizer_of_involution_coset (T : Subgroup G)
    ((F.I₂ (sourceResidual M Mc)).pCoreIn 2) (rankTwoSeed T M) (span F) (tripleProduct d a)
    hRT hc.seed_le (s.product_mem_span hc) (s.involution_of_ne_one hc hw1).2 hwV
    (le_sup_right.trans hc.normalized)
  · simpa only [F.last] using F.invariant 2
  · exact source_span_omega hG T hempty hM hu hmany hcard e F hc s
  · exact (source_triple_core_orbit_and_card
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s).1

/-- The centralizer of the literal opposite involution has index four in T. -/
theorem source_triple_sylow_centralizer_index
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    ((T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G)).relIndex
      (T : Subgroup G) = 4 := by
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let S := (T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G)
  have hRT : R ≤ (T : Subgroup G) := (source_parabolic_core_sylow_index_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).1
  have hcore : (sourceResidual M Mc).pCoreIn 2 = R :=
    (source_parabolic_residual_core_structure_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs).2.2.1
  have hTN : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    rw [← hcore]
    exact (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e).sylow_normalizes_L.trans
      (normalizer_le_normalizer_characteristic_image _ _)
  have hjoin : R ⊔ S = (T : Subgroup G) := (source_triple_sylow_frattini
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself).symm
  have hinter : R ⊓ S = R ⊓ centralizer ({tripleProduct d a} : Set G) := by
    dsimp only [S]
    rw [← inf_assoc, inf_eq_left.mpr hRT]
  have hRc : Nat.card R = 64 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hRcard, _⟩ :=
      source_elementary_factors_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    exact hRcard
  have hCc : Nat.card (R ⊓ S : Subgroup G) = 16 := by
    rw [hinter]
    exact (source_triple_core_orbit_and_card
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hc s).2
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes R S (inf_le_left.trans hTN)
  rw [hRc,hCc,hjoin] at hprod
  have hi := relIndex_mul_card_of_le (show S ≤ (T : Subgroup G) from inf_le_left)
  have hpos : 0 < Nat.card S := Nat.card_pos
  change S.relIndex (T : Subgroup G) = 4
  nlinarith

omit s in
/-- The cyclic-four supplement fixes the orders of the original H and T. -/
theorem source_cyclic_supplement_local_orders :
    Nat.card F.H = 4608 ∧ Nat.card T = 512 := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg, he, _, _, _, _, _⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨dU⟩ := quaternion_closure_of_full_orthogonal F dg hZ hne hr
  let Q := F.H.pCoreIn 2
  let D := supplement F
  have hUQ : F.U ≤ Q := le_pCoreIn_of_normalizes dg.two F.U_le_H
    (le_normalizer_conjugateSpanBy _ _)
  have hUD : F.U ⊓ D = F.Vi 1 := by
    change F.U ⊓ (Q ⊓ centralizer (F.U : Set G)) = F.Vi 1
    rw [← inf_assoc, inf_eq_left.mpr hUQ]
    exact (centerIn_eq_inf_centralizer F.U).symm.trans hZ
  have hQ : Q = F.U ⊔ D := core_eq_U_sup_centralizer F dg hZ dU
  have hQc : Nat.card Q = 64 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes F.U D
      (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
    rw [dU.card,hc.card,hUD, show Nat.card (F.Vi 1) = 2 by simpa using F.card 1 (by decide),
      ← hQ] at hh
    omega
  have hHc : Nat.card F.H = 4608 := by
    let q := QuotientGroup.mk' F.terminalHatAction.ker
    have hk : q.ker = pCore 2 F.H := by
      rw [QuotientGroup.ker_mk',terminal_kernel_of_center_point F dg hZ]
    have hQi : Nat.card (pCore 2 F.H) = 64 := by
      simpa only [Q,pCoreIn,card_map_of_injective F.H.subtype_injective] using hQc
    obtain ⟨ee, _, _⟩ := hr
    have hdot : Nat.card F.TerminalHdot = 72 :=
      (Nat.card_congr (ee.trans topEquiv).toEquiv).trans
        ChapterG.Section09.FittingRecognition.Four.card_orthogonalFour
    have hh := q.ker.card_mul_index
    rw [index_ker,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      Nat.card_congr topEquiv.toEquiv,hk,hQi,hdot] at hh
    exact hh.symm
  refine ⟨hHc, ?_⟩
  have hTc : Nat.card (T.subtype (F.invariant 1)) = 512 := by
    rw [Sylow.card_eq_multiplicity]
    change 2 ^ (Nat.card F.H).factorization 2 = 512
    rw [hHc]
    decide +kernel
  exact (Nat.card_congr (subgroupOfEquivOfLe (F.invariant 1)).toEquiv).symm.trans hTc

/-- The actual C_T(w) has order 128, the local input to its eventual Sylow recognition. -/
theorem source_triple_sylow_centralizer_card
    (hself : FactorSelfCentralizing F (sourceResidual M Mc)) :
    Nat.card ((T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G) : Subgroup G) = 128 := by
  have hi := relIndex_mul_card_of_le
    (show (T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G) ≤ (T : Subgroup G) from inf_le_left)
  rw [source_triple_sylow_centralizer_index hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself,
    (source_cyclic_supplement_local_orders hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc).2] at hi
  omega

omit hc s in
/-- Construct one source triple together with its marked order-four reduction
and centralizer of index four in the supplied Sylow subgroup. -/
theorem source_opposite_residual_reduction
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hproper : F.Vi 1 < supplement F) :
    ∃ z d a t : G, CubicTriple F (sourceResidual M Mc) z d a ∧
      tripleProduct d a ∈ F.H.pCoreIn 2 ∧ orderOf (tripleProduct d a) = 2 ∧
      t = (MulAut.conj a⁻¹) d * (MulAut.conj (a ^ 2)⁻¹) d ∧
      t ∈ F.U ∧ t ^ 2 = z ∧ orderOf t = 4 ∧ tripleProduct d a = d * t ∧
      localResidual F ⊓ centralizer ({tripleProduct d a} : Set G) =
        localResidual F ⊓ centralizer ({t} : Set G) ∧
      (T : Subgroup G) = (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔
        ((T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G)) ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer ({tripleProduct d a} : Set G) : Subgroup G) = 128 := by
  have hc := source_cyclicTIInput hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper
  obtain ⟨z,d,a,s,_,hw⟩ := source_triple_involution hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc
  obtain ⟨htU,ht2,hto,hwt⟩ := source_triple_pair_geometry hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  obtain ⟨hwQ,hC⟩ := source_triple_residual_centralizer_reduction hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  exact ⟨z,d,a,_,s,hwQ,hw,rfl,htU,ht2,hto,hwt,hC,
    source_triple_sylow_frattini hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself,
    source_triple_sylow_centralizer_card hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s hself⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
