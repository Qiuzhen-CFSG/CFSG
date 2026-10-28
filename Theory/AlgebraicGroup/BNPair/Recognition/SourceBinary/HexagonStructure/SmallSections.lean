module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MiddleSection
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.TorusIrreducibility
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# Small linear root sections and middle-root centrality

The actual R_j-action on X/Y is trivial when |X/Y| < 2^(2b) and
L_j is PSL₂(2ᵇ), b > 1. The effective quotient is no larger than X/Y.
Simplicity of the concrete binary PSL₂ model makes a nontrivial effective
action faithful, contradicting the proved representation bound. The actual
odd reflection–unipotent product and coprime Frattini faithfulness then
remove the action on X/Y itself. No unknown-group simplicity or perfectness
is assumed. The restriction b > 1 is available on the unequal-parameter
branch, and includes the acting field of order four.

Cartan irreducibility gives the literal middle-root intersection dichotomy.
A normal linear root in a Cartan-invariant two-subgroup is central: its
nonzero intersection with the center fills the root. Applied after the torus
step identifies the derived subgroup with the middle root, this proves
centrality under both the radical and the other rank-one group, followed
by all four vanishing mixed commutators, with exact right-conjugation words.
The derived-subgroup identification is an explicit preceding premise; it
and the two nonzero mixed commutators and irreducibility are not asserted
here. The original/geometric applications are in SmallSections at CFSG.

Source: Fong–Seitz I (4B), (5D), and (6E), printed pp.26–27,44.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates GTwoSource Theory.PSL2.SemilinearCoverage
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
  (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
  (μ : localGroup Q split j ≃* PSL(2,F)) (s : RootReflection Q split j)

private theorem oddProduct_ne_one : oddProduct Q split j hKj μ s ≠ 1 := by
  intro he
  have hs : (s.val : X ⧸ Q.D) = (oddPartner Q split j hKj μ s : X ⧸ Q.D)⁻¹ := by
    apply mul_eq_one_iff_eq_inv.mp
    simpa only [oddProduct_coe, coe_one] using congrArg Subtype.val he
  have hu : (s.val : X ⧸ Q.D) ∈ split.U := by
    rw [hs]
    exact split.U.inv_mem (simpleRoot_le Q split j (oddPartner_mem_root Q split j hKj μ s))
  have hn : (s.val : X ⧸ Q.D) = 1 := mem_bot.mp
    (split.unipotent_inf_N ▸ (show (s.val : X ⧸ Q.D) ∈ split.U ⊓ Q.tits.N from ⟨hu,s.val.property⟩))
  have hn' : s.val = 1 := Subtype.ext hn
  exact (Q.tits.involutions _ (Q.simple_mem j)).1
    (s.class_eq.symm.trans (by rw [hn',map_one]))

include hKj μ s in
/-- The literal section action vanishes below the binary linear degree bound. -/
theorem linear_small_section_action (d : RootSection Q split j)
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b)
    (hsmall : Nat.card d.Carrier < 2^(2*b)) : d.action = 1 := by
  have hlarge : 3 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ b by omega)
    norm_num at hh ⊢
    omega
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : IsSimpleGroup (SL2 F) := (Theory.PSL2.sl2QuotientEquiv F).isSimpleGroup
  let : IsSimpleGroup (rankOne Q split j) := (alignedPinning Q split j hKj μ s).symm.isSimpleGroup
  have hsize : Nat.card d.EffectiveCarrier ≤ Nat.card d.Carrier :=
    index_antitone (show d.denominator ≤ d.effectiveDenominator from by
      rw [d.effectiveDenominator_eq]; exact le_sup_right)
  have heff : d.effectiveAction = 1 := by
    rcases (inferInstance : d.effectiveAction.ker.Normal).eq_bot_or_eq_top with hk | hk
    · have hf := d.effectiveRepresentation_injective (d.effectiveAction.ker_eq_bot_iff.mp hk)
      have hd := linear_effectiveSection_card_bound Q split j hKj μ s d hf hb hF
      exact False.elim (not_lt_of_ge (hd.trans hsize) hsmall)
    · exact MonoidHom.ker_eq_top_iff.mp hk
  have hc : oddProduct Q split j hKj μ s ∈ d.action.ker :=
    d.action_eq_one_of_odd _ (oddProduct_order_coprime Q split j hKj μ s)
      (by rw [heff]; rfl)
  rcases (inferInstance : d.action.ker.Normal).eq_bot_or_eq_top with hk | hk
  · rw [hk, mem_bot] at hc
    exact (oddProduct_ne_one Q split j hKj μ s hc).elim
  · exact MonoidHom.ker_eq_top_iff.mp hk

/-- A normalized subgroup of the radical, as a section with trivial denominator. -/
@[expose] def subgroupSection (A : Subgroup (X ⧸ Q.D))
    (hA : A ≤ simpleRemainder Q split j)
    (hn : rankOne Q split j ≤ normalizer (A : Set _)) : RootSection Q split j where
  numerator := A
  le_radical := hA
  normalized := hn
  denominator := ⊥
  invariant _ := Subgroup.map_bot _

include hKj μ s in
/-- A small invariant subgroup is centralized in the original finite quotient. -/
theorem linear_small_subgroup_centralized (A : Subgroup (X ⧸ Q.D))
    (hA : A ≤ simpleRemainder Q split j)
    (hn : rankOne Q split j ≤ normalizer (A : Set _))
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b)
    (hsmall : Nat.card A < 2^(2*b)) :
    ⁅rankOne Q split j,A⁆ = ⊥ := by
  let d := subgroupSection Q split j A hA hn
  have hd : d.action = 1 := linear_small_section_action Q split j hKj μ s d hb hF
    (by
      change Nat.card (A ⧸ (⊥ : Subgroup A)) < _
      rwa [Nat.card_congr (QuotientGroup.quotientBot (G := A)).toEquiv])
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro r hr
  apply mem_centralizer_iff.mpr
  intro a ha
  have he : d.action ⟨r,hr⟩ (QuotientGroup.mk (⟨a,ha⟩ : d.numerator)) =
      QuotientGroup.mk (⟨a,ha⟩ : d.numerator) := by rw [hd]; rfl
  rw [d.action_mk] at he
  have hv := QuotientGroup.eq_iff_div_mem.mp he
  change d.numeratorAction ⟨r,hr⟩ ⟨a,ha⟩ / (⟨a,ha⟩ : d.numerator) ∈ (⊥ : Subgroup A) at hv
  have hh := congrArg Subtype.val (div_eq_one.mp (mem_bot.mp hv))
  change r*a*r⁻¹ = a at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The derived subgroup is normalized by the whole Cartan as well as R_j. -/
theorem radical_commutator_normalized (hK : simpleRemainder Q split j ≤ localKernel Q j) :
    Q.tits.standardParabolic {Q.simple j} ≤
      normalizer ((⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ : Subgroup (X ⧸ Q.D)) : Set _) := by
  intro r hr
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (remainder_parabolic_normalizes Q split j hK hr)]

/-- The actual Cartan irreducibility gives the source middle-root dichotomy. -/
theorem middle_root_derived_dichotomy
    (i : Fin 2) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,F))
    (hK : simpleRemainder Q split j ≤ localKernel Q j) :
    rootAt Q split i (Q.simple j*Q.simple i) ≤
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ∨
    Disjoint (rootAt Q split i (Q.simple j*Q.simple i))
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
  by_cases hz : C ⊓ D = ⊥
  · exact Or.inr (disjoint_iff.mpr hz)
  · left
    have hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer ((C ⊓ D : Subgroup (X ⧸ Q.D)) : Set _) :=
      (le_inf (rootAt_torus_normalizes Q split i _)
        (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans
          (radical_commutator_normalized Q split j hK)))).trans inf_normalizer_le_normalizer_inf
    have he := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split i μi hKi
      (Q.simple j*Q.simple i) (C ⊓ D) inf_le_left hz hH
    rw [←he]
    exact inf_le_right

/-- A root normal in a Cartan-invariant two-subgroup is centralized by it.
The nonzero central intersection is forced by the p-group fixed-point theorem;
the actual Cartan irreducibility then fills the whole root. -/
theorem normal_linear_root_centralized
    (i : Fin 2) (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,F)) (w : Weyl Q)
    (V : Subgroup (X ⧸ Q.D)) (hVU : V ≤ split.U)
    (hCV : rootAt Q split i w ≤ V)
    (hVC : V ≤ normalizer (rootAt Q split i w : Set _))
    (hHV : Q.tits.B ⊓ Q.tits.N ≤ normalizer (V : Set _)) :
    ⁅V,rootAt Q split i w⁆ = ⊥ := by
  let C := rootAt Q split i w
  let D := C.subgroupOf V
  let : D.Normal := normal_subgroupOf_of_le_normalizer hVC
  let : Nontrivial C := (C.nontrivial_iff_ne_bot).mpr (rootAt_ne_bot Q split i w)
  let : Nontrivial D := (subgroupOfEquivOfLe hCV).toEquiv.nontrivial
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.of_injective
    (inclusion hVU) (inclusion_injective _)⟩
  obtain ⟨x,hx,hxz⟩ := exists_nontrivial_center_mem_normal (p := 2) D
  have hxcent : ((x : V) : X ⧸ Q.D) ∈ centralizer (V : Set (X ⧸ Q.D)) := by
    apply mem_centralizer_iff.mpr
    intro v hv
    exact congrArg Subtype.val (mem_center_iff.mp hxz ⟨v,hv⟩)
  have hne : C ⊓ centralizer (V : Set (X ⧸ Q.D)) ≠ ⊥ := by
    intro he
    have h1 : ((x : V) : X ⧸ Q.D) = 1 := mem_bot.mp (he ▸ ⟨x.property,hxcent⟩)
    exact hx (Subtype.ext (Subtype.ext h1))
  have hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer
      ((C ⊓ centralizer (V : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) : Set _) :=
    (le_inf (rootAt_torus_normalizes Q split i w)
      (hHV.trans (normalizer_le_normalizer_centralizer V))).trans inf_normalizer_le_normalizer_inf
  have he := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split i μi hKi w
    (C ⊓ centralizer (V : Set (X ⧸ Q.D))) inf_le_left hne hH
  rw [commutator_comm]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [←he]
  exact inf_le_right

/-- The torus-derived identity makes the middle root central in its radical. -/
theorem derived_middle_root_radical_centralized (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,F))
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (hderived : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
      rootAt Q split i (Q.simple j*Q.simple i)) :
    ⁅simpleRemainder Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ := by
  apply normal_linear_root_centralized Q split i hKi μi _ _ inf_le_left
    (exchanged_roots_le_remainder Q split hm i j hij).2
  · rw [←hderived]
    exact (show simpleRemainder Q split j ≤ Q.tits.standardParabolic {Q.simple j} from
      inf_le_left.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))).trans
      (radical_commutator_normalized Q split j hK)
  · exact inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans
      (remainder_parabolic_normalizes Q split j hK))

include hKj μ s in
/-- An invariant middle root below the linear degree bound is centralized by R_j. -/
theorem invariant_middle_root_centralized (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hn : rankOne Q split j ≤ normalizer
      (rootAt Q split i (Q.simple j*Q.simple i) : Set _))
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b)
    (hsmall : Nat.card (simpleRoot Q split i) < 2^(2*b)) :
    ⁅rankOne Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ := by
  apply linear_small_subgroup_centralized Q split j hKj μ s _
    (exchanged_roots_le_remainder Q split hm i j hij).2 hn hb hF
  simpa only [rootAt, card_rightConjugate] using hsmall

include hKj μ s in
/-- The preceding derived identity supplies invariance; the size bound supplies centrality. -/
theorem derived_middle_root_centralized (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hderived : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
      rootAt Q split i (Q.simple j*Q.simple i))
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b)
    (hsmall : Nat.card (simpleRoot Q split i) < 2^(2*b)) :
    ⁅rankOne Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ := by
  apply invariant_middle_root_centralized Q split j hKj μ s hm i hij _ hb hF hsmall
  rw [←hderived]
  exact (rankOne_le_parabolic Q split j).trans (radical_commutator_normalized Q split j hKj)

private theorem conjugate_commutator (A B : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ n = ⁅rightConjugate A n,rightConjugate B n⁆ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', map_commutator]

/-- Conjugating the actual U_j--middle-root centrality by s_i and then s_j
produces the two crossed zero relations with the source's literal words. -/
private theorem middle_root_zero_relations_of_centralized
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (hVC : ⁅simpleRemainder Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hRC : ⁅rankOne Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ ∧
    ⁅rootAt Q split i (Q.simple j*Q.simple i),rootAt Q split i (Q.simple j)⁆ = ⊥ ∧
    ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j)⁆ = ⊥ ∧
    ⁅rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j)⁆ = ⊥ := by
  have hUC : ⁅simpleRoot Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ :=
    bot_unique ((commutator_mono (show simpleRoot Q split j ≤ rankOne Q split j from le_sup_left)
      le_rfl).trans hRC.le)
  have hs (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
  have hBE := congrArg (fun A => rightConjugate A (representative (Q.simple i) : X ⧸ Q.D)) hUC
  rw [conjugate_commutator, ←rootAt_eq Q split j (Q.simple i) _ (representative_spec _),
    rootAt_right Q split i _ _ _ (representative_spec _), mul_assoc, hs, mul_one] at hBE
  have hBE' : ⁅rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j)⁆ = ⊥ :=
    hBE.trans (by simp only [rightConjugate, comap_equiv_eq_map_symm', Subgroup.map_bot])
  have hAD := congrArg (fun A => rightConjugate A (representative (Q.simple j) : X ⧸ Q.D)) hBE'
  rw [conjugate_commutator, rootAt_right Q split j _ _ _ (representative_spec _),
    rootAt_right Q split i _ _ _ (representative_spec _), hs, rootAt_one, commutator_comm] at hAD
  refine ⟨bot_unique ((commutator_mono (simpleRoot_le_other_remainder Q split hm i j hij)
    le_rfl).trans hVC.le), ?_, ?_, hBE'⟩
  · rw [commutator_comm]
    exact bot_unique ((commutator_mono (exchanged_roots_le_remainder Q split hm i j hij).1
      le_rfl).trans hVC.le)
  · exact hAD.trans (by simp only [rightConjugate, comap_equiv_eq_map_symm', Subgroup.map_bot])

include hKj μ s in
/-- Once the torus step identifies the actual derived subgroup, its small
order and the actual Cartan action force the four zero commutators of (6E)(b).
The earlier derived-subgroup identification remains explicit. -/
theorem derived_middle_root_zero_relations
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (hderived : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
      rootAt Q split i (Q.simple j*Q.simple i))
    {b : ℕ} (hb : 1 < b) (hF : Nat.card F = 2^b)
    (hsmall : Nat.card (simpleRoot Q split i) < 2^(2*b)) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ ∧
    ⁅rootAt Q split i (Q.simple j*Q.simple i),rootAt Q split i (Q.simple j)⁆ = ⊥ ∧
    ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j)⁆ = ⊥ ∧
    ⁅rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j)⁆ = ⊥ :=
  middle_root_zero_relations_of_centralized Q split j hm i hij
    (derived_middle_root_radical_centralized Q split j hm i hij hKi μi hKj hderived)
    (derived_middle_root_centralized Q split j hKj μ s hm i hij hderived hb hF hsmall)

/-- For an opposite root of order two the normalizer centralizes its middle
conjugate directly. No identification or perfectness of either original
factor is required for this implication. -/
theorem binary_derived_middle_root_centralized
    (i : Fin 2) (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (hderived : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
      rootAt Q split i (Q.simple j*Q.simple i))
    (hsmall : Nat.card (simpleRoot Q split i) = 2) :
    ⁅simpleRemainder Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ ∧
    ⁅rankOne Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ := by
  have hc : Nat.card (rootAt Q split i (Q.simple j*Q.simple i)) = 2 := by
    simpa only [rootAt, card_rightConjugate] using hsmall
  have hn : Q.tits.standardParabolic {Q.simple j} ≤
      centralizer (rootAt Q split i (Q.simple j*Q.simple i) : Set _) := by
    apply le_trans _ (normalizer_le_centralizer_of_card_two _ hc)
    rw [←hderived]
    exact radical_commutator_normalized Q split j hK
  exact ⟨commutator_eq_bot_iff_le_centralizer.mpr
    ((show simpleRemainder Q split j ≤ Q.tits.standardParabolic {Q.simple j} from
      inf_le_left.trans (split.U_le.trans (Q.tits.B_le_standardParabolic _))).trans hn),
    commutator_eq_bot_iff_le_centralizer.mpr ((rankOne_le_parabolic Q split j).trans hn)⟩

/-- All four source zero relations also hold in the smallest opposite-root case. -/
theorem binary_derived_middle_root_zero_relations
    (hm : rotationOrder Q = 6) (i : Fin 2) (hij : i ≠ j)
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (hderived : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ =
      rootAt Q split i (Q.simple j*Q.simple i))
    (hsmall : Nat.card (simpleRoot Q split i) = 2) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ ∧
    ⁅rootAt Q split i (Q.simple j*Q.simple i),rootAt Q split i (Q.simple j)⁆ = ⊥ ∧
    ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j)⁆ = ⊥ ∧
    ⁅rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j)⁆ = ⊥ := by
  obtain ⟨hVC,hRC⟩ := binary_derived_middle_root_centralized Q split j i hK hderived hsmall
  exact middle_root_zero_relations_of_centralized Q split j hm i hij hVC hRC

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
