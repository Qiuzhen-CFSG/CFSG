module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBlockLayers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChiefPlane
public import Theory.Representation.SL2.MovedElementaryDegree

public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex

/-!
# Original chief-factor bounds force degree two in the noncentral branch

The cubic fixes no nontrivial point of the original moved layer. The
noncentral PSL₂ constituent bounds that layer's order below by 2^(2n),
and the literal quotient Sylow adds log₄(2^n) to its cubic chief length.
Thus the left Sylow intersection has at least three noncentral factors.

If the right residual is a block, its propagation identifies the maximal
component's entire core commutator with the right four-space. The core
therefore contributes at most two factors; the image of a normalized
subgroup of the original Sylow in A₇ has order at most eight and contributes
at most one more. Comparison forces n=2. The previously proved nonblock
torus argument handles the other branch, so no block premise remains in
the final degree theorem. In particular n>2 forces omega-centralization.

The sharper right-block exclusion, the degree-two left-block case,
postcentralization recognition and the source component sieve remain open.
Source: Aschbacher–Smith 5.1.13, printed pp.637–638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The cubic moves at least n binary chief factors of the original moved layer,
and its original Sylow intersection adds the quotient contribution. -/
theorem LocalA7Configuration.left_cubic_chief_lower
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    n ≤ conjugationCubicLength D (layer L W) ∧
      n + Nat.log 4 (2 ^ n) ≤ conjugationCubicLength D ((T : Subgroup G) ⊓ L) ∧
      3 ≤ conjugationCubicLength D ((T : Subgroup G) ⊓ L) := by
  have hLN : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer h.sylow_normalizes
  have hLW : L ≤ normalizer (W : Set G) := le_sup_left.trans (reduced_normalizes h.reduced)
  have hUL : layer L W ≤ L := le_normalizer_iff_commutator_le_right.mp
    (h.reduced.1.trans hLN)
  have hUW : layer L W ≤ W := le_normalizer_iff_commutator_le_left.mp hLW
  let : IsElementaryAbelian 2 W := h.reduced.2.1
  let : IsElementaryAbelian 2 (layer L W) := IsElementaryAbelian.of_le hUW
  have hUcore : layer L W ≤ L.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 _) hUL (normalizer_commutator_ge_right W L)
  have hm : ⁅layer L W,L⁆ = layer L W := commutator_isPPerfect_idempotent L W
    h.local_mem.2.2.1 (IsElementaryAbelian.isPGroup 2 W) hLW
  let := Chapter1.mem_L_isPerfect h.maximal_local.1
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hsize : 2^(2*n) ≤ Nat.card (layer L W) :=
    Representation.SL2.moved_subgroup_card_bound L (layer L W) hUL h.noncentral hm
      (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm) (by have := h.exponent; omega) hF
  have hfix : layer L W ⊓ centralizer (D : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hUW).trans_eq (a.cubic_fixed_eq_bot h hH hgen c d).1)
  have hlower : n ≤ conjugationCubicLength D (layer L W) := by
    unfold conjugationCubicLength
    rw [←inf_relIndex_right,inf_comm,hfix,relIndex_bot_left]
    have hh := Nat.log_mono_right (b := 4) hsize
    rw [pow_mul] at hh
    change Nat.log 4 (4^n) ≤ _ at hh
    rw [Nat.log_pow (by decide : 1 < 4)] at hh
    exact hh
  have hDL : D ≤ L := ((d.cubic_le.trans inf_le_left).trans c.left_le).trans inf_le_left
  have hDN : D ≤ normalizer (((T : Subgroup G) ⊓ L) : Set G) :=
    ((d.cubic_le.trans inf_le_left).trans c.left_le).trans inf_le_right
  have he := CubicEscape.psl_cubic_sylow_length h.linear h.sylow_normalizes d.cubic_card hDL hDN
  have hlow := hlower.trans (conjugationCubicLength_mono D hUcore)
  have htotal : n + Nat.log 4 (2^n) ≤ conjugationCubicLength D ((T : Subgroup G) ⊓ L) := by
    rw [he]
    omega
  refine ⟨hlower,htotal,?_⟩
  have hn := h.exponent
  have hlog : 1 ≤ Nat.log 4 (2 ^ n) := Nat.le_log_of_pow_le (by decide)
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ n by omega))
  omega



/-- The right block gives at most three factors on the original left Sylow
intersection: two on the four-space and at most one in the A7 quotient. -/
theorem LocalA7Configuration.right_block_chief_upper
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hb : ChapterC.IsChiBlockIn (pResidual 2 H)) :
    conjugationCubicLength D ((T : Subgroup G) ⊓ L) ≤ 3 := by
  let M := K ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let C := D.subgroupOf M
  let S := ((T : Subgroup G) ⊓ L).subgroupOf M
  let U := (localOmegaModule T K).subgroupOf M
  let Q := pCore 2 M
  let R := Q ⊔ S
  have hDK : D ≤ K := (d.cubic_le.trans inf_le_right).trans a.contains
  have hDM : D ≤ M := hDK.trans le_sup_left
  have hSM : (T : Subgroup G) ⊓ L ≤ M := inf_le_left.trans le_sup_right
  have hC3 : IsPGroup 3 C := IsPGroup.of_card (n := 1)
    ((Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv).trans d.cubic_card)
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  have hUQ : U ≤ Q := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  have hQP : Q ≤ (P : Subgroup M) := pCore_isPGroup.le_sylow_of_normal P
  have hRP : R ≤ (P : Subgroup M) := sup_le hQP (fun _ hx => hx.1)
  have hDN : D ≤ normalizer (((T : Subgroup G) ⊓ L) : Set G) :=
    ((d.cubic_le.trans inf_le_left).trans c.left_le).trans inf_le_right
  have hCS : C ≤ normalizer (S : Set M) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    change (x : G) * (y : G) * (x : G)⁻¹ ∈ (T : Subgroup G) ⊓ L
    exact le_normalizer_iff.mp hDN x.val hx y.val (show y.val ∈ (T : Subgroup G) ⊓ L from hy)
  have hCR : C ≤ normalizer (R : Set M) :=
    (le_inf (show C ≤ normalizer (Q : Set M) from le_normalizer_of_normal) hCS).trans
      (normalizer_inf_normalizer_le_normalizer_sup Q S)
  have hmove := (a.right_block_layers h hH hgen c d hb).2.2
  have hQC : ⁅Q,C⁆ ≤ U := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hDM,map_subgroupOf_eq_of_le a.reduced.1]
    exact (commutator_mono le_rfl hDK).trans_eq hmove
  have hlenQ : conjugationCubicLength C Q ≤ 2 := by
    rw [←CubicComparison.length_eq_of_commutator_le C Q U hC3 pCore_isPGroup hUQ
      le_normalizer_of_normal le_normalizer_of_normal hQC]
    have hh := CubicComparison.length_le_log_card C U
    have hc : Nat.card U = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe a.reduced.1).toEquiv).trans (a.four h hH hgen c d)
    rw [hc] at hh
    exact hh
  obtain ⟨q,hq,_,hk⟩ := a.four_action h (a.four h hH hgen c d)
  let f := q.subgroupMap R
  have hf : Function.Surjective f := q.subgroupMap_surjective R
  have hker : Q.subgroupOf R = f.ker := by
    ext r
    change r.val ∈ Q ↔ f r = 1
    rw [show Q = q.ker from hk.symm]
    constructor
    · intro hr
      exact Subtype.ext hr
    · intro hr
      exact congrArg Subtype.val hr
  let e : (R ⧸ Q.subgroupOf R) ≃* R.map q := QuotientGroup.liftEquiv _ hf hker
  have hcardP : Nat.card (P.mapSurjective hq) = 8 := by
    rw [Sylow.card_eq_multiplicity,nat_card_alternatingGroup,Nat.card_eq_fintype_card]
    norm_num [Nat.factorial]
    rw [show (2520 : ℕ).factorization 2 = 3 by
      rw [show 2520 = 2^3*315 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),Nat.factorization_pow]
      simp [Nat.prime_two.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 315)]]
    norm_num
  have hcard : Nat.card (R ⧸ Q.subgroupOf R) ≤ 8 := by
    rw [Nat.card_congr e.toEquiv]
    exact (card_le_of_le (map_mono hRP)).trans_eq hcardP
  have hsection := CubicComparison.section_length_le_log_card C R Q hC3
    (P.isPGroup'.to_le hRP) le_sup_left hCR le_normalizer_of_normal
  have hlog : Nat.log 4 (Nat.card (R ⧸ Q.subgroupOf R)) ≤ 1 :=
    (Nat.log_mono_right hcard).trans (by decide : Nat.log 4 8 ≤ 1)
  have hmono := conjugationCubicLength_mono C (show S ≤ R from le_sup_right)
  rw [CubicComparison.length_subgroupOf D ((T : Subgroup G) ⊓ L) M hDM hSM] at hmono
  change conjugationCubicLength D ((T : Subgroup G) ⊓ L) ≤ conjugationCubicLength C R at hmono
  unfold sectionCubicLength at hsection
  omega

/-- The right-block branch forces degree two from its original chief factors. -/
theorem LocalA7Configuration.degree_two_of_right_block
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hb : ChapterC.IsChiBlockIn (pResidual 2 H)) : n = 2 := by
  have hlo := (a.left_cubic_chief_lower h hH hgen c d).2.1
  have hup := a.right_block_chief_upper h hH hgen c d hb
  have hn := h.exponent
  have hlog : 1 ≤ Nat.log 4 (2^n) := Nat.le_log_of_pow_le (by decide)
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ n by omega))
  omega

/-- Both original block alternatives now force the original field degree two. -/
theorem LocalA7Configuration.degree_two
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) : n = 2 := by
  rcases a.degree_two_or_right_block h hH hgen c d with he | hb
  · exact he
  · exact a.degree_two_of_right_block h hH hgen c d hb

/-- The completed FF reduction and both chief-factor branches give degree two
under the original noncentral source inputs, with no block premise. -/
theorem localCartan_noncentral_degree_two
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) : n = 2 := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  exact a.degree_two h hH hgen c d


/-- The original higher-degree branch centralizes omega, without a block guard. -/
theorem localCartan_centralizes_of_degree_gt_two
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hn : 2 < n) : X ≤ omegaCentralizer T := by
  by_contra hc
  have he := localCartan_noncentral_degree_two h hH hgen c hY d hc
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
