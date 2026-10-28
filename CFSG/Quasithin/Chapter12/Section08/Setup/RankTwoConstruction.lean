module

public import CFSG.Quasithin.Chapter12.Section08.Setup.RankTwoBase
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.LocalKernel
public import Theory.GroupAction.FourAutomorphismOrbit
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# The dimension-two action and local source setup

Starting solely with Hypothesis 12.8.1(2), the literal action of LT on
V = ⟨Ω₁(Z(T))ᴹ⟩ has kernel O₂(LT) and image of order six. Since V has
order four, this is its full automorphism group. Functoriality of the
two-residual identifies the L-image with its order-three subgroup. Thus L
is transitive on nonidentity vectors and equal-order subgroups of V;
the subgroup transporter below uses the source's right-conjugation convention.

The original relative L-normality and characteristic two give O₂(L) ≠ 1.
Uniqueness of the maximal two-local over LT then identifies M with N_G(L).
For every actual invariant flag, its point lies in Ω₁(Z(T)). The original
centralizer escape prevents Ω₁(Z(T)) from being V, so it equals that point.
The point stabilizer in the order-three L-image is trivial, giving L₁ = 1.

The full M_V-action is expressed by its literal centralizer quotient and
its value on quotient representatives. The final applications supply every
rank-two setup input to LocalKernel and the existing SourceGeometry APIs.
Flag existence and the independent transporter implication remain with the
setup assembly; no Chapter 12.2 implication or full L-action is an input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis 12.8.1(2), Notation 12.8.2 and Lemma 12.8.3,
printed pp.849–850; consumer Lemma 12.8.10(5), p.854.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.RankTwoHypothesis
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L M : Subgroup G}
variable (h : RankTwoHypothesis K T L M)
include h

/-- The original S₃ quotient realizes every automorphism of the actual seed. -/
theorem full_LT_action :
    Function.Surjective (setupSeedAction (L ⊔ (T : Subgroup G)) (rankTwoSeed T M)
      ((sup_le h.L_le h.sylow_le).trans M_normalizes_seed)) := by
  let V := rankTwoSeed T M
  let := rankTwoSeed_elementary h
  let : Nontrivial V := (Finite.one_lt_card_iff_nontrivial).mp (by
    change 1 < Nat.card (rankTwoSeed T M)
    rw [rankTwoSeed_card h]; decide)
  let : IsKleinFour V := ⟨rankTwoSeed_card h, IsElementaryAbelian.exponent_eq_prime⟩
  let f := setupSeedAction (L ⊔ (T : Subgroup G)) V
    ((sup_le h.L_le h.sylow_le).trans M_normalizes_seed)
  have hc : Nat.card f.range = 6 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    rw [show f.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) from h.literal_action_kernel]
    obtain ⟨e⟩ := h.quotient_model
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  exact MonoidHom.range_eq_top.mp (f.range.eq_top_of_card_eq (hc.trans
    (IsKleinFour.card_mulAut V).symm))

/-- The full automorphism group is identified through the original S₃ quotient. -/
theorem seedAut_model : Nonempty (MulAut (rankTwoSeed T M) ≃* Equiv.Perm (Fin 3)) := by
  let f := setupSeedAction (L ⊔ (T : Subgroup G)) (rankTwoSeed T M)
    ((sup_le h.L_le h.sylow_le).trans M_normalizes_seed)
  obtain ⟨e⟩ := h.quotient_model
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f h.full_LT_action).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h.literal_action_kernel).trans e)⟩

/-- L induces precisely the two-residual of the actual automorphism group. -/
theorem L_action_range :
    (setupSeedAction L (rankTwoSeed T M) h.L_normalizes_seed).range =
      pResidual 2 (MulAut (rankTwoSeed T M)) := by
  let J := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf J
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer
    (show L ≤ J from le_sup_left)).mpr
      (sup_le L.le_normalizer h.sylow_normalizes_L)
  have hp : IsPPerfect 2 N := ((pResidual_eq_top_iff 2 L).mp h.L_residual).of_surjective
    (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).symm.surjective
  have hres : pResidual 2 J = N := pResidual_eq_of_isPPerfect_sup N
    ((T : Subgroup G).subgroupOf J) hp T.isPGroup'.comap_subtype (by
      rw [← subgroupOf_sup (show L ≤ J from le_sup_left)
        (show (T : Subgroup G) ≤ J from le_sup_right)]
      exact subgroupOf_self J)
  let f := setupSeedAction J (rankTwoSeed T M)
    ((sup_le h.L_le h.sylow_le).trans M_normalizes_seed)
  rw [← map_pResidual_of_surjective 2 f h.full_LT_action, hres]
  ext a
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨⟨l, (le_sup_left : L ≤ J) l.property⟩, l.property, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

/-- The L-image has order three; its full S₃ extension is induced by LT. -/
theorem L_action_card : Nat.card (setupSeedAction L (rankTwoSeed T M)
    h.L_normalizes_seed).range = 3 := by
  rw [h.L_action_range]
  obtain ⟨e⟩ := h.seedAut_model
  rw [← card_map_of_injective (K := pResidual 2 (MulAut (rankTwoSeed T M)))
    (f := e.toMonoidHom) e.injective, map_pResidual,
    Equiv.Perm.twoResidual_eq_alternating, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The literal L-centralizer is its intrinsic two-core, embedded in G. -/
theorem centralizer_L :
    L ⊓ Subgroup.centralizer (rankTwoSeed T M : Set G) = L.pCoreIn 2 := by
  have hnorm : (L ⊔ (T : Subgroup G)) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer h.sylow_normalizes_L
  apply le_antisymm
  · have hh : L ⊓ Subgroup.centralizer (rankTwoSeed T M : Set G) ≤
        L ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      rw [← h.centralizer]
      exact le_inf inf_le_left (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
    exact hh.trans (inf_pCoreIn_le_of_le 2 le_sup_left)
  · exact le_inf (pCoreIn_le 2 L)
      ((pCoreIn_mono_of_normalizes le_sup_left hnorm).trans
        (h.centralizer.symm ▸ inf_le_right))

private theorem L_nontrivial : L ≠ ⊥ := by
  intro hb
  have hc := h.L_action_card
  have hs : Subsingleton L := by rw [hb]; infer_instance
  have : Subsingleton (setupSeedAction L (rankTwoSeed T M) h.L_normalizes_seed).range :=
    Function.Surjective.subsingleton (MonoidHom.rangeRestrict_surjective _)
  have ho : Nat.card (setupSeedAction L (rankTwoSeed T M) h.L_normalizes_seed).range = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  omega


private theorem core_L_nontrivial : pCore 2 L ≠ ⊥ := by
  let : (L.subgroupOf M).Normal := h.L_normal
  have hc := normal_core_selfCentralizing
    (h.simpleQTKE.evenCharacteristic T M h.maximal h.sylow_le) (L.subgroupOf M)
  have hcL := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe h.L_le)).mp hc
  intro hb
  apply h.L_nontrivial
  apply le_bot_iff.mp
  intro x hx
  change x = 1
  have hm : (⟨x, hx⟩ : L) ∈ pCore 2 L := hcL (by
    intro y hy
    have hy1 : y = 1 := by
      have hym : y ∈ pCore 2 L := hy
      rw [hb] at hym
      exact mem_bot.mp hym
    simp [hy1])
  simpa only [hb, mem_bot, Subtype.ext_iff, Subgroup.coe_one] using hm

/-- The originally specified M agrees with the normalizer in Notation 12.8.2. -/
theorem M_eq_normalizer : M = normalizer (L : Set G) := by
  have hMN : M ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal
  apply le_antisymm hMN
  apply (normalizer_le_normalizer_characteristic_image L (pCore 2 L)).trans
  apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
  · intro N hN hJN
    exact Set.mem_singleton_iff.mp (h.unique ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN, hJN⟩)
  · exact pCore_isPGroup.map L.subtype
  · exact fun hb => h.core_L_nontrivial
      (((pCore 2 L).map_eq_bot_iff_of_injective L.subtype_injective).mp hb)
  · exact (sup_le h.L_le h.sylow_le).trans (hMN.trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))

/-- Transitivity of L on the three nonidentity vectors, with literal conjugation. -/
theorem nonidentity_transitive (x y : G)
    (hx : x ∈ rankTwoSeed T M) (hy : y ∈ rankTwoSeed T M)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ l ∈ L, l * x * l⁻¹ = y := by
  let := rankTwoSeed_elementary h
  let f := setupSeedAction L (rankTwoSeed T M) h.L_normalizes_seed
  have horbit := MulAction.nonidentity_mem_orbit_of_four_automorphism_subgroup
    (rankTwoSeed_card h) f.range (by rw [h.L_action_card]; decide)
    ⟨x, hx⟩ (fun he => hx1 (congrArg Subtype.val he))
    ⟨y, hy⟩ (fun he => hy1 (congrArg Subtype.val he))
  obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp horbit
  obtain ⟨l, hl⟩ := a.property
  refine ⟨l, l.property, ?_⟩
  have he : (a : MulAut (rankTwoSeed T M)) ⟨x, hx⟩ = ⟨y, hy⟩ := ha
  rw [← hl] at he
  exact congrArg Subtype.val he

/-- Every invariant flag has the original central omega subgroup as its point. -/
theorem sylowOmega_eq_point (F : InvariantFlag T (rankTwoSeed T M) 2) :
    sylowOmega T = F.Vi 1 := by
  let := rankTwoSeed_elementary h
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hPT := (F.le_seed 1).trans h.seed_le_sylow
  have hPC : F.Vi 1 ≤ Subgroup.centralizer (T : Set G) :=
    le_centralizer_iff.mp ((F.invariant 1).trans
      (normalizer_le_centralizer_of_card_two _ hc))
  have hPZ : F.Vi 1 ≤ sylowOmega T := by
    intro x hx
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl x
    · exact ⟨⟨x, hPT hx⟩, mem_center_iff.mpr (fun y =>
        Subtype.ext (mem_centralizer_iff.mp (hPC hx) y y.property)), rfl⟩
    · exact elemPow_eq_one_of_isElementaryAbelian x (F.le_seed 1 hx)
  have hZV : sylowOmega T ≤ rankTwoSeed T M := le_conjugateSpanBy _ _
  have hd : Nat.card (sylowOmega T) ∣ 2 ^ 2 := by
    simpa only [rankTwoSeed_card h, show (2 : ℕ) ^ 2 = 4 from rfl] using card_dvd_of_le hZV
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hge := card_le_of_le hPZ
  rw [hc, he] at hge
  interval_cases i
  · norm_num at hge
  · exact (eq_of_le_of_card_ge hPZ (by rw [he, hc]; decide)).symm
  · have hZeq : sylowOmega T = rankTwoSeed T M :=
      eq_of_le_of_card_ge hZV (by rw [he, rankTwoSeed_card h]; decide)
    exact (h.escape (hZeq ▸ h.seed_centralizer_le)).elim

/-- The point normalizer escapes M by the original centralizer-escape assumption. -/
theorem flag_escape (F : InvariantFlag T (rankTwoSeed T M) 2) : ¬ F.H ≤ M := by
  intro hHM
  apply h.escape
  rw [h.sylowOmega_eq_point F]
  exact (Subgroup.centralizer_le_normalizer _).trans hHM

/-- Equal-order subgroups of V are conjugate by L using right conjugation. -/
theorem subgroup_transitive (A B : Subgroup G)
    (hA : A ≤ rankTwoSeed T M) (hB : B ≤ rankTwoSeed T M)
    (hc : Nat.card A = Nat.card B) : ∃ l ∈ L, conjugate A l = B := by
  have hconj1 (D : Subgroup G) : conjugate D 1 = D := by
    have he : (MulAut.conj (1 : G)⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    unfold conjugate
    rw [he, Subgroup.map_id]
  have hd : Nat.card A ∣ 2 ^ 2 := by
    simpa only [rankTwoSeed_card h, show (2 : ℕ) ^ 2 = 4 from rfl] using card_dvd_of_le hA
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases i
  · have ha : A = ⊥ := card_eq_one.mp he
    have hb : B = ⊥ := card_eq_one.mp (hc.symm.trans he)
    exact ⟨1, L.one_mem, by rw [hconj1, ha, hb]⟩
  · have ha : Nat.card A = 2 := he
    have hb : Nat.card B = 2 := hc.symm.trans ha
    obtain ⟨x, hx⟩ := ne_bot_iff_exists_ne_one.mp (show A ≠ ⊥ by
      intro hh; simp [hh] at ha)
    obtain ⟨y, hy⟩ := ne_bot_iff_exists_ne_one.mp (show B ≠ ⊥ by
      intro hh; simp [hh] at hb)
    have hax : zpowers (x : G) = A := by
      have hh := congrArg (map A.subtype) (zpowers_eq_top_of_prime_card ha hx)
      simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype, Subgroup.subtype_apply] using hh
    have hby : zpowers (y : G) = B := by
      have hh := congrArg (map B.subtype) (zpowers_eq_top_of_prime_card hb hy)
      simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype, Subgroup.subtype_apply] using hh
    obtain ⟨l, hl, heq⟩ := h.nonidentity_transitive x y (hA x.property) (hB y.property)
      (fun hh => hx (Subtype.ext hh)) (fun hh => hy (Subtype.ext hh))
    refine ⟨l⁻¹, L.inv_mem hl, ?_⟩
    rw [conjugate, ← hax, MonoidHom.map_zpowers]
    rw [inv_inv]
    change zpowers (l * (x : G) * l⁻¹) = B
    rw [heq, hby]
  · have ha : A = rankTwoSeed T M := eq_of_le_of_card_ge hA (by
      rw [he, rankTwoSeed_card h]; decide)
    have hb : B = rankTwoSeed T M := eq_of_le_of_card_ge hB (by
      rw [← hc, he, rankTwoSeed_card h]; decide)
    exact ⟨1, L.one_mem, by rw [hconj1, ha, hb]⟩

/-- The point stabilizer in L is a two-group, hence its two-residual is trivial. -/
theorem Li_one_eq_bot (F : InvariantFlag T (rankTwoSeed T M) 2) : F.Li L 1 = ⊥ := by
  let N := L ⊓ F.Gi 1
  let f := setupSeedAction N (rankTwoSeed T M) (inf_le_left.trans h.L_normalizes_seed)
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp (show F.Vi 1 ≠ ⊥ by
    intro hh; simp [hh] at hc)
  let v : rankTwoSeed T M := ⟨z, F.le_seed 1 z.property⟩
  have hv : v ≠ 1 := fun he => hz (Subtype.ext (congrArg (fun w : rankTwoSeed T M => (w : G)) he))
  have hfix : ∀ a ∈ f.range, a v = v := by
    rintro a ⟨x, rfl⟩
    apply Subtype.ext
    have hxc := normalizer_le_centralizer_of_card_two (F.Vi 1) hc x.property.2
    change (x : G) * (z : G) * (x : G)⁻¹ = z
    rw [← hxc z z.property, mul_inv_cancel_right]
  have hbound := card_mulAut_subgroup_le_two_of_fixed_point (rankTwoSeed_card h) v hv f.range hfix
  have hle : f.range ≤ (setupSeedAction L (rankTwoSeed T M) h.L_normalizes_seed).range := by
    rintro a ⟨x, rfl⟩
    exact ⟨⟨x, x.property.1⟩, rfl⟩
  have hd : Nat.card f.range ∣ 3 := by
    simpa only [h.L_action_card] using card_dvd_of_le hle
  have hfbot : f.range = ⊥ := card_eq_one.mp
    ((Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_right (by omega))
  have hNcore : N ≤ L.pCoreIn 2 := by
    rw [← h.centralizer_L]
    intro x hx
    refine ⟨hx.1, ?_⟩
    have hfx : f ⟨x, hx⟩ = 1 := by
      have hm := show f ⟨x, hx⟩ ∈ f.range from ⟨⟨x, hx⟩, rfl⟩
      simpa only [hfbot, mem_bot] using hm
    exact (setupSeedAction_ker N (rankTwoSeed T M) _).le hfx
  have hp : IsPGroup 2 N := (isPGroup_pCoreIn 2 L).to_le hNcore
  have hr : pResidual 2 N = ⊥ := by
    apply le_bot_iff.mp
    exact sInf_le ⟨inferInstance, hp.of_equiv QuotientGroup.quotientBot.symm⟩
  change (pResidual 2 N).map N.subtype = ⊥
  rw [hr, Subgroup.map_bot]

/-- The full seed action of M extends the already surjective LT-action. -/
theorem full_M_action : Function.Surjective
    (setupSeedAction M (rankTwoSeed T M) M_normalizes_seed) := by
  intro a
  obtain ⟨x, hx⟩ := h.full_LT_action a
  exact ⟨⟨x, (sup_le h.L_le h.sylow_le) x.property⟩, hx⟩

/-- The relative normalizer M_V induces the full seed automorphism group. -/
theorem full_seedNormalizer_action : Function.Surjective
    (setupSeedAction (seedNormalizer M (rankTwoSeed T M)) (rankTwoSeed T M) inf_le_right) := by
  intro a
  obtain ⟨x, hx⟩ := h.full_M_action a
  exact ⟨⟨x, x.property, M_normalizes_seed x.property⟩, hx⟩

omit h in
instance seedNormalizerCentralizer_normal :
    ((Subgroup.centralizer (rankTwoSeed T M : Set G)).subgroupOf
      (seedNormalizer M (rankTwoSeed T M))).Normal := by
  rw [← setupSeedAction_ker (seedNormalizer M (rankTwoSeed T M))
    (rankTwoSeed T M) (show seedNormalizer M (rankTwoSeed T M) ≤
      normalizer (rankTwoSeed T M : Set G) from inf_le_right)]
  infer_instance

/-- The full action of M_V on V, factored through its literal centralizer. -/
noncomputable def seedNormalizerQuotientEquiv :
    (seedNormalizer M (rankTwoSeed T M) ⧸
      (Subgroup.centralizer (rankTwoSeed T M : Set G)).subgroupOf (seedNormalizer M (rankTwoSeed T M))) ≃*
      MulAut (rankTwoSeed T M) :=
  (QuotientGroup.quotientMulEquivOfEq
    (setupSeedAction_ker (seedNormalizer M (rankTwoSeed T M)) (rankTwoSeed T M) inf_le_right).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ h.full_seedNormalizer_action)

/-- The quotient equivalence retains the original conjugation map. -/
theorem seedNormalizerQuotientEquiv_mk
    (x : seedNormalizer M (rankTwoSeed T M)) (v : rankTwoSeed T M) :
    (h.seedNormalizerQuotientEquiv (QuotientGroup.mk' _ x) v : G) =
      (x : G) * (v : G) * (x : G)⁻¹ := rfl

/-- The existing flag action is the same literal surjective LT-action. -/
theorem binarySeedAction_surjective (F : InvariantFlag T (rankTwoSeed T M) 2) :
    Function.Surjective (F.binarySeedAction L h.L_normalizes_seed) := by
  intro a
  obtain ⟨x, hx⟩ := h.full_LT_action a
  exact ⟨x, hx⟩

/-- All setup premises for the existing local-kernel source application come
from the original rank-two hypothesis. The flag and original conjugator remain
arbitrary, and the nonabelian and center-containment antecedents are retained. -/
theorem localKernel_center_product
    (F : InvariantFlag T (rankTwoSeed T M) 2) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate F.ZU g ≤ F.U →
      (F.ZU = centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
        Disjoint (centerIn (F.I₂ L)) (F.Vi 1) ∧
        ∃ e : centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
          ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
      ⁅L, centerIn (F.I₂ L)⁆ = ⊥ := by
  let := rankTwoSeed_elementary h
  exact F.localKernel_source_center_product h.simpleQTKE L M
    ⟨by decide, by decide⟩ h.seed_le_sylow h.L_normalizes_seed
    h.sylow_normalizes_L h.L_residual (fun hn => by omega) h.M_eq_normalizer
    h.unique h.seed_centralizer_le h.centralizer_L (h.flag_escape F)
    (h.binarySeedAction_surjective F) (fun hn => by omega) h.centralizer hne g hgP hgH

/-- The actual point normalizer is a member of the source local family. -/
theorem pointNormalizer_mem_Hz (F : InvariantFlag T (rankTwoSeed T M) 2) :
    F.H ∈ F.Hz L M := F.H_mem_Hz (by decide) L M (h.flag_escape F)

/-- The source family of spans is abelian exactly when the point-normalizer span is. -/
theorem all_local_spans_abelian_iff (F : InvariantFlag T (rankTwoSeed T M) 2) :
    (∀ J ∈ F.Hz L M, IsMulCommutative (F.UH J)) ↔ IsMulCommutative F.U :=
  F.all_local_spans_abelian_iff (by decide) L M (h.flag_escape F)

/-- The actual L-transitivity supplies the intersecting-conjugates criterion. -/
theorem abelian_U_iff_intersections_commute (F : InvariantFlag T (rankTwoSeed T M) 2) :
    IsMulCommutative F.U ↔ ∀ g : G,
      rankTwoSeed T M ⊓ conjugate (rankTwoSeed T M) g ≠ ⊥ →
        ⁅rankTwoSeed T M, conjugate (rankTwoSeed T M) g⁆ = ⊥ := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp (show F.Vi 1 ≠ ⊥ by
    intro hh; simp [hh] at hc)
  have hgen : F.Vi 1 = zpowers (z : G) := by
    have hh := congrArg (map (F.Vi 1).subtype) (zpowers_eq_top_of_prime_card hc hz)
    apply Eq.symm
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype, Subgroup.subtype_apply] using hh
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  apply F.abelian_U_iff_intersections_commute (by decide) z hgen hz1
  intro x hx hx1
  obtain ⟨l, hl, he⟩ := h.nonidentity_transitive z x (F.le_seed 1 z.property) hx hz1 hx1
  exact ⟨l, h.L_normalizes_seed hl, he⟩

/-- The derived normalization supplies the existing parabolic seed geometry. -/
theorem parabolic_seed_geometry (F : InvariantFlag T (rankTwoSeed T M) 2)
    (g : G) (hg : g ∈ F.P L) :
    rankTwoSeed T M ≤ F.E g ∧
      conjugate F.ZU g ≤ Subgroup.centralizer (rankTwoSeed T M : Set G) := by
  let := rankTwoSeed_elementary h
  exact F.parabolic_seed_geometry L h.L_normalizes_seed g hg

end CFSG.Quasithin.Chapter12.Section08.RankTwoHypothesis
