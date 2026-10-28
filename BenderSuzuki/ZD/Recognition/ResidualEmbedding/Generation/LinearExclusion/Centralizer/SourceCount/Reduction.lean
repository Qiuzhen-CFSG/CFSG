module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceCount.Foundations
public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.ConjugacyClassSize

/-!
# Inversion and normal-closure assembly for the source count

An order-four coset witness forces the elementary abelian U to have order two:
all its nonidentity elements invert the same element x, and the product of two
distinct such elements would also centralize x. The actual PSL₂ embedding then
shows J = U. Finally the q² conjugate involutions and identity occupy more than
half of the normal subgroup R₁, so their literal normal closure inside M is R₁.

The normalizer-growth and census premises are explicit. No supplement M = VD,
normal complement, or desired centralizer or normal-closure order is assumed
by the assembly theorem.

Source: GLS IV, Chapter 2, Lemma 15.6, refs/KGroup/GLS4/Chapter2.tex,
lines 2718–2745. The final identification also records the subgroup equality
needed when applying the subsequent Lemma 15.7 to the literal normal closure.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount
open Subgroup Theory.GroupTheory
universe u

private theorem card_two_of_inverting
    {H : Type*} [Group H] (U : Subgroup H) (hne : U ≠ ⊥)
    (hsq : ∀ u ∈ U, u ^ 2 = 1) (x : H) (hx : x ^ 2 ≠ 1)
    (hux : ∀ u ∈ U, u ≠ 1 → (u * x) ^ 2 = 1) : Nat.card U = 2 := by
  have hinv (u : H) (hu : u ∈ U) (hu1 : u ≠ 1) : MulAut.conj u x = x⁻¹ := by
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq u hu)
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [MulAut.conj_apply, hui, pow_two, mul_assoc] using hux u hu hu1
  obtain ⟨u, hu⟩ := ne_bot_iff_exists_ne_one.mp hne
  apply (Nat.card_eq_two_iff' (1 : U)).mpr
  refine ⟨u, hu, ?_⟩
  intro v hv
  by_contra hne
  have hv1 : (v : H) ≠ 1 := fun he => hv (Subtype.ext he)
  have hu1 : (u : H) ≠ 1 := fun he => hu (Subtype.ext he)
  have hvu : (u : H) * v ≠ 1 := by
    intro he
    apply hne
    apply Subtype.ext
    have hui : (u : H)⁻¹ = u :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq u u.property)
    exact (eq_inv_of_mul_eq_one_right he).trans hui
  have hconj : MulAut.conj ((u : H) * v) x = x := by
    calc
      _ = MulAut.conj (u : H) (MulAut.conj (v : H) x) := by
        simp only [MulAut.conj_apply, mul_inv_rev, mul_assoc]
      _ = MulAut.conj (u : H) x⁻¹ := by rw [hinv v v.property hv1]
      _ = (MulAut.conj (u : H) x)⁻¹ := map_inv _ _
      _ = x := by rw [hinv u u.property hu1, inv_inv]
  have he : x = x⁻¹ := hconj.symm.trans (hinv _ (U.mul_mem u.property v.property) hvu)
  exact hx (by simpa only [pow_two] using eq_inv_iff_mul_eq_one.mp he)

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "J" => centralizer (residualGenerated M z t : Set G)
local notation "U" => twoCore M z t
local notation "A" => closure (Z ∩ (M : Set G))
local notation "R" => sourceNormalizer Z M z t

/-- The source order-four coset witness forces U to have order two.
Two distinct nonidentity inverters would have a nonidentity product which
both fixes and inverts x, contradicting x² ≠ 1. -/
public theorem twoCore_card_of_census (hs : CentralizerLocalTwoData d)
    (hc : ∃ x ∈ R, x ^ 2 ≠ 1 ∧ ∀ u ∈ U, u ≠ 1 → (u * x) ^ 2 = 1) :
    Nat.card U = 2 := by
  obtain ⟨x, _, hx, hux⟩ := hc
  apply card_two_of_inverting U (twoCore_ne_bot d hs) ?_ x hx hux
  intro u hu
  exact congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      hs.twoCore_elementary.exponent_dvd_p ⟨u, hu⟩)

/-- A normal two-core of order two is centralized by J. The genuine
embedding in PSL₂ puts J in an involution centralizer, hence makes J a
two-group. Since U is Sylow in J, the literal subgroups J and U coincide. -/
public theorem centralizer_eq_twoCore_of_card_two (hm : CentralizerLocalModelData d)
    (hs : CentralizerLocalTwoData d) (hU : Nat.card U = 2) : J = U := by
  have hp : Nat.card (pCore 2 J) = 2 := by
    rw [twoCore, card_map_of_injective (J).subtype_injective] at hU
    exact hU
  obtain ⟨u, hu1, _⟩ := (Nat.card_eq_two_iff' (1 : pCore 2 J)).mp hp
  let f := d.model.toMonoidHom.comp hm.embedding
  have hf : Function.Injective f := d.model.injective.comp hm.embedding_injective
  have hu2 : (u : J) ^ 2 = 1 := congrArg Subtype.val
    (hp ▸ pow_card_eq_one' (x := u))
  have hfu : orderOf (f (u : J)) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hu2, map_one]
    · intro he
      exact hu1 (Subtype.ext (hf (he.trans (map_one f).symm)))
  obtain ⟨_, _, _, _, _, hC⟩ := Theory.PSL2.involution_root_geometry (f (u : J)) hfu
  have hmem (j : J) : f j ∈ centralizer ({f (u : J)} : Set (MatrixGroups.PSL2BinaryMatrixGroup n)) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← map_mul, ← map_mul]
    apply congrArg f
    exact (mem_centralizer_iff.mp
      (normalizer_le_centralizer_of_card_two (pCore 2 J) hp
        (show j ∈ normalizer (pCore 2 J : Set J) from
          le_normalizer_of_normal (mem_top j))) u u.property).symm
  have hJ : IsPGroup 2 J := hC.of_injective (f.codRestrict _ hmem)
    (fun a b he => hf (congrArg Subtype.val he))
  obtain ⟨S, hS⟩ := hs.twoCore_sylow
  have htop : pCore 2 J = ⊤ := by
    rw [← hS]
    exact (S.is_maximal' (hJ.to_subgroup ⊤) le_top).symm
  change J = (pCore 2 J).map (J).subtype
  rw [htop, ← MonoidHom.range_eq_map]
  exact (J).range_subtype.symm

private theorem centralizer_singleton_eq_normalizer_of_card_two
    {H : Type*} [Group H] (W : Subgroup H) (hW : Nat.card W = 2)
    {u : H} (hu : u ∈ W) (hu1 : u ≠ 1) :
    centralizer ({u} : Set H) = normalizer (W : Set H) := by
  obtain ⟨v, _, hv⟩ := (Nat.card_eq_two_iff' (1 : W)).mp hW
  have hchoices (w : H) (hw : w ∈ W) : w = 1 ∨ w = u := by
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (congrArg Subtype.val
        ((hv ⟨w, hw⟩ (fun he => hw1 (congrArg Subtype.val he))).trans
          (hv ⟨u, hu⟩ (fun he => hu1 (congrArg Subtype.val he))).symm))
  apply le_antisymm
  · apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro g hg w hw
    rcases hchoices w hw with rfl | rfl
    · simp
    · exact (mem_centralizer_singleton_iff.mp hg).symm
  · intro g hg
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (normalizer_le_centralizer_of_card_two W hW hg) u hu).symm

/-- Once U has order two, its nonidentity element has exactly q²
conjugates under M. This needs no supplement M = VD. -/
public theorem twoCore_involution_class_card (hs : CentralizerLocalTwoData d)
    (hU : Nat.card U = 2) {u : M} (hu : (u : G) ∈ U) (hu1 : u ≠ 1) :
    Nat.card (ConjClasses.mk u).carrier = (2 ^ n) ^ 2 := by
  have hUM : U ≤ M := (twoCore_le_pointCore d hs).trans (map_subtype_le _)
  have hcard : Nat.card ((U).subgroupOf M) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUM).toEquiv).trans hU
  rw [ConjClasses.nat_card_carrier_eq_index_centralizer,
    centralizer_singleton_eq_normalizer_of_card_two ((U).subgroupOf M) hcard hu hu1,
    ← subgroupOf_normalizer_eq hUM]
  change (normalizer (U : Set G)).relIndex M = _
  change (normalizer ((pCore 2 J).map (J).subtype : Set G)).relIndex M = _
  rw [d.centralizer_twoCore_normalizer_eq hs.twoCore_ne_bot, ← inf_relIndex_left]
  exact d.point_normalizer_index

private theorem class_card_add_one_le_normalClosure
    {H : Type*} [Group H] [Finite H] (W : Subgroup H)
    {u : H} (hu : u ∈ W) (hu1 : u ≠ 1) :
    Nat.card (ConjClasses.mk u).carrier + 1 ≤ Nat.card (normalClosure (W : Set H)) := by
  let N := normalClosure (W : Set H)
  have hc (x : H) (hx : x ∈ (ConjClasses.mk u).carrier) : x ∈ N ∧ x ≠ 1 := by
    have hi : IsConj u x :=
      (ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp hx)).symm
    obtain ⟨g, rfl⟩ := isConj_iff.mp hi
    refine ⟨(inferInstance : N.Normal).conj_mem u (subset_normalClosure hu) g, ?_⟩
    intro he
    exact hu1 ((MulAut.conj g).injective (he.trans (map_one _).symm))
  let f : (ConjClasses.mk u).carrier ⊕ Unit → N :=
    Sum.elim (fun x => ⟨x, (hc x x.property).1⟩) (fun _ => 1)
  have hf : Function.Injective f := by
    intro x y he
    have he' := congrArg Subtype.val he
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext he')
      | inr y => exact ((hc x x.property).2 he').elim
    | inr x =>
      cases y with
      | inl y => exact ((hc y y.property).2 he'.symm).elim
      | inr y => exact congrArg Sum.inr (Subsingleton.elim _ _)
  simpa only [Nat.card_sum, Nat.card_eq_fintype_card, Fintype.card_unit] using
    Nat.card_le_card_of_injective f hf

/-- Identify the literal normal closure inside M with R₁. It contains
the q² conjugate involutions and identity, so its order exceeds half the
order of R₁; Lagrange therefore forces equality. -/
public theorem normalClosure_twoCore_eq_sourceNormalizer
    (hs : CentralizerLocalTwoData d) (hg : NormalizerData d) (hU : Nat.card U = 2) :
    normalClosure ((U).subgroupOf M : Set M) = (R).subgroupOf M := by
  let : ((R).subgroupOf M).Normal := hg.relative_normal
  have hle : normalClosure ((U).subgroupOf M : Set M) ≤ (R).subgroupOf M :=
    normalClosure_le_normal (fun _ hu => (sup_le_sourceNormalizer d hs) ((show U ≤ A ⊔ U from le_sup_right) hu))
  have hUM : U ≤ M := (twoCore_le_pointCore d hs).trans (map_subtype_le _)
  have hcard : Nat.card ((U).subgroupOf M) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUM).toEquiv).trans hU
  obtain ⟨u, hu1, _⟩ := (Nat.card_eq_two_iff' (1 : (U).subgroupOf M)).mp hcard
  have huM1 : (u : M) ≠ 1 := fun he => hu1 (Subtype.ext he)
  have hlow := class_card_add_one_le_normalClosure ((U).subgroupOf M) u.property huM1
  rw [twoCore_involution_class_card d hs hU u.property huM1] at hlow
  have hRcard : Nat.card ((R).subgroupOf M) = 2 * (2 ^ n) ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe sourceNormalizer_le_point).toEquiv,
      hg.card, hU, mul_comm]
  apply eq_of_le_of_card_ge hle
  have he := Nat.eq_of_dvd_of_lt_two_mul Nat.card_pos.ne' (card_dvd_of_le hle)
    (show Nat.card ((R).subgroupOf M) <
      2 * Nat.card (normalClosure ((U).subgroupOf M : Set M)) by
      rw [hRcard]
      omega)
  exact he.le

/-- Assemble the source cardinalities from the earlier local inputs,
the intermediate normalizer geometry, and the actual order-four coset witness.
The last two premises still require their independent source proofs. -/
public theorem counts_of_normalizer_and_census
    (hm : CentralizerLocalModelData d) (hs : CentralizerLocalTwoData d)
    (hg : NormalizerData d)
    (hc : ∃ x ∈ R, x ^ 2 ≠ 1 ∧ ∀ u ∈ U, u ≠ 1 → (u * x) ^ 2 = 1) :
    Nat.card J = 2 ∧ Nat.card (normalClosure ((J).subgroupOf M : Set M)) =
      2 * (2 ^ n) ^ 2 := by
  have hU := twoCore_card_of_census d hs hc
  have hJ := centralizer_eq_twoCore_of_card_two d hm hs hU
  rw [hJ]
  refine ⟨hU, ?_⟩
  rw [normalClosure_twoCore_eq_sourceNormalizer d hs hg hU,
    Nat.card_congr (subgroupOfEquivOfLe sourceNormalizer_le_point).toEquiv,
    hg.card, hU, mul_comm]


end BenderSuzuki.ZD.LinearExclusion.SourceCount
