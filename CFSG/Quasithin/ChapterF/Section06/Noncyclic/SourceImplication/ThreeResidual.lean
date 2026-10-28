module

public import CFSG.Quasithin.ChapterF.Section06.Elementary
public import Theory.Frattini.PGroup
public import Theory.ElementaryAbelian.PrimePlane
public import Theory.GroupAction.OddInvolutionFrattini
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Preparations for the three-group branch of F.6.16

For a genuine Goldschmidt triple whose two-residual L is a three-group,
the local residuals have order three and generate L. If O₃(G) is noncyclic,
these marked generators identify L/Φ(L) with the elementary plane. Cubic
generation also makes the abelianization elementary, proving Φ(L) = [L,L].
The local Frattini joins are normal in the ambient group. The small Sylow
alternatives retain the actual local cores, and the four-group case supplies
two commuting involutions, each centralizing the opposite local residual.

These are branch preparations: the hypothesis that L is a three-group is
explicit. No assertion of the complete noncyclic source implication is made.
The class-three exclusion and the other residual case belong to its assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.16, printed pp.308–309 (1 March 2004 manuscript).
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Noncyclic
variable {G : Type*} [Group G] [Finite G]


private theorem local_residual_card
    (he : Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)))
    (hL : IsPGroup 3 (pResidual 2 G)) : Nat.card (pResidual 2 G) = 3 := by
  obtain ⟨e⟩ := he
  let q := QuotientGroup.mk' (pCore 2 G)
  let f := q.subgroupMap (pResidual 2 G)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    have hxQ : (x : G) ∈ pCore 2 G := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact Subgroup.disjoint_def.mp
      (hL.disjoint_of_coprime pCore_isPGroup (by decide)) x.property hxQ
  have hc := Nat.card_congr (MulEquiv.ofBijective f
    ⟨hf, q.subgroupMap_surjective _⟩).toEquiv
  rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)] at hc
  exact hc.trans (residual_of_symmetricThree e).2


omit [Finite G] in
theorem threeCore_le_twoResidual : pCore 3 G ≤ pResidual 2 G := by
  intro x hx
  obtain ⟨n, hn⟩ := pCore_isPGroup (p := 3) (G := G) ⟨x, hx⟩
  apply mem_pResidual_of_orderOf_coprime
  apply ((by decide : Nat.Coprime 2 3).pow_right n).of_dvd_right
  simpa only [orderOf_mk] using orderOf_dvd_of_pow_eq_one hn

omit [Finite G] in
theorem residual_nocyclic (hn : ¬ IsCyclic (pCore 3 G)) :
    ¬ IsCyclic (pResidual 2 G) := by
  intro hc
  let : IsCyclic (pResidual 2 G) := hc
  exact hn (isCyclic_of_le threeCore_le_twoResidual)

theorem odd_residual_of_three (hL : IsPGroup 3 (pResidual 2 G)) :
    pResidual 2 G = pPrimeCore 2 G := by
  apply le_antisymm
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    obtain ⟨n, hn⟩ := hL.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  · intro x hx
    exact mem_pResidual_of_orderOf_coprime
      (pPrimeCore_coprime_card.of_dvd_right
        ((pPrimeCore 2 G).orderOf_dvd_natCard hx))

variable {G₁ G₂ : Subgroup G}

theorem local_residual_card_three (h : IsGoldschmidtTriple G₁ G₂)
    (hL : IsPGroup 3 (pResidual 2 G)) :
    Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3 := by
  have hi := map_pResidual_le 2 G₁.subtype
  have hp := hL.of_injective (inclusion hi) (inclusion_injective hi)
  have hp' : IsPGroup 3 (pResidual 2 G₁) :=
    hp.of_equiv (equivMapOfInjective _ G₁.subtype G₁.subtype_injective).symm
  rw [card_map_of_injective G₁.subtype_injective]
  exact local_residual_card h.quotient_left hp'

omit [Finite G] in
theorem primeToThreeCore_eq_bot_of_quotient
    {Ghat : Type*} [Group Ghat] [Finite Ghat]
    (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat)) : pPrimeCore 3 G = ⊥ := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [pPrimeCore_map_iso, pPrimeCore_quotient_pPrimeCore_eq_bot, Subgroup.map_bot]

theorem cores_eq_bot_of_intersection_card_two (h : IsGoldschmidtTriple G₁ G₂)
    (hc : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 2) :
    (pCore 2 G₁).map G₁.subtype = ⊥ := by
  have hm := (((pCore 2 G₁).map G₁.subtype).subgroupOf (G₁ ⊓ G₂)).index_mul_card
  rw [show (((pCore 2 G₁).map G₁.subtype).subgroupOf (G₁ ⊓ G₂)).index = 2 from
    h.left_core_index, hc] at hm
  apply card_eq_one.mp
  rw [← Nat.card_congr (subgroupOfEquivOfLe h.local_twoCore_le_intersection).toEquiv]
  omega

-- The two specified cubic subgroups give the actual Frattini plane.
theorem frattini_plane_of_cubic_generators
    (hG : IsPGroup 3 G) (hn : ¬ IsCyclic G)
    (A B : Subgroup G) (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hgen : A ⊔ B = ⊤) :
    Nat.card (G ⧸ frattini G) = 9 ∧
      Nonempty ((G ⧸ frattini G) ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  let : Fact (IsPGroup 3 G) := ⟨hG⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsElementaryAbelian 3 (G ⧸ frattini G) := isElementaryAbelian_quotient_frattini
  let q := QuotientGroup.mk' (frattini G)
  let a := q.comp A.subtype
  let b := q.comp B.subtype
  let f := MonoidHom.noncommCoprod a b (fun _ _ => Commute.all _ _)
  have hs : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.noncommCoprod_range]
    dsimp only [a, b]
    rw [MonoidHom.range_comp, MonoidHom.range_comp, range_subtype, range_subtype]
    rw [← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hd := card_dvd_of_surjective f hs
  rw [Nat.card_prod, hA, hB] at hd
  obtain ⟨n, hnle, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp hd
  have hc : Nat.card (G ⧸ frattini G) = 9 := by
    interval_cases n
    · have : Subsingleton (G ⧸ frattini G) := Finite.card_le_one_iff_subsingleton.mp
        (by omega)
      exact (OddInvolutionFrattini.noncyclic_frattini_quotient hn inferInstance).elim
    · exact (OddInvolutionFrattini.noncyclic_frattini_quotient hn
        (isCyclic_of_prime_card (by simpa using hcard))).elim
    · exact hcard
  exact ⟨hc, IsElementaryAbelian.nonempty_mulEquiv_plane_of_card hc⟩


/-- Multiplication of the two specified cubic subgroups gives coordinates on
the Frattini quotient, retaining both inclusions. -/
theorem exists_marked_frattini_equiv
    (hG : IsPGroup 3 G) (hn : ¬ IsCyclic G)
    (A B : Subgroup G) (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hgen : A ⊔ B = ⊤) :
    ∃ e : (A × B) ≃* (G ⧸ frattini G), ∀ (a : A) (b : B),
      e (a, b) = QuotientGroup.mk' (frattini G) (a : G) *
        QuotientGroup.mk' (frattini G) (b : G) := by
  let : Fact (IsPGroup 3 G) := ⟨hG⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsElementaryAbelian 3 (G ⧸ frattini G) := isElementaryAbelian_quotient_frattini
  let q := QuotientGroup.mk' (frattini G)
  let a := q.comp A.subtype
  let b := q.comp B.subtype
  let f := MonoidHom.noncommCoprod a b (fun _ _ => Commute.all _ _)
  have hs : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.noncommCoprod_range]
    dsimp only [a, b]
    rw [MonoidHom.range_comp, MonoidHom.range_comp, range_subtype, range_subtype,
      ← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hc : Nat.card (A × B) = Nat.card (G ⧸ frattini G) := by
    rw [Nat.card_prod, hA, hB, (frattini_plane_of_cubic_generators hG hn A B hA hB hgen).1]
  exact ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hs, hc⟩),
    fun _ _ => rfl⟩

omit [Finite G] in
theorem residual_eq_threeCore (hL : IsPGroup 3 (pResidual 2 G)) :
    pResidual 2 G = pCore 3 G :=
  le_antisymm (le_sSup ⟨inferInstance, hL⟩) threeCore_le_twoResidual

theorem residual_frattini_plane (h : IsGoldschmidtTriple G₁ G₂)
    (hL : IsPGroup 3 (pResidual 2 G)) (hn : ¬ IsCyclic (pCore 3 G)) :
    Nat.card ((pResidual 2 G) ⧸ frattini (pResidual 2 G)) = 9 ∧
      Nonempty (((pResidual 2 G) ⧸ frattini (pResidual 2 G)) ≃*
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) := by
  let L := pResidual 2 G
  let A := (pResidual 2 G₁).map G₁.subtype
  let B := (pResidual 2 G₂).map G₂.subtype
  have ha : A ≤ L := map_pResidual_le 2 G₁.subtype
  have hb : B ≤ L := map_pResidual_le 2 G₂.subtype
  apply frattini_plane_of_cubic_generators hL (residual_nocyclic hn)
    (A.subgroupOf L) (B.subgroupOf L)
  · rw [Nat.card_congr (subgroupOfEquivOfLe ha).toEquiv]
    exact local_residual_card_three h hL
  · rw [Nat.card_congr (subgroupOfEquivOfLe hb).toEquiv]
    exact local_residual_card_three h.symm hL
  · apply map_injective L.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le ha, map_subgroupOf_eq_of_le hb,
      ← MonoidHom.range_eq_map, range_subtype]
    exact h.twoResidual_eq_sup.symm

-- Cubic generation makes the abelianization elementary, so Φ equals the derived group.
theorem frattini_eq_derived_of_cubic_generators
    (hG : IsPGroup 3 G) (A B : Subgroup G)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hgen : A ⊔ B = ⊤) :
    frattini G = _root_.commutator G := by
  let : Fact (IsPGroup 3 G) := ⟨hG⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsMulCommutative (G ⧸ _root_.commutator G) :=
    (Normal.quotient_commutative_iff_commutator_le).mpr le_rfl
  let q := QuotientGroup.mk' (_root_.commutator G)
  let a := q.comp A.subtype
  let b := q.comp B.subtype
  let f := MonoidHom.noncommCoprod a b (fun _ _ => Commute.all _ _)
  have hs : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.noncommCoprod_range]
    dsimp only [a, b]
    rw [MonoidHom.range_comp, MonoidHom.range_comp, range_subtype, range_subtype,
      ← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  have hcube (x : G) : x ^ 3 ∈ _root_.commutator G := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (x ^ 3) = 1
    rw [map_pow]
    obtain ⟨⟨xA, xB⟩, he⟩ := hs (q x)
    rw [← he]
    change (a xA * b xB) ^ 3 = 1
    rw [(Commute.all _ _).mul_pow, ← map_pow, ← map_pow,
      (show xA ^ 3 = 1 by simpa only [hA] using pow_card_eq_one' (x := xA)),
      (show xB ^ 3 = 1 by simpa only [hB] using pow_card_eq_one' (x := xB)),
      map_one, map_one, mul_one]
  apply le_antisymm ?_ (commutator_le_frattini_of_isPGroup (p := 3))
  rw [frattini_eq_closure_commutator_union_powers (p := 3)]
  apply (Subgroup.closure_le _).mpr
  rintro x (hx | ⟨y, rfl⟩)
  · exact hx
  · exact hcube y

theorem residual_frattini_eq_derived (h : IsGoldschmidtTriple G₁ G₂)
    (hL : IsPGroup 3 (pResidual 2 G)) :
    frattini (pResidual 2 G) = _root_.commutator (pResidual 2 G) := by
  let L := pResidual 2 G
  let A := (pResidual 2 G₁).map G₁.subtype
  let B := (pResidual 2 G₂).map G₂.subtype
  have ha : A ≤ L := map_pResidual_le 2 G₁.subtype
  have hb : B ≤ L := map_pResidual_le 2 G₂.subtype
  apply frattini_eq_derived_of_cubic_generators hL (A.subgroupOf L) (B.subgroupOf L)
  · rw [Nat.card_congr (subgroupOfEquivOfLe ha).toEquiv]
    exact local_residual_card_three h hL
  · rw [Nat.card_congr (subgroupOfEquivOfLe hb).toEquiv]
    exact local_residual_card_three h.symm hL
  · apply map_injective L.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le ha, map_subgroupOf_eq_of_le hb,
      ← MonoidHom.range_eq_map, range_subtype]
    exact h.twoResidual_eq_sup.symm


-- The source subgroup X_i = L_i Φ(L) is ambient normal.
theorem local_frattini_join_normal (h : IsGoldschmidtTriple G₁ G₂)
    (hL : IsPGroup 3 (pResidual 2 G)) :
    ((pResidual 2 G₁).map G₁.subtype ⊔
      (frattini (pResidual 2 G)).map (pResidual 2 G).subtype).Normal := by
  let L := pResidual 2 G
  let A := (pResidual 2 G₁).map G₁.subtype
  let F := (frattini L).map L.subtype
  let X := A ⊔ F
  have hAL : A ≤ L := map_pResidual_le 2 G₁.subtype
  have hXL : X ≤ L := sup_le hAL (map_subtype_le _)
  have hLL : ⁅L, L⁆ = F := by
    rw [← map_subtype_commutator]
    exact congrArg (fun U : Subgroup L => U.map L.subtype)
      (residual_frattini_eq_derived h hL).symm
  have hLN : L ≤ normalizer (X : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    exact ((commutator_mono le_rfl hXL).trans_eq hLL).trans le_sup_right
  have hTN : G₁ ⊓ G₂ ≤ normalizer (X : Set G) := by
    apply (le_inf h.intersection_normalizes_left_residual
      (show G₁ ⊓ G₂ ≤ normalizer (F : Set G) by rw [normalizer_eq_top]; exact le_top)).trans
    exact normalizer_inf_normalizer_le_normalizer_sup A F
  apply normalizer_eq_top_iff.mp
  apply top_unique
  obtain ⟨T, hT⟩ := h.intersection_sylow
  rw [← pResidual_sup_sylow_eq_top T]
  exact sup_le hLN (hT ▸ hTN)


theorem local_residual_equiv_three (h : IsGoldschmidtTriple G₁ G₂)
    (hL : IsPGroup 3 (pResidual 2 G)) :
    Nonempty ((pResidual 2 G₁).map G₁.subtype ≃* Multiplicative (ZMod 3)) :=
  ⟨mulEquivOfPrimeCardEq (local_residual_card_three h hL) (by simp)⟩

theorem three_residual_sylow_alternatives (h : IsGoldschmidtTriple G₁ G₂)
    {Ghat : Type*} [Group Ghat] [Finite Ghat]
    (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat)) (hL : IsPGroup 3 (pResidual 2 G)) :
    (Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2)) ∧
      (pCore 2 G₁).map G₁.subtype = ⊥ ∧ (pCore 2 G₂).map G₂.subtype = ⊥) ∨
    (Nonempty ((pCore 2 G₁).map G₁.subtype ≃* Multiplicative (ZMod 2)) ∧
      Nonempty ((pCore 2 G₂).map G₂.subtype ≃* Multiplicative (ZMod 2)) ∧
      Nonempty (↥(G₁ ⊓ G₂) ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) := by
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp
    (twoCore_le_primeToThreeCore.trans_eq (primeToThreeCore_eq_bot_of_quotient e))
  rcases h.odd_residual_small_sylow hcore (odd_residual_of_three hL) with htwo | hfour
  · have hc : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 2 := by
      rw [Nat.card_congr htwo.some.toEquiv]
      simp
    exact Or.inl ⟨htwo, cores_eq_bot_of_intersection_card_two h hc,
      cores_eq_bot_of_intersection_card_two h.symm (by simpa only [inf_comm] using hc)⟩
  · exact Or.inr hfour


theorem local_core_centralizes_residual (h : IsGoldschmidtTriple G₁ G₂)
    (hL : IsPGroup 3 (pResidual 2 G)) :
    (pCore 2 G₁).map G₁.subtype ≤
      centralizer ((pResidual 2 G₁).map G₁.subtype : Set G) := by
  let Q := (pCore 2 G₁).map G₁.subtype
  let A := (pResidual 2 G₁).map G₁.subtype
  have hd : Disjoint Q A :=
    (pCore_isPGroup.map G₁.subtype).disjoint_of_coprime
      (IsPGroup.of_card (n := 1) (by simpa only [pow_one] using local_residual_card_three h hL))
      (by decide : Nat.Coprime 2 3)
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  rw [← hd.eq_bot]
  apply le_inf
  · rw [← map_commutator]
    exact map_mono (commutator_le_left _ _)
  · rw [← map_commutator]
    exact map_mono (commutator_le_right _ _)

/-- The two distinct local cores provide actual commuting involutions with
opposite markings. Each fixes the opposite cubic residual pointwise. -/
theorem exists_marked_commuting_involutions (h : IsGoldschmidtTriple G₁ G₂)
    (hcore : pCore 2 G = ⊥) (hL : IsPGroup 3 (pResidual 2 G))
    (hnot : ¬ Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2))) :
    ∃ t₁ t₂ : G,
      t₁ ∈ (pCore 2 G₂).map G₂.subtype ∧ t₁ ∉ (pCore 2 G₁).map G₁.subtype ∧
      t₂ ∈ (pCore 2 G₁).map G₁.subtype ∧ t₂ ∉ (pCore 2 G₂).map G₂.subtype ∧
      orderOf t₁ = 2 ∧ orderOf t₂ = 2 ∧ Commute t₁ t₂ ∧
      t₁ ∈ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) ∧
      t₂ ∈ centralizer ((pResidual 2 G₁).map G₁.subtype : Set G) := by
  obtain ⟨⟨e₁⟩, ⟨e₂⟩, ⟨eT⟩⟩ :=
    (h.odd_residual_small_sylow hcore (odd_residual_of_three hL)).resolve_left hnot
  let Q₁ := (pCore 2 G₁).map G₁.subtype
  let Q₂ := (pCore 2 G₂).map G₂.subtype
  have hc₁ : Nat.card Q₁ = 2 := by rw [Nat.card_congr e₁.toEquiv]; simp
  have hc₂ : Nat.card Q₂ = 2 := by rw [Nat.card_congr e₂.toEquiv]; simp
  obtain ⟨t₂, ht₂⟩ := (ne_bot_iff_exists_ne_one (H := Q₁)).mp
    (by intro hb; simp only [hb] at hc₁; simp_all)
  obtain ⟨t₁, ht₁⟩ := (ne_bot_iff_exists_ne_one (H := Q₂)).mp
    (by intro hb; simp only [hb] at hc₂; simp_all)
  have hi : Q₁ ⊓ Q₂ = ⊥ := h.core_intersection_trivial hcore (odd_residual_of_three hL)
  have hn₁ : (t₁ : G) ∉ Q₁ := by
    intro hm
    apply ht₁
    apply Subtype.ext
    exact mem_bot.mp (hi ▸ (show (t₁ : G) ∈ Q₁ ⊓ Q₂ from ⟨hm, t₁.property⟩))
  have hn₂ : (t₂ : G) ∉ Q₂ := by
    intro hm
    apply ht₂
    apply Subtype.ext
    exact mem_bot.mp (hi ▸ (show (t₂ : G) ∈ Q₁ ⊓ Q₂ from ⟨t₂.property, hm⟩))
  have ho₁ : orderOf (t₁ : G) = 2 := by
    rw [← orderOf_mk]
    exact orderOf_eq_prime (by simpa only [hc₂] using pow_card_eq_one' (x := t₁)) ht₁
  have ho₂ : orderOf (t₂ : G) = 2 := by
    rw [← orderOf_mk]
    exact orderOf_eq_prime (by simpa only [hc₁] using pow_card_eq_one' (x := t₂)) ht₂
  have ht₁T : (t₁ : G) ∈ G₁ ⊓ G₂ := by
    simpa only [inf_comm G₂ G₁] using h.symm.local_twoCore_le_intersection t₁.property
  have ht₂T : (t₂ : G) ∈ G₁ ⊓ G₂ := h.local_twoCore_le_intersection t₂.property
  have hcomm : Commute (t₁ : G) (t₂ : G) := by
    have he : (⟨t₁, ht₁T⟩ : ↥(G₁ ⊓ G₂)) * ⟨t₂, ht₂T⟩ = ⟨t₂, ht₂T⟩ * ⟨t₁, ht₁T⟩ := by
      apply eT.injective
      simp only [map_mul]
      exact mul_comm _ _
    exact congrArg Subtype.val he
  exact ⟨t₁, t₂, t₁.property, hn₁, t₂.property, hn₂, ho₁, ho₂, hcomm,
    local_core_centralizes_residual h.symm hL t₁.property,
    local_core_centralizes_residual h hL t₂.property⟩

end CFSG.Quasithin.ChapterF.Noncyclic
