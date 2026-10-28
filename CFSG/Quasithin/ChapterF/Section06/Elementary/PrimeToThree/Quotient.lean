module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.Core
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Quotient
public import Theory.GroupTheory.CoprimeQuotientNormalizer

/-!
# Quotient amalgams over the prime-to-three core

The kernel on each local group is its intrinsic copy of the ambient two-core.
The first isomorphism theorem therefore gives one compatible isomorphism of
amalgams, with the original quotient maps on representatives. The common
Sylow image has index three in both local images. Maximality then separates
the full-overlap case from equal local images. In the latter case the
quotient is actually symmetric of degree three, both local cores equal
the ambient core, and both local groups supplement the prime-to-three core.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma F.6.11(2), printed pp.306–307. The noncyclicity assertion is separate.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

private noncomputable def twoCoreQuotientEquiv
    (f : G →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    (G ⧸ pCore 2 G) ≃* (H ⧸ pCore 2 H) := by
  let q := (QuotientGroup.mk' (pCore 2 H)).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have he : q.ker = pCore 2 G := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup hf hk
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

variable {G₁ G₂ : Subgroup G}

theorem IsGoldschmidtTriple.primeToThreeCore_subgroup_kernel
    (h : IsGoldschmidtTriple G₁ G₂) (M : Subgroup G) (hM : M ≤ G₁) :
    ((QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap M).ker =
      (pCore 2 G).subgroupOf M := by
  rw [ker_subgroupMap, QuotientGroup.ker_mk']
  ext x
  change x.val ∈ pPrimeCore 3 G ↔ x.val ∈ pCore 2 G
  constructor
  · intro hx
    rw [← h.left_inf_primeToThreeCore]
    exact ⟨hM x.property, hx⟩
  · exact fun hx => twoCore_le_primeToThreeCore hx

theorem IsGoldschmidtTriple.primeToThreeCore_quotient_left
    (h : IsGoldschmidtTriple G₁ G₂) :
    Nonempty (((G₁.map (QuotientGroup.mk' (pPrimeCore 3 G))) ⧸
      pCore 2 (G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)))) ≃*
        Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := h.quotient_left
  refine ⟨(twoCoreQuotientEquiv _
    ((QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap_surjective G₁) ?_).symm.trans e⟩
  rw [h.primeToThreeCore_subgroup_kernel G₁ le_rfl]
  exact pCore_isPGroup.comap_subtype

theorem IsGoldschmidtTriple.primeToThreeCore_quotient_twoCore_eq_bot
    (_h : IsGoldschmidtTriple G₁ G₂) : pCore 2 (G ⧸ pPrimeCore 3 G) = ⊥ := by
  exact le_bot_iff.mp (twoCore_le_primeToThreeCore.trans
    (pPrimeCore_quotient_pPrimeCore_eq_bot 3).le)

noncomputable def IsGoldschmidtTriple.primeToThreeCoreLocalEquiv
    (h : IsGoldschmidtTriple G₁ G₂) (M : Subgroup G) (hM : M ≤ G₁) :
    (M ⧸ (QuotientGroup.mk' (pCore 2 G)).ker.subgroupOf M) ≃*
      M.map (QuotientGroup.mk' (pPrimeCore 3 G)) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [QuotientGroup.ker_mk', h.primeToThreeCore_subgroup_kernel M hM])).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap_surjective M))

theorem IsGoldschmidtTriple.primeToThreeCoreLocalEquiv_mk
    (h : IsGoldschmidtTriple G₁ G₂) (M : Subgroup G) (hM : M ≤ G₁) (g : M) :
    h.primeToThreeCoreLocalEquiv M hM (QuotientGroup.mk' _ g) =
      (QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap M g := by rfl

noncomputable def IsGoldschmidtTriple.primeToThreeCoreAmalgamIso
    (h : IsGoldschmidtTriple G₁ G₂) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroupQuotients (QuotientGroup.mk' (pCore 2 G))
        G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      (RankTwoAmalgam.ofSubgroups
        (G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)))
        ((G₁ ⊓ G₂).map (QuotientGroup.mk' (pPrimeCore 3 G)))
        (G₂.map (QuotientGroup.mk' (pPrimeCore 3 G)))
        (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)) where
  left := h.primeToThreeCoreLocalEquiv G₁ le_rfl
  middle := h.primeToThreeCoreLocalEquiv (G₁ ⊓ G₂) inf_le_left
  right := h.symm.primeToThreeCoreLocalEquiv G₂ le_rfl
  left_commutes b := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ b
    rfl
  right_commutes b := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ b
    rfl

theorem IsGoldschmidtTriple.primeToThreeCoreAmalgamIso_left_mk
    (h : IsGoldschmidtTriple G₁ G₂) (g : G₁) :
    h.primeToThreeCoreAmalgamIso.left (QuotientGroup.mk' _ g) =
      (QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap G₁ g := by rfl

theorem IsGoldschmidtTriple.primeToThreeCoreAmalgamIso_middle_mk
    (h : IsGoldschmidtTriple G₁ G₂) (g : (G₁ ⊓ G₂ : Subgroup G)) :
    h.primeToThreeCoreAmalgamIso.middle (QuotientGroup.mk' _ g) =
      (QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap (G₁ ⊓ G₂) g := by rfl

theorem IsGoldschmidtTriple.primeToThreeCoreAmalgamIso_right_mk
    (h : IsGoldschmidtTriple G₁ G₂) (g : G₂) :
    h.primeToThreeCoreAmalgamIso.right (QuotientGroup.mk' _ g) =
      (QuotientGroup.mk' (pPrimeCore 3 G)).subgroupMap G₂ g := by rfl

private theorem sylow_index_three (S : Sylow 2 G)
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) : (S : Subgroup G).index = 3 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ pCore 2 G
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let R := S.mapSurjective hf
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hR : Nat.card R = 2 := by
    rw [R.card_eq_multiplicity, hc]
    change 2 ^ (Nat.factorization (2 * 3) 2) = 2
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hi := (R : Subgroup (Equiv.Perm (Fin 3))).index_mul_card
  rw [hc, hR] at hi
  have hi3 : (R : Subgroup (Equiv.Perm (Fin 3))).index = 3 := by omega
  change ((S : Subgroup G).map f).index = 3 at hi3
  rwa [Subgroup.index_map_eq _ hf (by rw [hk]; exact pCore_isPGroup.le_sylow_of_normal S)] at hi3

omit [Finite G] in
private theorem intermediate_of_relIndex_three {A B C : Subgroup G}
    (hAB : A ≤ B) (hBC : B ≤ C) (hi : A.relIndex C = 3) : B = A ∨ B = C := by
  have hm := relIndex_mul_relIndex A B C hAB hBC
  rw [hi] at hm
  have hp : (A.relIndex B * B.relIndex C).Prime := hm ▸ Nat.prime_three
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hB⟩ | ⟨_, hA⟩
  · exact Or.inr (le_antisymm hBC (relIndex_eq_one.mp hB))
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp hA) hAB)

theorem IsGoldschmidtTriple.primeToThreeCore_image_intersection_or_eq
    (h : IsGoldschmidtTriple G₁ G₂) :
    (G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)) ⊓
        G₂.map (QuotientGroup.mk' (pPrimeCore 3 G)) =
      (G₁ ⊓ G₂).map (QuotientGroup.mk' (pPrimeCore 3 G))) ∨
    G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)) =
      G₂.map (QuotientGroup.mk' (pPrimeCore 3 G)) := by
  let q := QuotientGroup.mk' (pPrimeCore 3 G)
  let A := G₁.map q
  let B := G₂.map q
  obtain ⟨T, hT⟩ := h.intersection_sylow
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 3 G))
  have hS : (S : Subgroup _) = (G₁ ⊓ G₂).map q := by change (T : Subgroup G).map q = _; rw [hT]
  have hSA : (S : Subgroup _) ≤ A := hS ▸ Subgroup.map_mono inf_le_left
  have hSB : (S : Subgroup _) ≤ B := hS ▸ Subgroup.map_mono inf_le_right
  have hAi : (S : Subgroup _).relIndex A = 3 :=
    sylow_index_three (S.subtype hSA) h.primeToThreeCore_quotient_left.some
  have hBi : (S : Subgroup _).relIndex B = 3 :=
    sylow_index_three (S.subtype hSB) h.symm.primeToThreeCore_quotient_left.some
  rcases intermediate_of_relIndex_three (le_inf hSA hSB) inf_le_left hAi with hI | hA
  · exact Or.inl (hI.trans hS)
  · rcases intermediate_of_relIndex_three (le_inf hSA hSB) inf_le_right hBi with hI | hB
    · exact Or.inl (hI.trans hS)
    · exact Or.inr (hA.symm.trans hB)

theorem IsGoldschmidtTriple.quotient_primeToThreeCore_of_intersection
    (h : IsGoldschmidtTriple G₁ G₂)
    (hi : G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)) ⊓
      G₂.map (QuotientGroup.mk' (pPrimeCore 3 G)) =
      (G₁ ⊓ G₂).map (QuotientGroup.mk' (pPrimeCore 3 G))) :
    IsGoldschmidtTriple (G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)))
      (G₂.map (QuotientGroup.mk' (pPrimeCore 3 G))) := by
  refine ⟨?_, h.primeToThreeCore_quotient_left, h.symm.primeToThreeCore_quotient_left, ?_⟩
  · rw [← Subgroup.map_sup, h.generated,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · obtain ⟨T, hT⟩ := h.intersection_sylow
    refine ⟨T.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
    change _ = (T : Subgroup G).map _
    rw [hi, hT]

omit [Finite G] in
private theorem map_left_eq_top_of_supplement
    (hgen : G₁ ⊔ pPrimeCore 3 G = ⊤) :
    G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)) = ⊤ := by
  apply comap_injective (QuotientGroup.mk'_surjective _)
  rw [comap_map_eq, QuotientGroup.ker_mk', hgen, Subgroup.comap_top]

omit [Finite G] in
private theorem left_surjective_of_supplement
    (hgen : G₁ ⊔ pPrimeCore 3 G = ⊤) :
    Function.Surjective ((QuotientGroup.mk' (pPrimeCore 3 G)).comp G₁.subtype) := by
  apply MonoidHom.range_eq_top.mp
  rw [MonoidHom.range_comp, range_subtype]
  exact map_left_eq_top_of_supplement hgen

theorem IsGoldschmidtTriple.primeToThreeCore_supplement_left_core
    (h : IsGoldschmidtTriple G₁ G₂) (hgen : G₁ ⊔ pPrimeCore 3 G = ⊤) :
    (pCore 2 G₁).map G₁.subtype = pCore 2 G := by
  let f := (QuotientGroup.mk' (pPrimeCore 3 G)).comp G₁.subtype
  have hk : f.ker = (pCore 2 G).subgroupOf G₁ := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    simpa only [ker_subgroupMap, QuotientGroup.ker_mk', subgroupOf] using
      h.primeToThreeCore_subgroup_kernel G₁ le_rfl
  have hp : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup.comap_subtype
  have he := f.comap_pCore_of_ker_isPGroup (left_surjective_of_supplement hgen) hp
  rw [h.primeToThreeCore_quotient_twoCore_eq_bot] at he
  change f.ker = pCore 2 G₁ at he
  rw [← he, hk, map_subgroupOf_eq_of_le (h.twoCore_isGreatest.1.1.trans inf_le_left)]

theorem IsGoldschmidtTriple.primeToThreeCore_supplement_quotient
    (h : IsGoldschmidtTriple G₁ G₂) (hgen : G₁ ⊔ pPrimeCore 3 G = ⊤) :
    Nonempty ((G ⧸ pPrimeCore 3 G) ≃* Equiv.Perm (Fin 3)) := by
  let f := (QuotientGroup.mk' (pPrimeCore 3 G)).comp G₁.subtype
  have hk : f.ker = (pCore 2 G).subgroupOf G₁ := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    simpa only [ker_subgroupMap, QuotientGroup.ker_mk', subgroupOf] using
      h.primeToThreeCore_subgroup_kernel G₁ le_rfl
  have hp : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup.comap_subtype
  let e := (twoCoreQuotientEquiv f (left_surjective_of_supplement hgen) hp).symm.trans
    h.quotient_left.some
  exact ⟨((QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq h.primeToThreeCore_quotient_twoCore_eq_bot.symm)).trans e)⟩

theorem IsGoldschmidtTriple.primeToThreeCore_collapsed_sup
    (h : IsGoldschmidtTriple G₁ G₂)
    (he : G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)) =
      G₂.map (QuotientGroup.mk' (pPrimeCore 3 G))) :
    G₁ ⊔ pPrimeCore 3 G = ⊤ ∧ G₂ ⊔ pPrimeCore 3 G = ⊤ := by
  let q := QuotientGroup.mk' (pPrimeCore 3 G)
  have hg : G₁.map q ⊔ G₂.map q = ⊤ := by
    rw [← Subgroup.map_sup, h.generated, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have h₂ : G₂.map q = ⊤ := by simpa only [q, he, sup_idem] using hg
  have h₁ : G₁.map q = ⊤ := he.trans h₂
  have step (A : Subgroup G) (ha : A.map q = ⊤) : A ⊔ pPrimeCore 3 G = ⊤ := by
    have hm := congrArg (Subgroup.comap q) ha
    simpa only [q, comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] using hm
  exact ⟨step G₁ h₁, step G₂ h₂⟩

open scoped Pointwise in
theorem IsGoldschmidtTriple.primeToThreeCore_collapsed_structure
    (h : IsGoldschmidtTriple G₁ G₂)
    (he : G₁.map (QuotientGroup.mk' (pPrimeCore 3 G)) =
      G₂.map (QuotientGroup.mk' (pPrimeCore 3 G))) :
    (pCore 2 G₁).map G₁.subtype = pCore 2 G ∧
    (pCore 2 G₂).map G₂.subtype = pCore 2 G ∧
    Nonempty ((G ⧸ pPrimeCore 3 G) ≃* Equiv.Perm (Fin 3)) ∧
    (G₁ : Set G) * (pPrimeCore 3 G : Set G) = Set.univ ∧
    (G₂ : Set G) * (pPrimeCore 3 G : Set G) = Set.univ := by
  obtain ⟨h₁, h₂⟩ := h.primeToThreeCore_collapsed_sup he
  refine ⟨h.primeToThreeCore_supplement_left_core h₁,
    h.symm.primeToThreeCore_supplement_left_core h₂,
    h.primeToThreeCore_supplement_quotient h₁, ?_, ?_⟩
  · rw [← mul_normal, h₁]; rfl
  · rw [← mul_normal, h₂]; rfl

end CFSG.Quasithin.ChapterF
