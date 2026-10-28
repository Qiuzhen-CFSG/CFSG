module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.PushingSetup

/-!
# The central residual used to rule out outside A₃-blocks

The preimage of Z(O_p(M/O₂(M))) is normal in M. Its two-residual is
nontrivial, two-perfect, and has prime support {2,p}. It is contained in
the source normalizer residual Y, and its full ambient normalizer is M.

Source: Aschbacher–Smith, printed p.1157, proof of 15.4.3(1).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
variable {G : Type*} [Group G] [Finite G]

@[expose] def quotientCoreCenter (p : ℕ) (M : Subgroup G) : Subgroup (M ⧸ pCore 2 M) :=
  (center (pCore p (M ⧸ pCore 2 M))).map (pCore p (M ⧸ pCore 2 M)).subtype

@[expose] def centralPreimage (p : ℕ) (M : Subgroup G) : Subgroup G :=
  ((quotientCoreCenter p M).comap (QuotientGroup.mk' (pCore 2 M))).map M.subtype

@[expose] def centralResidual (p : ℕ) (M : Subgroup G) : Subgroup G :=
  (pResidual 2 (centralPreimage p M)).map (centralPreimage p M).subtype

omit [Finite G] in
/-- The preimage has exactly the specified central quotient image. -/
theorem quotientImage_centralPreimage (p : ℕ) (M : Subgroup G) :
    quotientImage M (centralPreimage p M) = quotientCoreCenter p M := by
  unfold quotientImage centralPreimage
  rw [subgroupOf, comap_map_eq_self_of_injective M.subtype_injective,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

/-- The odd central quotient is unchanged by the two-residual. -/
theorem quotientImage_centralResidual (p : ℕ) [Fact p.Prime] (hp : Odd p) (M : Subgroup G) :
    quotientImage M (centralResidual p M) = quotientCoreCenter p M := by
  have hAM : centralPreimage p M ≤ M := map_subtype_le _
  rw [centralResidual, quotientImage_residual hAM, quotientImage_centralPreimage]
  have hc : IsPGroup p (quotientCoreCenter p M) := pCore_isPGroup.to_le (map_subtype_le _)
  have ht : pResidual 2 (quotientCoreCenter p M) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, hn⟩ := hc.exists_card_eq
    exact mem_pResidual_of_orderOf_coprime
      ((hp.coprime_two_left.pow_right n).of_dvd_right (hn ▸ _root_.orderOf_dvd_natCard x))
  rw [ht, ← MonoidHom.range_eq_map, range_subtype]

omit [Finite G] in
/-- The central residual is genuinely normal relative to M. -/
theorem centralResidual_normal (p : ℕ) (M : Subgroup G) :
    ((centralResidual p M).subgroupOf M).Normal := by
  unfold centralResidual
  apply normal_embedded_pResidual_subgroupOf 2 (show centralPreimage p M ≤ M from map_subtype_le _)
  rw [centralPreimage, subgroupOf, comap_map_eq_self_of_injective M.subtype_injective]
  have : (quotientCoreCenter p M).Normal := by unfold quotientCoreCenter; infer_instance
  infer_instance

/-- Kernel-image counting retains the two-group kernel and p-group image. -/
theorem prime_support_of_quotient_image {p : ℕ} [Fact p.Prime]
    {M A : Subgroup G} (hAM : A ≤ M)
    (hi : IsPGroup p (quotientImage M A)) (q : ℕ) (hq : q.Prime)
    (hd : q ∣ Nat.card A) : q = 2 ∨ q = p := by
  let f := (QuotientGroup.mk' (pCore 2 M)).comp (inclusion hAM)
  have hr : f.range = quotientImage M A := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨inclusion hAM a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a.val, ha⟩, rfl⟩
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 M).comap (inclusion hAM) := by
      ext x
      change QuotientGroup.mk' (pCore 2 M) (inclusion hAM x) = 1 ↔ inclusion hAM x ∈ pCore 2 M
      exact QuotientGroup.eq_one_iff _
    rw [he]
    exact pCore_isPGroup.comap_of_injective (inclusion hAM) (inclusion_injective hAM)
  rw [← f.ker.card_mul_index, index_ker, hr] at hd
  rcases hq.dvd_mul.mp hd with h | h
  · obtain ⟨n, hn⟩ := hk.exists_card_eq
    exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_two (hn ▸ h))
  · obtain ⟨n, hn⟩ := hi.exists_card_eq
    exact Or.inr (Nat.prime_eq_prime_of_dvd_pow hq Fact.out (hn ▸ h))

/-- Prime support of the actual central residual. -/
theorem centralResidual_prime_support (p : ℕ) [Fact p.Prime] (hp : Odd p) (M : Subgroup G)
    (q : ℕ) (hq : q.Prime) (hd : q ∣ Nat.card (centralResidual p M)) : q = 2 ∨ q = p := by
  have hAM : centralResidual p M ≤ M := (map_subtype_le _).trans (map_subtype_le _)
  apply prime_support_of_quotient_image hAM _ q hq hd
  rw [quotientImage_centralResidual p hp]
  exact pCore_isPGroup.to_le (map_subtype_le _)

/-- A nontrivial p-core has nontrivial center; the odd image survives O². -/
theorem centralResidual_ne_bot (p : ℕ) [Fact p.Prime] (hp : Odd p) (M : Subgroup G)
    (hne : pCore p (M ⧸ pCore 2 M) ≠ ⊥) : centralResidual p M ≠ ⊥ := by
  let P := pCore p (M ⧸ pCore 2 M)
  let : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  let : Group.IsNilpotent P := (pCore_isPGroup (p := p) (G := M ⧸ pCore 2 M)).isNilpotent
  have hz : quotientCoreCenter p M ≠ ⊥ := fun he =>
    Group.IsNilpotent.center_ne_bot P
      ((map_eq_bot_iff_of_injective _ P.subtype_injective).mp he)
  intro hb
  apply hz
  rw [← quotientImage_centralResidual p hp M, hb]
  simp [quotientImage, subgroupOf]

/-- The central preimage normalizes X by the proved residual lifting identity. -/
theorem centralResidual_le_normalizerResidual (T : Sylow 2 G) {p : ℕ} [Fact p.Prime]
    {X M : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hXM : X ⊔ (T : Subgroup G) ≤ M)
    (hXp : quotientImage M X ≤ pCore p (M ⧸ pCore 2 M)) :
    centralResidual p M ≤ normalizerResidual M X := by
  apply embedded_pResidual_mono
  refine le_inf (map_mono (comap_mono ((map_subtype_le _).trans (pCore_le_fitting _ p)))) ?_
  rintro _ ⟨m, hm, rfl⟩
  have hcentral : QuotientGroup.mk' (pCore 2 M) m ∈ centralizer (quotientImage M X : Set _) := by
    obtain ⟨z, hz, he⟩ := hm
    rw [← he]
    apply mem_centralizer_iff.mpr
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hXp hx⟩)
  have hn : m ∈ (normalizer (quotientImage M X : Set _)).comap (QuotientGroup.mk' (pCore 2 M)) :=
    Subgroup.centralizer_le_normalizer _ hcentral
  rw [(xi_quotient_normalizers T hX hXM).1,
    ← subgroupOf_normalizer_eq (le_sup_left.trans hXM)] at hn
  exact hn

/-- A nontrivial normal subgroup in characteristic two has nontrivial two-core.
Maximal two-locality therefore identifies its full ambient normalizer. -/
theorem normalizer_eq_of_normal_in_maximal_twoLocal {M A : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hHe : M ∈ Chapter1.He G)
    (hAM : A ≤ M) (hn : (A.subgroupOf M).Normal) (hne : A ≠ ⊥) :
    normalizer (A : Set G) = M := by
  have hAe := Chapter1.lemma_1_1_3_1 hHe hne hAM hn.isSubnormal
  have hcore : A.pCoreIn 2 ≠ ⊥ := by
    intro hb
    apply hne
    apply bot_unique
    intro a ha
    have hc : a ∈ centralizer (A.pCoreIn 2 : Set G) := by
      intro y hy
      have hy1 : y = 1 := by
        change y ∈ A.pCoreIn 2 at hy
        rw [hb] at hy
        exact hy
      simp [hy1]
    exact hb ▸ hAe ⟨ha, hc⟩
  have hMN : M ≤ normalizer (A : Set G) := (normal_subgroupOf_iff_le_normalizer hAM).mp hn
  have hNC := normalizer_le_normalizer_characteristic_image A (pCore 2 A)
  have hlocal : IsTwoLocal (normalizer (A.pCoreIn 2 : Set G)) :=
    ⟨_, hcore, isPGroup_pCoreIn 2 A, rfl⟩
  have he := hM.eq_of_le hlocal (hMN.trans hNC)
  exact le_antisymm (hNC.trans he.symm.le) hMN

omit [Finite G] in
/-- An actual lowercase ξ image cannot vanish in a quotient by a two-core. -/
theorem xi_quotientImage_ne_bot {T X M : Subgroup G}
    (hX : X ∈ Xi T) (hXM : X ≤ M) : quotientImage M X ≠ ⊥ := by
  intro hb
  have hle : X.subgroupOf M ≤ pCore 2 M := by
    simpa only [quotientImage, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hb
  have hp : IsPGroup 2 X := (pCore_isPGroup.to_le hle).of_equiv (subgroupOfEquivOfLe hXM)
  apply Xi.core_ne_top hX
  apply top_unique
  exact le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩

/-- The source supplies every property of Y₀ used by the outside-block argument. -/
theorem source_centralResidual (T : Sylow 2 G) (h : SourceHypotheses T)
    (h42 : Earlier1542 (G := G)) {X : Subgroup G} (hX : X ∈ Xi (T : Subgroup G))
    (hp : 3 < (pCore 2 X).index)
    (hmax : ∀ Y ∈ Xi (T : Subgroup G), (pCore 2 Y).index ≤ (pCore 2 X).index)
    {M H : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hXM : X ⊔ (T : Subgroup G) ≤ M) (hNH : normalizer (X : Set G) ≤ H) :
    let Y₀ := centralResidual (pCore 2 X).index M
    Y₀ ≠ ⊥ ∧ Y₀ ≤ normalizerResidual M X ∧ Y₀ ≤ M ⊓ H ∧
      IsPPerfect 2 Y₀ ∧ (Y₀.subgroupOf M).Normal ∧ normalizer (Y₀ : Set G) = M ∧
      (∀ q : ℕ, q.Prime → q ∣ Nat.card Y₀ → q = 2 ∨ q = (pCore 2 X).index) := by
  let p := (pCore 2 X).index
  let : Fact p.Prime := ⟨hX.2.2.2.1⟩
  have hi := source_quotient_image_le_core T h h42 hX hp hmax hM hXM
  have hnz : pCore p (M ⧸ pCore 2 M) ≠ ⊥ := fun he =>
    xi_quotientImage_ne_bot hX (le_sup_left.trans hXM) (bot_unique (he ▸ hi))
  have hn := centralResidual_ne_bot p hX.2.2.2.2 M hnz
  have hle := centralResidual_le_normalizerResidual T hX hXM hi
  have hXF := (source_iterated_core_containment T h h42 hX hp hmax hM hXM).1.trans
    (twoPrimePreimage_le_twoFittingPreimage p M)
  have hYI := hle.trans (normalizerResidual_bounds T hX hXF hNH).2
  have hHe : M ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    (h.simpleQTKE.evenCharacteristic T M hM (le_sup_right.trans hXM))
  exact ⟨hn, hle, hYI, isPPerfect_embedded_pResidual 2 _, centralResidual_normal p M,
    normalizer_eq_of_normal_in_maximal_twoLocal hM hHe (hYI.trans inf_le_left)
      (centralResidual_normal p M) hn,
    centralResidual_prime_support p hX.2.2.2.2 M⟩
end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
