module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveCoreGeneration
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryGeometry

/-!
# Movement-free source applications of the nonblock sieve

All images here use one literal normalQuotientAction on the full component
quotient. Ambient core movement and the proposed whole-radical generation
identity pass through that same map. The original subgroup geometry supplies
perfectness, innerness, mutual normalization and the secondary-core image
bound. These prove the binary and both unitary exclusions using only core
movement and explicitly assumed generation.

For central secondary-core images, perfectness kills the radical-secondary
commutator. Thus a trivial torus image kills the radical by generation.
The prime-torus extractor explicitly requires a nontrivial image, and the
conditional exceptional-model assembly retains its model inspection, core
centrality, prime exclusions and generation inputs. It does not construct
those inputs or a source witness.

No SecondaryData witness is used or reconstructed. The source-record owner,
`qt-d-1222-rankone-uniqueness-nonblock`, supplies the actual secondary witness
and must establish generation for the whole radical, including any part
outside K. The sieve owner retains model inspection and the remaining model
centralizer applications.
Source: Aschbacher–Smith, original 4.3.11–16, printed pp.617–618;
see the movement correction in `docs/quasithin-proof-basis.md`.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve

namespace SourceImages
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable (c : SourceConfiguration T L) (C : Subgroup (rootNormalizer c)) [C.Normal]

/-- Every subgroup in this source adapter uses the same literal quotient action. -/
def image (B : Subgroup G) : Subgroup (MulAut (C ⧸ pCore 2 C)) :=
  (B.subgroupOf (rootNormalizer c)).map (normalQuotientAction C (pCore 2 C))

omit [Finite G] in
/-- Ambient commutators pass through restriction to the root normalizer and its action. -/
theorem image_commutator (A B : Subgroup G)
    (hA : A ≤ rootNormalizer c) (hB : B ≤ rootNormalizer c) :
    image c C ⁅A,B⁆ = ⁅image c C A,image c C B⁆ := by
  have he : ⁅A.subgroupOf (rootNormalizer c),B.subgroupOf (rootNormalizer c)⁆ =
      ⁅A,B⁆.subgroupOf (rootNormalizer c) := by
    apply map_injective (rootNormalizer c).subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hA,map_subgroupOf_eq_of_le hB,
      map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup A B).trans (sup_le hA hB))]
  simp only [image,← map_commutator,he]

omit [Finite G] in
/-- Normalization is preserved by the same restricted action. -/
theorem image_normalizes {A B : Subgroup G} (h : A ≤ normalizer (B : Set G)) :
    image c C A ≤ normalizer (image c C B : Set _) := by
  have hh : A.subgroupOf (rootNormalizer c) ≤
      normalizer (B.subgroupOf (rootNormalizer c) : Set (rootNormalizer c)) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro b
    exact mem_normalizer_iff.mp (h ha) b.val
  exact (map_mono hh).trans ((B.subgroupOf (rootNormalizer c)).le_normalizer_map _)

/-- The original secondary group gives a perfect action image. -/
theorem secondary_perfect (hK : secondary c ≤ rootNormalizer c) :
    Group.IsPerfect (image c C (secondary c)) := by
  let := EndgameSieve.secondary_perfect c
  let e := subgroupOfEquivOfLe hK
  let : Group.IsPerfect ((secondary c).subgroupOf (rootNormalizer c)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.IsPerfect.map _

omit [Finite G] in
/-- The original secondary image is inner on the full component quotient. -/
theorem secondary_inner (hK : secondary c ≤ C.map (rootNormalizer c).subtype) :
    image c C (secondary c) ≤ MulAut.innerSubgroup (C ⧸ pCore 2 C) := by
  rintro a ⟨x,hx,rfl⟩
  obtain ⟨z,hz,hzx⟩ := hK hx
  have he : z = x := Subtype.ext hzx
  subst z
  exact ⟨QuotientGroup.mk' (pCore 2 C) ⟨x,hz⟩,
    (normalQuotientAction_inner C (pCore 2 C) ⟨x,hz⟩).symm⟩

/-- Only the original core is moved by the torus. -/
theorem core_moved (Y : Subgroup G) (hR : R₂ c ≤ rootNormalizer c)
    (hY : Y ≤ rootNormalizer c) (hm : ⁅Q c,Y⁆ = Q c) :
    ⁅image c C (Q c),image c C Y⁆ = image c C (Q c) := by
  rw [← image_commutator c C _ _ ((core_le_radical c).trans hR) hY,hm]

/-- The proposed whole-radical generation premise has its literal action-image form. -/
theorem generation_image (hK : secondary c ≤ rootNormalizer c)
    (hR : R₂ c ≤ rootNormalizer c) (hg : Q c ⊔ ⁅R₂ c,secondary c⁆ = R₂ c) :
    image c C (Q c) ⊔ ⁅image c C (R₂ c),image c C (secondary c)⁆ = image c C (R₂ c) := by
  rw [← image_commutator c C _ _ hR hK]
  have hs : (Q c ⊔ ⁅R₂ c,secondary c⁆).subgroupOf (rootNormalizer c) =
      (Q c).subgroupOf (rootNormalizer c) ⊔ ⁅R₂ c,secondary c⁆.subgroupOf (rootNormalizer c) := by
    apply map_injective (rootNormalizer c).subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le ((core_le_radical c).trans hR),
      map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup _ _).trans (sup_le hR hK)),
      map_subgroupOf_eq_of_le (sup_le ((core_le_radical c).trans hR)
        ((Subgroup.commutator_le_sup _ _).trans (sup_le hR hK)))]
  have he := congrArg (image c C) hg
  unfold image at he
  rw [hs,Subgroup.map_sup] at he
  exact he

/-- The literal core and radical images satisfy the two-group and normalization
hypotheses used in the repaired model rows, without a secondary-data record. -/
theorem radical_geometry
    (hn : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G)) :
    IsPGroup 2 (image c C (R₂ c)) ∧ image c C (Q c) ≤ image c C (R₂ c) ∧
      image c C (secondary c) ≤ normalizer (image c C (Q c) : Set _) ∧
      image c C (secondary c) ≤ normalizer (image c C (R₂ c) : Set _) ∧
      image c C (R₂ c) ≤ normalizer (image c C (secondary c) : Set _) := by
  refine ⟨((isPGroup_pCoreIn 2 (secondary c ⊔ S c)).comap_subtype).map _,
    map_mono (subgroupOf_mono _ (core_le_radical c)),?_,?_,?_⟩
  · exact image_normalizes c C ((secondary_le_original.trans (map_subtype_le _)).trans (core_normalized c))
  · exact image_normalizes c C (secondary_normalizes_radical c)
  · exact image_normalizes c C ((R₂ c).le_normalizer.trans (hn.trans inf_le_right))

omit [Finite G] in
/-- The original secondary two-core maps into the embedded two-core of its
actual action image. This is containment, with no assumption on the action kernel. -/
theorem secondary_core_le :
    image c C ((secondary c).pCoreIn 2) ≤ (image c C (secondary c)).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes
  · exact ((isPGroup_pCoreIn 2 (secondary c)).comap_subtype).map _
  · exact map_mono (subgroupOf_mono _ (pCoreIn_le 2 (secondary c)))
  · exact image_normalizes c C ((secondary c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (secondary c) (pCore 2 (secondary c))))

/-- The binary model kills the original secondary-core image, so the source
commutator bound suffices for full torus centralization. -/
theorem binary_torus_centralizes {m : ℕ}
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (2 ^ m))
    (Y : Subgroup G) (hK : secondary c ≤ C.map (rootNormalizer c).subtype)
    (hY : Y ≤ rootNormalizer c) (hcomm : ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2) :
    image c C Y ≤ centralizer (image c C (secondary c) : Set _) := by
  let := secondary_perfect c C (hK.trans (map_subtype_le _))
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [commutator_comm,← image_commutator c C _ _ (hK.trans (map_subtype_le _)) hY]
  apply bot_unique
  have hb := binary_inner_twoCore_eq_bot hm (image c C (secondary c)) (secondary_inner c C hK)
  exact (map_mono (subgroupOf_mono _ hcomm)).trans ((secondary_core_le c C).trans hb.le)

/-- The repaired binary row on the actual action. The source torus commutator bound
supplies centralization; only the core is assumed moved. -/
theorem binary_radical_eq_bot {m : ℕ}
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (2 ^ m))
    (Y : Subgroup G) (hK : secondary c ≤ C.map (rootNormalizer c).subtype)
    (hR : R₂ c ≤ rootNormalizer c) (hY : Y ≤ rootNormalizer c)
    (hn : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (hne : image c C (secondary c) ≠ ⊥)
    (hcomm : ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2)
    (hmoved : ⁅Q c,Y⁆ = Q c)
    (hgen : image c C (Q c) ⊔ ⁅image c C (R₂ c),image c C (secondary c)⁆ = image c C (R₂ c)) :
    image c C (R₂ c) = ⊥ := by
  let := secondary_perfect c C (hK.trans (map_subtype_le _))
  obtain ⟨h2,hQR,hXQ,hXR,hRX⟩ := radical_geometry c C hn
  exact binary_generated_twoGroup_eq_bot hm _ hne (secondary_inner c C hK) _ _ _ h2 hQR hXQ hXR hRX
    (binary_torus_centralizes c C hm Y hK hY hcomm)
    (core_moved c C Y hR hY hmoved) hgen

/-- Both full unitary rows are excluded on the literal action using only core
movement and the separately supplied whole-radical generation identity. -/
theorem unitary_radical_eq_bot [Group.IsPerfect (C ⧸ pCore 2 C)] {n : ℕ} (hn : 1 < n)
    (hm : Chapter1.Section02.LocalModels.IsSU (C ⧸ pCore 2 C) 3 (2 ^ n) ∨
      ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 (2 ^ n))
    (Y : Subgroup G) (hK : secondary c ≤ C.map (rootNormalizer c).subtype)
    (hR : R₂ c ≤ rootNormalizer c) (hY : Y ≤ rootNormalizer c)
    (hN : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (hne : image c C (secondary c) ≠ ⊥) (hmoved : ⁅Q c,Y⁆ = Q c)
    (hgen : image c C (Q c) ⊔ ⁅image c C (R₂ c),image c C (secondary c)⁆ = image c C (R₂ c)) :
    image c C (R₂ c) = ⊥ := by
  let := secondary_perfect c C (hK.trans (map_subtype_le _))
  obtain ⟨h2,hQR,_,hXR,_⟩ := radical_geometry c C hN
  have hi := secondary_inner c C hK
  have hmove := core_moved c C Y hR hY hmoved
  rcases hm with hm | hm
  · exact special_unitary_generated_twoGroup_eq_bot hn hm _ hne hi _ _ _ h2 hQR hXR hmove hgen
  · exact unitary_generated_twoGroup_eq_bot hn hm _ hne hi _ _ _ h2 hQR hXR hmove hgen

/-- In rows with central secondary-core image, killing the torus kills the whole
radical by generation and perfectness, even though the torus need not move it. -/
theorem radical_eq_bot_of_torus_eq_bot
    (Y : Subgroup G) (hK : secondary c ≤ rootNormalizer c)
    (hR : R₂ c ≤ rootNormalizer c) (hY : Y ≤ rootNormalizer c)
    (hN : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (hc : image c C ((secondary c).pCoreIn 2) ≤ centralizer (image c C (secondary c) : Set _))
    (hmoved : ⁅Q c,Y⁆ = Q c)
    (hgen : image c C (Q c) ⊔ ⁅image c C (R₂ c),image c C (secondary c)⁆ = image c C (R₂ c))
    (hzero : image c C Y = ⊥) : image c C (R₂ c) = ⊥ := by
  let := secondary_perfect c C hK
  have hQ : image c C (Q c) = ⊥ := by
    rw [← core_moved c C Y hR hY hmoved,hzero,commutator_bot_right]
  have hcomm : ⁅image c C (R₂ c),image c C (secondary c)⁆ = ⊥ := by
    apply commutator_eq_bot_of_iterated_eq_bot
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_trans _ hc
    rw [← image_commutator c C _ _ hR hK]
    apply map_mono
    apply subgroupOf_mono
    rw [commutator_comm]
    exact commutator_le_pCore_of_mutual_normalization _ _ (isPGroup_pCoreIn 2 _)
      (secondary_normalizes_radical c) ((R₂ c).le_normalizer.trans (hN.trans inf_le_right))
  rw [← hgen,hQ,hcomm,bot_sup_eq]
/-- Cauchy extraction on the literal torus action, retaining the necessary
nontrivial-image premise. Core movement alone does not supply that premise. -/
theorem torus_prime_action_of_nontrivial_image {n : ℕ} (hn : 0 < n)
    (Y : Subgroup G) (hY : Y ≤ rootNormalizer c) (hcard : Nat.card Y = 2 ^ n - 1)
    (hne : image c C Y ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ 2 ^ n - 1 ∧
      ∃ y : rootNormalizer c, (y : G) ∈ Y ∧
        orderOf (normalQuotientAction C (pCore 2 C) y) = p := by
  have hnc : Nat.card (image c C Y) ≠ 1 := fun he => hne ((image c C Y).eq_bot_of_card_eq he)
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hnc
  have hdiv : Nat.card (image c C Y) ∣ 2 ^ n - 1 := by
    have hh := (Y.subgroupOf (rootNormalizer c)).card_map_dvd (normalQuotientAction C (pCore 2 C))
    rw [Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv,hcard] at hh
    exact hh
  have hd := hpd.trans hdiv
  have ho : Odd (2 ^ n - 1) := by
    rw [Nat.odd_iff]
    have h2 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt hn))
    have hpos : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    omega
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := image c C Y) p hpd
  obtain ⟨y,hy,he⟩ := a.property
  refine ⟨p,hp,ho.of_dvd_nat hd,hd,y,hy,?_⟩
  rw [he,Subgroup.orderOf_coe]
  exact ha

/-- Centrality of the original secondary-core image lifts the torus commutator
bound to centralization of the full secondary image. -/
theorem torus_centralizes (Y : Subgroup G) (hK : secondary c ≤ rootNormalizer c)
    (hY : Y ≤ rootNormalizer c) (hcomm : ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2)
    (hc : image c C ((secondary c).pCoreIn 2) ≤ centralizer (image c C (secondary c) : Set _)) :
    image c C Y ≤ centralizer (image c C (secondary c) : Set _) := by
  let := secondary_perfect c C hK
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_eq_bot_of_iterated_eq_bot
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [commutator_comm,← image_commutator c C _ _ hK hY]
  exact (map_mono (subgroupOf_mono _ hcomm)).trans hc

/-- Under core centrality and whole-radical generation, the prescribed
nontrivial radical image forces a nontrivial torus image. This replaces the
legacy argument that inferred it from whole-radical torus movement. -/
theorem torus_image_ne_bot_of_radical_action
    (Y : Subgroup G) (hK : secondary c ≤ rootNormalizer c)
    (hR : R₂ c ≤ rootNormalizer c) (hY : Y ≤ rootNormalizer c)
    (hN : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (hc : image c C ((secondary c).pCoreIn 2) ≤ centralizer (image c C (secondary c) : Set _))
    (hmoved : ⁅Q c,Y⁆ = Q c)
    (hgen : image c C (Q c) ⊔ ⁅image c C (R₂ c),image c C (secondary c)⁆ = image c C (R₂ c))
    (hrad : image c C (R₂ c) ≠ ⊥) : image c C Y ≠ ⊥ := by
  intro hy
  exact hrad (radical_eq_bot_of_torus_eq_bot c C Y hK hR hY hN hc hmoved hgen hy)

/-- Prime centralizer exclusions kill the torus, with no nontriviality assumption
on its action and no movement assumption on the radical. -/
theorem torus_eq_bot_of_prime_centralizers {n : ℕ} (hn : 0 < n)
    (Y : Subgroup G) (hK : secondary c ≤ rootNormalizer c)
    (hY : Y ≤ rootNormalizer c) (hcard : Nat.card Y = 2 ^ n - 1)
    (hcomm : ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2)
    (hc : image c C ((secondary c).pCoreIn 2) ≤ centralizer (image c C (secondary c) : Set _))
    (he : ∀ p : ℕ, p.Prime → Odd p → p ∣ 2 ^ n - 1 →
      ∀ a ∈ image c C Y, a ∈ centralizer (image c C (secondary c) : Set _) → orderOf a ≠ p) :
    image c C Y = ⊥ := by
  by_contra hne
  obtain ⟨p,hp,ho,hd,y,hy,hyorder⟩ := torus_prime_action_of_nontrivial_image c C hn Y hY hcard hne
  have hya : normalQuotientAction C (pCore 2 C) y ∈ image c C Y := mem_map_of_mem _ hy
  exact he p hp ho hd _ hya (torus_centralizes c C Y hK hY hcomm hc hya) hyorder

/-- Movement-free counterpart of the original source sieve on the literal full
quotient. All four 4.3.16 rows and the terminal outer-action clause are retained.
The model inspection, centrality and prime exclusions remain explicit inputs;
this is not an unconditional source theorem. -/
theorem exceptional_of_source_inputs {n : ℕ} (hn : 1 < n)
    (Y : Subgroup G) (hK : secondary c ≤ rootNormalizer c)
    (hR : R₂ c ≤ rootNormalizer c) (hY : Y ≤ rootNormalizer c)
    (hN : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (hcard : Nat.card Y = 2 ^ n - 1) (hcomm : ⁅secondary c,Y⁆ ≤ (secondary c).pCoreIn 2)
    (hmoved : ⁅Q c,Y⁆ = Q c)
    (hgen : image c C (Q c) ⊔ ⁅image c C (R₂ c),image c C (secondary c)⁆ = image c C (R₂ c))
    (hrad : image c C (R₂ c) ≠ ⊥)
    (hm : NonexceptionalModel (C ⧸ pCore 2 C) n ∨
      (ExceptionalModel (C ⧸ pCore 2 C) n ∧
        image c C Y ⊓ MulAut.innerSubgroup (C ⧸ pCore 2 C) = ⊥))
    (hc : NonexceptionalModel (C ⧸ pCore 2 C) n →
      image c C ((secondary c).pCoreIn 2) ≤ centralizer (image c C (secondary c) : Set _))
    (he : NonexceptionalModel (C ⧸ pCore 2 C) n →
      ∀ p : ℕ, p.Prime → Odd p → p ∣ 2 ^ n - 1 →
      ∀ a ∈ image c C Y, a ∈ centralizer (image c C (secondary c) : Set _) → orderOf a ≠ p) :
    ExceptionalModel (C ⧸ pCore 2 C) n ∧
      image c C Y ⊓ MulAut.innerSubgroup (C ⧸ pCore 2 C) = ⊥ := by
  rcases hm with hm | hm
  · let hc' := hc hm
    have hradzero : image c C (R₂ c) = ⊥ :=
      radical_eq_bot_of_torus_eq_bot c C Y hK hR hY hN hc' hmoved hgen
        (torus_eq_bot_of_prime_centralizers c C (by omega) Y hK hY hcard hcomm hc'
          (he hm))
    exact (hrad hradzero).elim
  · exact hm
