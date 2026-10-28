module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobal
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction

/-!
# The small-Cartan consequence of the field-action reduction

The orthogonal row of original 5.1.6 supplies two literal torus factors.
The minus factor centralizes Ω₁(Z(T)), so its join with H has nontrivial
two-core. If the plus join also had nontrivial core, local control would
make both factors normalize O²(H), contradicting the whole join's zero
core. The source's conditional bound therefore gives n = 4 or 8.

At n = 8 the minus factor has order 17 and is retained. The plus factor
has order 15, so Cauchy's theorem and Lagrange's theorem construct its
order-three and order-five generators. The n = 2 and n = 4 rows use the
same literal Hall orders. The field-action reduction remains an explicit
source obligation; this module does not assert original 5.1.6.

Source: Aschbacher--Smith, 5.1.6 and the first paragraphs of 5.2.2,
printed pp.631--633,647 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The torus geometry of the higher-degree orthogonal row in 5.1.6.
Its bound is conditional on the core of the plus join, and the centralizer
is that of the original Sylow omega-center. This is an output contract. -/
def CartanHigherFieldReduction (T : Sylow 2 G) (H A : Subgroup G) (n : ℕ) : Prop :=
  4 ∣ n ∧ ∃ Dminus Dplus : Subgroup G,
    Dminus ⊔ Dplus = A ∧
    Nat.card Dminus = 2 ^ (n / 2) + 1 ∧
    Nat.card Dplus = 2 ^ (n / 2) - 1 ∧
    Dminus ⊔ H ≤ omegaCentralizer T ∧
    ((Dplus ⊔ H).pCoreIn 2 ≠ ⊥ ∨ n ≤ 8)

/-- The numerical and torus-action consequence of original 5.1.6 before
local control is used. This is an output contract, not a source theorem. -/
def CartanFieldReduction (T : Sylow 2 G) (H A : Subgroup G) (n : ℕ) : Prop :=
  n = 2 ∨ n = 4 ∨ CartanHigherFieldReduction T H A n

/-- A nontrivial central omega subgroup lies in the two-core of the
literal join. Here H contains the original Sylow and already has nonzero core. -/
theorem core_ne_bot_of_omega_centralizes {T : Sylow 2 G} {D H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hH : H.pCoreIn 2 ≠ ⊥)
    (hc : D ⊔ H ≤ omegaCentralizer T) : (D ⊔ H).pCoreIn 2 ≠ ⊥ := by
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hT : (T : Subgroup G) ≠ ⊥ := fun he => hH (bot_unique (he ▸ hQT))
  let : Nontrivial T := (nontrivial_iff_ne_bot _).mpr hT
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  have hZ : Z ≠ ⊥ := by
    intro he
    exact omega_center_ne_bot T.isPGroup'
      ((Subgroup.map_eq_bot_iff_of_injective _ (f := (T : Subgroup G).subtype)
        (T : Subgroup G).subtype_injective).mp he)
  have hZT : Z ≤ (T : Subgroup G) := fun x hx =>
    ((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  have hZcore : Z ≤ (D ⊔ H).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hZT)
      (hZT.trans (hTH.trans le_sup_right))
      (hc.trans (Subgroup.centralizer_le_normalizer _))
  exact fun he => hZ (bot_unique (he ▸ hZcore))

private theorem split_card_fifteen (D : Subgroup G) (hD : Nat.card D = 15) :
    ∃ A₃ A₅ : Subgroup G, A₃ ⊔ A₅ = D ∧ Nat.card A₃ = 3 ∧ Nat.card A₅ = 5 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) 3 (n := 1) (by
    rw [hD]; norm_num)
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) 5 (n := 1) (by
    rw [hD]; norm_num)
  let A₃ := P.map D.subtype
  let A₅ := Q.map D.subtype
  have h3 : Nat.card A₃ = 3 := by
    rw [card_map_of_injective D.subtype_injective]
    simpa only [pow_one] using hP
  have h5 : Nat.card A₅ = 5 := by
    rw [card_map_of_injective D.subtype_injective]
    simpa only [pow_one] using hQ
  have h3d : 3 ∣ Nat.card (A₃ ⊔ A₅ : Subgroup G) := by
    rw [← h3]
    exact card_dvd_of_le le_sup_left
  have h5d : 5 ∣ Nat.card (A₃ ⊔ A₅ : Subgroup G) := by
    rw [← h5]
    exact card_dvd_of_le le_sup_right
  have h15 : 15 ∣ Nat.card (A₃ ⊔ A₅ : Subgroup G) :=
    (by decide : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd h3d h5d
  refine ⟨A₃, A₅, eq_of_le_of_card_ge (sup_le (map_subtype_le _) (map_subtype_le _)) ?_, h3, h5⟩
  rw [hD]
  exact Nat.le_of_dvd (Nat.card_pos) h15

/-- The two small rows of 5.1.6 need no higher-field input.  The literal
Cartan has order three in degree two and order fifteen in degree four; in the
latter case Cauchy's theorem supplies the actual order-three and order-five
subgroups. The factor whose join with H has nontrivial two-core is the
trivial subgroup in both rows. -/
theorem cartanSmallGeneration_of_degree_two_or_four
    {T : Sylow 2 G} {L H A : Subgroup G} {n : ℕ}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcard : Nat.card A = 2 ^ n - 1)
    (hn : n = 2 ∨ n = 4) : CartanSmallGeneration A H n := by
  have hHcore : ((⊥ : Subgroup G) ⊔ H).pCoreIn 2 ≠ ⊥ := by
    simpa only [bot_sup_eq] using (show H.pCoreIn 2 ≠ ⊥ from hH.1.1.1)
  rcases hn with rfl | rfl
  · refine ⟨Or.inl rfl, ⊥, A, ⊥, by simp, hHcore, Or.inr ?_, Or.inl rfl⟩
    simpa using hcard
  · obtain ⟨A₃, A₅, hsup, h3, h5⟩ := split_card_fifteen A (by simpa using hcard)
    exact ⟨Or.inr (Or.inl rfl), ⊥, A₃, A₅,
      by simpa only [bot_sup_eq] using hsup, hHcore, Or.inr h3, Or.inr h5⟩

/-- In the split orthogonal branch, local control forces the plus join
to have trivial core: otherwise both torus factors normalize O²(H),
contradicting the zero core of the whole Cartan join. -/
theorem CartanFieldReduction.small_degree_and_split
    {κ : GroupClass} {T : Sylow 2 G} {L W H A : Subgroup G} {n : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hr : CartanFieldReduction T H A n) (hc : CartanLocalControl A H)
    (hzero : (A ⊔ H).pCoreIn 2 = ⊥) :
    n = 2 ∨ n = 4 ∨ (n = 8 ∧ ∃ Dminus Dplus : Subgroup G,
      Dminus ⊔ Dplus = A ∧ Nat.card Dminus = 17 ∧ Nat.card Dplus = 15 ∧
      (Dminus ⊔ H).pCoreIn 2 ≠ ⊥) := by
  rcases hr with hn | hn | ⟨hfour, Dminus, Dplus, hsup, hm, hp, hcentral, hbound⟩
  · exact Or.inl hn
  · exact Or.inr (Or.inl hn)
  have hmcore := core_ne_bot_of_omega_centralizes hH.1.1.2 hH.1.1.1 hcentral
  have hmA : Dminus ≤ A := hsup ▸ le_sup_left
  have hpA : Dplus ≤ A := hsup ▸ le_sup_right
  have hpzero : (Dplus ⊔ H).pCoreIn 2 = ⊥ := by
    by_contra hpnonzero
    have hAN : A ≤ normalizer (residual H : Set G) := by
      rw [← hsup]
      exact sup_le (hc Dminus hmA hmcore) (hc Dplus hpA hpnonzero)
    exact (h.cartan_core_ne_bot_iff hH hc le_rfl).mpr hAN hzero
  have hle : n ≤ 8 := hbound.resolve_left (fun hn => hn hpzero)
  have hn : n = 4 ∨ n = 8 := by
    have := h.exponent
    obtain ⟨k, hk⟩ := hfour
    omega
  rcases hn with hn | hn
  · exact Or.inr (Or.inl hn)
  · refine Or.inr (Or.inr ⟨hn, Dminus, Dplus, hsup, ?_, ?_, hmcore⟩)
    · simpa [hn] using hm
    · simpa [hn] using hp

/-- Construct the exact three factors consumed by 5.2.2 from the source
field reduction and the order of the original Hall Cartan. -/
theorem cartanSmallGeneration_of_fieldReduction
    {κ : GroupClass} {T : Sylow 2 G} {L W H A : Subgroup G} {n : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hr : CartanFieldReduction T H A n) (hc : CartanLocalControl A H)
    (hzero : (A ⊔ H).pCoreIn 2 = ⊥) (hcard : Nat.card A = 2 ^ n - 1) :
    CartanSmallGeneration A H n := by
  have hHcore : ((⊥ : Subgroup G) ⊔ H).pCoreIn 2 ≠ ⊥ := by
    simpa only [bot_sup_eq] using (show H.pCoreIn 2 ≠ ⊥ from hH.1.1.1)
  rcases hr.small_degree_and_split h hH hc hzero with hn | hn | ⟨hn, Dminus, Dplus, hs, hm, hp, hmc⟩
  · refine ⟨Or.inl hn, ⊥, A, ⊥, by simp, hHcore, Or.inr ?_, Or.inl rfl⟩
    simpa [hn] using hcard
  · have h15 : Nat.card A = 15 := by simpa [hn] using hcard
    obtain ⟨A₃, A₅, hs, h3, h5⟩ := split_card_fifteen A h15
    exact ⟨Or.inr (Or.inl hn), ⊥, A₃, A₅, by simpa only [bot_sup_eq] using hs,
      hHcore, Or.inr h3, Or.inr h5⟩
  · obtain ⟨A₃, A₅, hsup, h3, h5⟩ := split_card_fifteen Dplus hp
    exact ⟨Or.inr (Or.inr hn), Dminus, A₃, A₅,
      by rw [sup_assoc, hsup, hs], hmc, Or.inr h3, Or.inr h5⟩

/-- The still-unproved portion of original 5.1.6 required by this
consumer. Local Cartan control is absent: it is used only after this
field-action reduction. The field exponent is the original n of L. -/
def SourceCartanFieldReduction (κ : GroupClass.{u})
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ), Input κ T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        (A ⊔ H).pCoreIn 2 = ⊥ → CartanFieldReduction T H A n

/-- The nonnormal-Sylow and field-automorphism argument at the start of
5.1.6. It is independent of the later module analysis and local control. -/
def SourceCartanEvenExponent (κ : GroupClass.{u})
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ), Input κ T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        (A ⊔ H).pCoreIn 2 = ⊥ → Even n

/-- The higher-degree part of 5.1.6, with evenness explicit so its proof
can proceed independently of the nonnormal-Sylow argument. The module and
field-action conclusions must be established from the original Input. -/
def SourceCartanHigherFieldReduction (κ : GroupClass.{u})
    (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ), Input κ T L W n →
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      1 < ChapterE.generationParameter H →
      ∀ A B : Subgroup G, CartanPair T L H A B →
        (A ⊔ H).pCoreIn 2 = ⊥ → Even n → 4 < n →
          CartanHigherFieldReduction T H A n

/-- Evenness removes the odd small degree; the independent higher-degree
source argument supplies the remaining row. Both source proofs are explicit. -/
theorem sourceCartanFieldReduction_of_even_and_higher {κ : GroupClass.{u}}
    (heven : SourceCartanEvenExponent κ G)
    (hhigher : SourceCartanHigherFieldReduction κ G) :
    SourceCartanFieldReduction κ G := by
  intro T L W n h H hH hgen A B c hzero
  have he := heven T L W n h H hH hgen A B c hzero
  by_cases hlarge : 4 < n
  · exact Or.inr (Or.inr (hhigher T L W n h H hH hgen A B c hzero he hlarge))
  · have hn : n = 2 ∨ n = 4 := by
      obtain ⟨k, hk⟩ := he
      have := h.exponent
      omega
    exact hn.elim Or.inl (fun h4 => Or.inr (Or.inl h4))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
