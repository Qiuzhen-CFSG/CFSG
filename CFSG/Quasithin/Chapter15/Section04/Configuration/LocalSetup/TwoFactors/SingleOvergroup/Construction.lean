module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Baumann
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.LocalSylow
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# The Goldschmidt construction for single-factor overgroups

For the raw preceding witnesses in Aschbacher–Smith 15.4.15, put
`Gᵢ = YᵢT`. The order-three quotient of `Yᵢ` makes `T` maximal in `Gᵢ`,
while `Yᵢ = [Yᵢ,J(T)]` excludes normality of `T`. The three-coset action
therefore gives the actual symmetric-three quotient over `O₂(Gᵢ)`.
Distinct unique maximal two-local overgroups force `G₁ ∩ G₂ = T` and
`O₂(⟨G₁,G₂⟩) = 1`. Characteristic two passes down the Sylow interval
from the two maximal overgroups, yielding the intrinsic `F*(Gᵢ) = O₂(Gᵢ)`.

The transport lemmas retain the actual `Ω₁(Z(T))`, its order, and its
noncentrality under subgroup restriction and actual overlap isomorphisms.
The raw hypotheses are exactly the consumed parts of 15.4.12 and condition
(E); the fixed-index input is the permitted conclusion of 15.4.14.
No definition of the source Y-family or classification alternative is
replaced here. The later F.6.5 case analysis remains to be assembled.

Source: *The Classification of Quasithin Groups*, combined 1 March 2004
manuscript, 15.4.12–15, printed pp.1160–1161.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
variable {G : Type*} [Group G] [Finite G]

private theorem index_sup_of_normal (A B : Subgroup G) [A.Normal] :
    B.relIndex (A ⊔ B) = B.relIndex A := by
  have he : A.relIndex B * B.relIndex (A ⊔ B) =
      A.relIndex B * B.relIndex A := by
    calc
      _ = (B ⊓ A).relIndex (A ⊔ B) := by
        rw [← inf_relIndex_left (H := B) (K := A)]
        exact relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
      _ = (B ⊓ A).relIndex A * A.relIndex (A ⊔ B) :=
        (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
      _ = _ := by simp [inf_relIndex_right, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero index_ne_zero_of_finite) he

/-- The single-factor witness gives the actual quotient by the two-core. -/
theorem single_factor_quotient (T : Sylow 2 G) (Y : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hi : (pCore 2 Y).index = 3)
    (hcomm : Y = ⁅Y, ChapterB.thompsonJ (T : Subgroup G) 0⁆) :
    (T : Subgroup G).relIndex (Y ⊔ (T : Subgroup G)) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  have hp : (pCore 2 Y).index.Prime := hi ▸ Nat.prime_three
  have hc : pCore 2 Y ≠ ⊤ := by
    intro he
    have h := (pCore 2 Y).index_eq_one.mpr he
    omega
  have hpar := minimalParabolic_join_of_quotient_irreducible T Y hn hc
    (quotient_irreducible_of_prime_core_index _ _ hp) hcomm
  let A := Y ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ A from le_sup_right)
  have hcoreT : Y.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hnorm : A ≤ normalizer (Y.pCoreIn 2 : Set G) :=
      (sup_le Y.le_normalizer hn).trans
        (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
    have hcore := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Y)
      ((pCoreIn_le 2 Y).trans le_sup_left) hnorm
    exact hcore.trans (by
      simpa only [P, A, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
        using pCoreIn_le_sylow A P)
  have hle : pCore 2 Y ≤ (T : Subgroup G).subgroupOf Y := by
    intro y hy
    exact hcoreT (mem_map.mpr ⟨y,hy,rfl⟩)
  have hindex : (P : Subgroup A).index = (T : Subgroup G).relIndex Y := by
    let Y' := Y.subgroupOf A
    let T' := (T : Subgroup G).subgroupOf A
    let : Y'.Normal := normal_subgroupOf_of_le_normalizer (sup_le Y.le_normalizer hn)
    have hsup : Y' ⊔ T' = ⊤ := by
      rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
    calc
      _ = T'.relIndex (Y' ⊔ T') := by rw [hsup, relIndex_top_right]; rfl
      _ = T'.relIndex Y' := index_sup_of_normal Y' T'
      _ = _ := relIndex_subgroupOf le_sup_left
  have hd : (P : Subgroup A).index ∣ 3 := by
    rw [hindex, ← hi]
    exact index_dvd_of_le hle
  have hthree : (P : Subgroup A).index = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · have ht : A ≤ (T : Subgroup G) := (relIndex_eq_one.mp h)
      exact (hpar.1.1.not_ge ht).elim
    · exact h
  have hproper : pCore 2 A < (P : Subgroup A) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P) ?_
    intro he
    have hnP : (P : Subgroup A).Normal := he ▸ inferInstance
    have hnT : A ≤ normalizer (T : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (show (T : Subgroup G) ≤ A from le_sup_right)).mp hnP
    exact hpar.2 hnT
  exact ⟨hthree, sylow_index_three_core_quotient P hthree hproper⟩

omit [Finite G] in
/-- The intersection equality is forced by the genuine unique overgroups. -/
theorem intersection_eq_sylow (T : Sylow 2 G) {Y₁ Y₂ M₁ M₂ : Subgroup G}
    (hn₁ : (T : Subgroup G) ≤ normalizer (Y₁ : Set G))
    (hi₁ : (pCore 2 Y₁).index = 3)
    (hu₁ : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₁ ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (hM₂ : IsMaximalTwoLocal M₂) (hY₂M₂ : Y₂ ≤ M₂)
    (hTM₂ : (T : Subgroup G) ≤ M₂) (hne : M₁ ≠ M₂) :
    (Y₁ ⊔ (T : Subgroup G)) ⊓ (Y₂ ⊔ (T : Subgroup G)) = (T : Subgroup G) := by
  have hp : (pCore 2 Y₁).index.Prime := hi₁ ▸ Nat.prime_three
  have hc : pCore 2 Y₁ ≠ ⊤ := by
    intro he
    have h := (pCore 2 Y₁).index_eq_one.mpr he
    omega
  have hcov := sylow_covBy_join_of_quotient_irreducible T Y₁ hn₁ hc
    (quotient_irreducible_of_prime_core_index _ _ hp)
  have hT := le_inf (le_sup_right : (T : Subgroup G) ≤ Y₁ ⊔ (T : Subgroup G))
    (le_sup_right : (T : Subgroup G) ≤ Y₂ ⊔ (T : Subgroup G))
  rcases hcov.eq_or_eq hT inf_le_left with h | h
  · exact h
  · have hle : Y₁ ⊔ (T : Subgroup G) ≤ M₂ :=
      h.symm.le.trans (inf_le_right.trans (sup_le hY₂M₂ hTM₂))
    exact (hne (hu₁ M₂ hM₂ hle).symm).elim

omit [Finite G] in
/-- Characteristic two descends through a Sylow interval. -/
theorem characteristic_two_of_sylow_interval (T : Sylow 2 G)
    {A M : Subgroup G} (hTA : (T : Subgroup G) ≤ A) (hAM : A ≤ M)
    (hM : HasCharacteristicTwo M) : HasCharacteristicTwo A := by
  apply Chapter1.mem_He_iff.mp
  have hM' := Chapter1.mem_He_iff.mpr hM
  have hcore := Chapter3.twoCore_le_of_sylow_le T hTA hAM
  intro x hx
  exact hcore (hM' ⟨hAM hx.1, (centralizer_le hcore) hx.2⟩)

omit [Finite G] in
/-- The original omega-center is also the local omega-center after restricting T. -/
theorem omega_center_subgroupOf {T A : Subgroup G} (hTA : T ≤ A) :
    Stellmacher.omegaOneCenterAmbient (T.subgroupOf A) =
      (Stellmacher.omegaOneCenterAmbient T).subgroupOf A := by
  have hm := Stellmacher.omegaOneCenterAmbient_map_injective A.subtype A.subtype_injective
    (T.subgroupOf A)
  rw [map_subgroupOf_eq_of_le hTA] at hm
  rw [hm]
  exact (comap_map_eq_self_of_injective A.subtype_injective _).symm

omit [Finite G] in
/-- A relative-index-two fixed subgroup excludes centrality in the generator. -/
theorem omega_center_not_central (T : Sylow 2 G) (Y : Subgroup G)
    (hi : (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (Y : Set G)).relIndex (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    ¬ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
      centralizer ((Y ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
  intro hc
  have hle := hc.trans (centralizer_le (le_sup_left : Y ≤ Y ⊔ (T : Subgroup G)))
  rw [inf_eq_left.mpr hle, relIndex_self] at hi
  omega
/-- Construct the source Goldschmidt triple, its trivial ambient two-core,
and characteristic two in both generators from the raw single-factor witnesses. -/
theorem single_factor_goldschmidt (T : Sylow 2 G)
    {Y₁ Y₂ M₁ M₂ : Subgroup G}
    (hEven : IsEvenCharacteristicAt T)
    (hM₁ : IsMaximalTwoLocal M₁) (hM₂ : IsMaximalTwoLocal M₂)
    (hTM₁ : (T : Subgroup G) ≤ M₁) (hTM₂ : (T : Subgroup G) ≤ M₂)
    (hY₁M₁ : Y₁ ≤ M₁) (hY₂M₂ : Y₂ ≤ M₂)
    (hn₁ : M₁ ≤ normalizer (Y₁ : Set G)) (hn₂ : M₂ ≤ normalizer (Y₂ : Set G))
    (hi₁ : (pCore 2 Y₁).index = 3) (hi₂ : (pCore 2 Y₂).index = 3)
    (hc₁ : Y₁ = ⁅Y₁, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hc₂ : Y₂ = ⁅Y₂, ChapterB.thompsonJ (T : Subgroup G) 0⁆)
    (hu₁ : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₁ ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (hu₂ : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₂ ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂) :
    let G₁ := Y₁ ⊔ (T : Subgroup G)
    let G₂ := Y₂ ⊔ (T : Subgroup G)
    let I := G₁ ⊔ G₂
    G₁ ⊓ G₂ = (T : Subgroup G) ∧
      ChapterF.IsGoldschmidtTriple (G₁.subgroupOf I) (G₂.subgroupOf I) ∧
      pCore 2 I = ⊥ ∧
      Theory.GroupTheory.generalizedFitting (G₁.subgroupOf I) = pCore 2 (G₁.subgroupOf I) ∧
      Theory.GroupTheory.generalizedFitting (G₂.subgroupOf I) = pCore 2 (G₂.subgroupOf I) := by
  dsimp only
  let G₁ := Y₁ ⊔ (T : Subgroup G)
  let G₂ := Y₂ ⊔ (T : Subgroup G)
  let I := G₁ ⊔ G₂
  have hT₁ := hTM₁.trans hn₁
  have hT₂ := hTM₂.trans hn₂
  have hint := intersection_eq_sylow T hT₁ hi₁ hu₁ hM₂ hY₂M₂ hTM₂ hne
  have hquot₁ := (single_factor_quotient T Y₁ hT₁ hi₁ hc₁).2
  have hquot₂ := (single_factor_quotient T Y₂ hT₂ hi₂ hc₂).2
  let P := T.subtype (show (T : Subgroup G) ≤ I from le_sup_right.trans le_sup_left)
  have hP : (P : Subgroup I).map I.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (le_sup_right.trans le_sup_left)
  have hchar₁ := characteristic_two_of_sylow_interval T le_sup_right
    (sup_le hY₁M₁ hTM₁) (hEven M₁ hM₁ hTM₁)
  have hchar₂ := characteristic_two_of_sylow_interval T le_sup_right
    (sup_le hY₂M₂ hTM₂) (hEven M₂ hM₂ hTM₂)
  have he₁ := hchar₁.of_equiv (subgroupOfEquivOfLe (show G₁ ≤ I from le_sup_left)).symm
  have he₂ := hchar₂.of_equiv (subgroupOfEquivOfLe (show G₂ ≤ I from le_sup_right)).symm
  exact ⟨hint, goldschmidt_triple_in_join G₁ G₂ (T : Subgroup G) hquot₁ hquot₂ P hP hint,
    twoCore_join_eq_bot_of_distinct_unique hu₁ hu₂ hne,
    generalizedFitting_eq_twoCore_of_mem_He (Chapter1.mem_He_iff.mpr he₁),
    generalizedFitting_eq_twoCore_of_mem_He (Chapter1.mem_He_iff.mpr he₂)⟩

omit [Finite G] in
/-- The order of the marked omega-center is unchanged in a local subgroup. -/
theorem omega_center_card_subgroupOf {T A : Subgroup G} (hTA : T ≤ A) :
    Nat.card (Stellmacher.omegaOneCenterAmbient (T.subgroupOf A)) =
      Nat.card (Stellmacher.omegaOneCenterAmbient T) := by
  have hm := Stellmacher.omegaOneCenterAmbient_map_injective A.subtype A.subtype_injective
    (T.subgroupOf A)
  rw [map_subgroupOf_eq_of_le hTA] at hm
  rw [hm]
  exact Nat.card_congr ((Stellmacher.omegaOneCenterAmbient (T.subgroupOf A)).equivMapOfInjective
    A.subtype A.subtype_injective).toEquiv

omit [Finite G] in
/-- Noncentrality transfers with the actual common Sylow subgroup. -/
theorem omega_center_not_central_subgroupOf {T A B : Subgroup G}
    (hTA : T ≤ A) (hBA : B ≤ A)
    (hn : ¬ Stellmacher.omegaOneCenterAmbient T ≤ centralizer (B : Set G)) :
    ¬ Stellmacher.omegaOneCenterAmbient (T.subgroupOf A) ≤
      centralizer (B.subgroupOf A : Set A) := by
  intro hc
  apply hn
  intro z hz
  have hzA : z ∈ A := hTA ((Stellmacher.mem_omegaOneCenterAmbient_iff T z).mp hz).1
  have hz' : (⟨z,hzA⟩ : A) ∈ Stellmacher.omegaOneCenterAmbient (T.subgroupOf A) := by
    rw [omega_center_subgroupOf hTA]
    exact hz
  apply mem_centralizer_iff.mpr
  intro b hb
  exact congrArg Subtype.val (mem_centralizer_iff.mp (hc hz') (⟨b,hBA hb⟩ : A) hb)

omit [Finite G] in
/-- An actual isomorphism of overlap groups preserves their omega-center orders. -/
theorem omega_center_card_eq_of_equiv {H : Type*} [Group H]
    (T : Subgroup G) (S : Subgroup H) (e : T ≃* S) :
    Nat.card (Stellmacher.omegaOneCenterAmbient T) =
      Nat.card (Stellmacher.omegaOneCenterAmbient S) := by
  have hT := omega_center_card_subgroupOf (T := T) (A := T) le_rfl
  have hS := omega_center_card_subgroupOf (T := S) (A := S) le_rfl
  rw [subgroupOf_self] at hT hS
  rw [← hT, ← hS]
  have hm := Stellmacher.omegaOneCenterAmbient_map_injective e.toMonoidHom e.injective ⊤
  rw [map_top_of_surjective _ e.surjective] at hm
  rw [hm]
  exact Nat.card_congr ((Stellmacher.omegaOneCenterAmbient (⊤ : Subgroup T)).equivMapOfInjective
    e.toMonoidHom e.injective).toEquiv

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SingleOvergroup
