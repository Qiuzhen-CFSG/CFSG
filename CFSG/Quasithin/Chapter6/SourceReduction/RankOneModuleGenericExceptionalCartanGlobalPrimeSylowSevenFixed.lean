module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSeven
public import Theory.GroupAction.PrimeFixedQuotient
public import Theory.GroupTheory.ConjugateSpanCentralizerLift

/-!
# Fixed lifts and the original omega-module at the seven-actor endpoint

For E ≤ B of order seven and original field degree n = 2, 4, or 8,
the established trivial action on L/O₂(L) lifts fixed representatives:
its fibers have two-power order. Thus C_L(E) covers that exact quotient,
and C_L(E)/O₂(C_L(E)) is identified with it by the inclusion map.

The original O₂(L) centralizes the L-span of Ω₁(Z(T)). Consequently the
same span is generated under C_L(E), and E fixes this span exactly when
it fixes Ω₁(Z(T)). This supplies the quotient-to-module implication in
the source's faithfulness argument without assuming abelianness of O₂(L),
a representation model, or equality of the two field parameters.

The final application retains these statements on the original changed
Sylow and literal E = B ∩ R. It does not assert that E fixes Ω₁(Z(T)),
or exclude binary triality. Those geometry and movement statements,
source selection, higher-field reduction, other component families and
final normalization remain with qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.2.2, printed pp.648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The seven-centralizer covers the original left quotient, through its actual inclusion. -/
theorem CartanPair.seven_centralizer_covers_left {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B E : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hn : n = 2 ∨ n = 4 ∨ n = 8) (hEB : E ≤ B) (hE : Nat.card E = 7) :
    Function.Surjective ((QuotientGroup.mk' (pCore 2 L)).comp
      (inclusion (show L ⊓ centralizer (E : Set G) ≤ L from inf_le_left))) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hEp : IsPGroup 7 E := IsPGroup.of_card (n := 1) (by simpa using hE)
  have hcop : ¬ 7 ∣ Nat.card (pCore 2 L) := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    rw [hk]
    exact fun hd => (by decide : ¬ 7 ∣ 2) ((by decide : Nat.Prime 7).dvd_of_dvd_pow hd)
  exact centralizer_quotient_surjective_of_prime_fixed L E (pCore 2 L) hEp
    (hEB.trans (c.right_le.trans inf_le_left)) hcop
    (c.seven_left_commutators h hn hEB hE)

/-- Removing the centralizer's own two-core gives the original left quotient,
with the equivalence induced by inclusion rather than an abstract family tag. -/
theorem CartanPair.seven_centralizer_quotient {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B E : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hn : n = 2 ∨ n = 4 ∨ n = 8) (hEB : E ≤ B) (hE : Nat.card E = 7) :
    let C := L ⊓ centralizer (E : Set G)
    ∃ e : (C ⧸ pCore 2 C) ≃* (L ⧸ pCore 2 L),
      ∀ x : C, e (QuotientGroup.mk' (pCore 2 C) x) =
        QuotientGroup.mk' (pCore 2 L) (inclusion inf_le_left x) := by
  let C := L ⊓ centralizer (E : Set G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let f := q.comp (inclusion (show C ≤ L from inf_le_left))
  have hf : Function.Surjective f := c.seven_centralizer_covers_left h hn hEB hE
  have hk : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective inf_le_left)
  have hqk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hcore := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hqk
  have hker : f.ker = pCore 2 C := by
    dsimp only [f]
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk',← hcore,comap_comap]
    exact f.comap_pCore_of_ker_isPGroup hf hk
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf),fun _ => rfl⟩

/-- The embedded left two-core fixes the full original omega-generated module. -/
theorem Input.core_centralizes_omega_span {κ : GroupClass}
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ} (h : Input κ T L W n) :
    L.pCoreIn 2 ≤ centralizer
      (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G) := by
  let Q := L.pCoreIn 2
  have hLN : L ≤ normalizer (Q : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hJN : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (sup_le L.le_normalizer h.sylow_normalizes).trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hQT : Q ≤ (T : Subgroup G) := by
    have hc := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      ((pCoreIn_le 2 L).trans (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)) hJN
    exact hc.trans ((pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right))
  apply le_centralizer_iff.mp
  exact conjugateSpanBy_le
    (le_centralizer_iff.mp (hQT.trans sylow_le_omegaCentralizer))
    (hLN.trans (normalizer_le_normalizer_centralizer Q))

/-- Every L-conjugate of the original omega-center is already a conjugate
under the literal seven-centralizer. -/
theorem CartanPair.seven_omega_span_eq {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B E : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hn : n = 2 ∨ n = 4 ∨ n = 8) (hEB : E ≤ B) (hE : Nat.card E = 7) :
    conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L =
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
        (L ⊓ centralizer (E : Set G)) := by
  apply conjugateSpanBy_eq_of_quotient_surjective _ L _ (pCore 2 L) inf_le_left
    (c.seven_centralizer_covers_left h hn hEB hE)
  exact h.core_centralizes_omega_span.trans (centralizer_le (le_conjugateSpanBy _ _))

/-- For the actual seven-actor, fixing the source omega-center is equivalent
to fixing its whole L-generated module. No representation model is assumed. -/
theorem CartanPair.seven_centralizes_omega_span_iff {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B E : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hn : n = 2 ∨ n = 4 ∨ n = 8) (hEB : E ≤ B) (hE : Nat.card E = 7) :
    E ≤ centralizer
      (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G) ↔
      E ≤ omegaCentralizer T := by
  constructor
  · exact fun he => he.trans (centralizer_le (le_conjugateSpanBy _ _))
  · intro he
    rw [c.seven_omega_span_eq h hn hEB hE]
    apply le_centralizer_iff.mp
    exact conjugateSpanBy_le (le_centralizer_iff.mp he)
      (inf_le_right.trans (centralizer (E : Set G)).le_normalizer)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- On the actual changed Sylow, the surviving rank-two branch gives a
quotient-covering seven-centralizer and generates the original omega-module
from that centralizer. All maps refer to the original L and B ∩ R. -/
theorem LocalData.changedSylow_seven_fixed_lifts
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hn : n = 2 ∨ n = 4 ∨ n = 8)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    ∃ P : Sylow 2 (extension T L H B D R),
      let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
      normalizingSylow T R ≤ T₁ ∧
      T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
      ((T₁ = normalizingSylow T R ∧
        let X := generated L H D R ⊔ normalizingSylow T R
        let q := QuotientGroup.mk' (pCore 2 X)
        ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
          (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
          (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
          (Chapter1.Section02.LocalModels.RankTwoTheoremC (K ⧸ pCore 2 K) →
            Triality.Standard.IsTrialityGroupAt 2 (K ⧸ pCore 2 K) ∧
            ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧ p = 3 ∧
            Nat.card (B ⊓ R : Subgroup G) = 7 ∧
            let E := B ⊓ R
            let C := L ⊓ centralizer (E : Set G)
            ∃ e : (C ⧸ pCore 2 C) ≃* (L ⧸ pCore 2 L),
              (∀ x : C, e (QuotientGroup.mk' (pCore 2 C) x) =
                QuotientGroup.mk' (pCore 2 L) (inclusion inf_le_left x)) ∧
              conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L =
                conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) C ∧
              (E ≤ centralizer
                (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G) ↔
                E ≤ omegaCentralizer T))) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  obtain ⟨P,hTP,hD,hcases⟩ := d.changedSylow_binary_configuration h hH c hd hz
  refine ⟨P,hTP,hD,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hm⟩ | ha
  · refine Or.inl ⟨he,K,hRK,hKX,hK,hKn,hlt,?_⟩
    intro hmodel
    obtain ⟨htrial,hr,hp⟩ := hm hmodel
    have hcard : Nat.card (B ⊓ R : Subgroup G) = 7 := by
      simpa using d.right_cartan_card (m := 3) c hr
    obtain ⟨e,he⟩ := c.seven_centralizer_quotient h hn inf_le_left hcard
    exact ⟨htrial,hr,hp,hcard,e,he,
      c.seven_omega_span_eq h hn inf_le_left hcard,
      c.seven_centralizes_omega_span_iff h hn inf_le_left hcard⟩
  · exact Or.inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
