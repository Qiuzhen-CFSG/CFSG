module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowBinaryTriality
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSmallGenerationTorus
public import Theory.SpecificGroups.PSL2.SmallDegreeSevenActors
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeTerminal

/-!
# The actual seven-subgroup at the binary triality endpoint

The right Borel formula and the original odd Hall condition identify
B ∩ R with the multiplicative group of the field of R/O₂(R). In the
binary triality branch this gives order seven, and oddness makes its
literal map into R/O₂(R) injective. Since B normalizes the cyclic left
Cartan, this subgroup centralizes the order-three or order-five actor.

At the original degrees n = 2, 4, or 8, the full automorphism group of
L/O₂(L) is seven-free. Thus B ∩ R acts trivially on that quotient; the
conclusion below records the commutators in the original embedded O₂(L).
Both facts are retained on the actual changed-Sylow witness, together
with the normal containing component and its literal quotient embedding.

This is a constraint on the remaining binary configuration, not an
exclusion or an identification of the two field degrees. The small-degree
source reduction, module argument, other component families and final
normalization remain with qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.1.10–11 and 5.2.2, printed pp.634–635,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The literal right Hall intersection is the torus of the marked linear
quotient. This uses the source Borel equality and introduces no Hall premise. -/
theorem LocalData.right_cartan_equiv_units
    {T : Sylow 2 G} {L H A B D R : Subgroup G} {m : ℕ}
    (d : LocalData T L H B D R) (c : CartanPair T L H A B)
    (hm : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ m)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ m ∧ Nonempty ((B ⊓ R : Subgroup G) ≃* Fˣ) := by
  obtain ⟨P,hP⟩ := d.right_sylow
  have hPlit : (P : Subgroup R) = (Global.sourceS L H ⊓ R).subgroupOf R := by
    apply map_injective R.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Global.sourceS L H ⊓ R ≤ R from inf_le_right)]
    exact hP
  have hN : (normalizer (P : Set R)).map R.subtype =
      ChapterF.Source.borel R (Global.sourceS L H) := by
    change (normalizer ((P : Subgroup R) : Set R)).map R.subtype = _
    rw [hPlit,←subgroupOf_normalizer_eq (show Global.sourceS L H ⊓ R ≤ R from inf_le_right),
      subgroupOf_map_subtype, inf_comm]
    rfl
  let C := (B ⊓ R).subgroupOf R
  have hCN : C ≤ normalizer (P : Set R) := by
    apply (map_le_map_iff_of_injective R.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le inf_le_right,hN,d.right_borel]
    exact le_sup_right
  have hgen : (P : Subgroup R) ⊔ C = normalizer (P : Set R) := by
    apply map_injective R.subtype_injective
    rw [Subgroup.map_sup,hP,map_subgroupOf_eq_of_le inf_le_right,hN,d.right_borel]
  have hBo : Odd (Nat.card B) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
    exact OddHall.odd_hall_odd c.right_hall
  have hCo : Odd (Nat.card C) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show B ⊓ R ≤ R from inf_le_right)).toEquiv]
    exact hBo.of_dvd_nat (card_dvd_of_le (show B ⊓ R ≤ B from inf_le_left))
  obtain ⟨k,hk⟩ := P.isPGroup'.exists_card_eq
  have hd : Disjoint (P : Subgroup R) C := disjoint_of_coprime_natCard (by
    rw [hk]
    exact (Nat.coprime_two_left.mpr hCo).pow_left k)
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e' := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let q := e'.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hq : Function.Surjective q := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = pCore 2 R := by
    ext x
    exact e'.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  obtain ⟨f⟩ := Matrix.SpecialLinearGroup.sylow_normalizer_complement_equiv_units
    q hq P (hker ▸ pCore_isPGroup.le_sylow_of_normal P) C hCN hd hgen
  exact ⟨F,inferInstance,inferInstance,inferInstance,hF,
    ⟨(subgroupOfEquivOfLe (show B ⊓ R ≤ R from inf_le_right)).symm.trans f⟩⟩

/-- The order of the original right Hall intersection, at the right field
parameter, follows from its actual unit-group equivalence. -/
theorem LocalData.right_cartan_card
    {T : Sylow 2 G} {L H A B D R : Subgroup G} {m : ℕ}
    (d : LocalData T L H B D R) (c : CartanPair T L H A B)
    (hm : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ m)) :
    Nat.card (B ⊓ R : Subgroup G) = 2 ^ m - 1 := by
  obtain ⟨F,_,_,_,hF,⟨e⟩⟩ := d.right_cartan_equiv_units c hm
  rw [Nat.card_congr e.toEquiv,Nat.card_units,hF]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- A subgroup of order seven in the original right Hall group centralizes
both possible prime actors, since their automorphism orders are two or four. -/
theorem CartanPair.seven_centralizes_prime_actor {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D E : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D) (hEB : E ≤ B) (hE : Nat.card E = 7) :
    E ≤ centralizer (D : Set G) := by
  have hp : p.Prime := by rcases hd.prime with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic D := isCyclic_of_prime_card hd.card
  have hED := hEB.trans (c.normalizes_prime_actor h hd)
  let f := D.normalizerMonoidHom.comp (inclusion hED)
  have hc : Nat.Coprime (Nat.card E) (Nat.card (MulAut D)) := by
    rw [hE,IsCyclic.card_mulAut,hd.card]
    rcases hd.prime with rfl | rfl <;> decide
  have hc1 : Nat.card f.range = 1 := Nat.eq_one_of_dvd_coprimes hc
    (card_range_dvd f) f.range.card_subgroup_dvd_card
  have hf : ∀ a : E, f a = 1 := fun a =>
    mem_bot.mp ((f.range.eq_bot_of_card_eq hc1) ▸ (show f a ∈ f.range from ⟨a,rfl⟩))
  intro a ha b hb
  have he := congrArg (fun z : MulAut D => (z (⟨b,hb⟩ : D) : G)) (hf ⟨a,ha⟩)
  change a * b * a⁻¹ = b at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- In the three source degrees the actual quotient action of an order-seven
right Hall subgroup is trivial. Commutators use the original inclusion of L. -/
theorem CartanPair.seven_left_commutators {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B E : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hn : n = 2 ∨ n = 4 ∨ n = 8) (hEB : E ≤ B) (hE : Nat.card E = 7) :
    ∀ a ∈ E, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ L.pCoreIn 2 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hEL : E ≤ normalizer (L : Set G) := hEB.trans (c.right_le.trans inf_le_left)
  let ρ := (quotientAut (pCore 2 L)).comp (L.normalizerMonoidHom.comp (inclusion hEL))
  let σ := (MulAut.congr e).toMonoidHom.comp ρ
  have hs : σ = 1 := Theory.PSL2.SmallDegreeSevenActors.action_eq_one hF hn hE σ
  have hr (a : E) : ρ a = 1 := by
    apply (MulAut.congr e).injective
    exact (DFunLike.congr_fun hs a).trans (map_one (MulAut.congr e)).symm
  intro a ha l hl
  have he := congrArg (fun z : MulAut (L ⧸ pCore 2 L) =>
    z (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)) (hr ⟨a,ha⟩)
  change quotientAut (pCore 2 L)
    (L.normalizerMonoidHom (inclusion hEL ⟨a,ha⟩))
    (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩) = QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩ at he
  rw [quotientAut_apply_mk] at he
  have hm := QuotientGroup.eq_iff_div_mem.mp he
  exact ⟨_,hm,by
    change a * l * a⁻¹ / l = _
    rw [div_eq_mul_inv]⟩


/-- The original right Hall intersection embeds in the literal right
component quotient: its odd order meets the two-core trivially. -/
theorem CartanPair.right_cartan_quotient_injective
    {T : Sylow 2 G} {L H A B R : Subgroup G}
    (c : CartanPair T L H A B) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 R)).comp
      (inclusion (show B ⊓ R ≤ R from inf_le_right))) := by
  have hBo : Odd (Nat.card B) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.right_le).toEquiv]
    exact OddHall.odd_hall_odd c.right_hall
  have hCo : Odd (Nat.card (B ⊓ R : Subgroup G)) :=
    hBo.of_dvd_nat (card_dvd_of_le (show B ⊓ R ≤ B from inf_le_left))
  obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 R).exists_card_eq
  have hd : Disjoint (B ⊓ R : Subgroup G) (R.pCoreIn 2) :=
    disjoint_of_coprime_natCard (by
      rw [hk]
      exact (Nat.coprime_two_right.mpr hCo).pow_right k)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  apply Subtype.ext
  exact hd.le_bot ⟨x.property,
    ⟨inclusion inf_le_right x, (QuotientGroup.eq_one_iff _).mp hx, rfl⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The remaining rank-two branch has an actual right Hall subgroup of order
seven. It centralizes D, survives in R/O₂(R), and is trivial on L/O₂(L)
at the original three small degrees. No equality of field degrees is used. -/
theorem LocalData.changedSylow_seven_actor
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
            B ⊓ R ≤ centralizer (D : Set G) ∧
            Function.Injective ((QuotientGroup.mk' (pCore 2 R)).comp
              (inclusion (show B ⊓ R ≤ R from inf_le_right))) ∧
            ∀ b ∈ B ⊓ R, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ L.pCoreIn 2)) ∨
        ∃ U : Sylow 2 G, (U : Subgroup G) = T₁) := by
  obtain ⟨P,hTP,hD,hcases⟩ := d.changedSylow_binary_configuration h hH c hd hz
  refine ⟨P,hTP,hD,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hm⟩ | ha
  · refine Or.inl ⟨he,K,hRK,hKX,hK,hKn,hlt,?_⟩
    intro hmodel
    obtain ⟨htrial,hr,hp⟩ := hm hmodel
    have hcard : Nat.card (B ⊓ R : Subgroup G) = 7 := by
      simpa using d.right_cartan_card (m := 3) c hr
    exact ⟨htrial,hr,hp,hcard,
      c.seven_centralizes_prime_actor h hd inf_le_left hcard,
      c.right_cartan_quotient_injective,
      c.seven_left_commutators h hn inf_le_left hcard⟩
  · exact Or.inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
