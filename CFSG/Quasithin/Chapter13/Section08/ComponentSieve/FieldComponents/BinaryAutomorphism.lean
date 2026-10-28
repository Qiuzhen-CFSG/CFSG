module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The binary three-dimensional automorphism clause of 13.8.21

Once H=KT, the actual quotient H*=H/O₂(H) has a normal simple K* with
2-group quotient. Its centralizer vanishes. Conjugation embeds H* into
Aut(L₃(2)), whose order is twice |L₃(2)|. The earlier exclusion H*≄L₃(2)
therefore makes this embedding surjective. The result retains the prescribed
identification of K* and the literal conjugation action.

Source: Aschbacher–Smith, 13.8.21(3), printed p.957, using 13.8.19.
The exclusion in 13.8.19 remains an explicit earlier input.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

omit [Finite G] in
/-- H=KT gives the actual two-group quotient H*/K*, without a splitting
or disjointness hypothesis on the Sylow supplement. -/
theorem star_quotient_isTwoGroup_of_supplement
    (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hH : H = K ⊔ T) (hT : IsPGroup 2 T) :
    IsPGroup 2 (Source.Hstar H ⧸ Source.starImage H K) := by
  have hKH : K ≤ H := by rw [hH]; exact le_sup_left
  have hTH : T ≤ H := by rw [hH]; exact le_sup_right
  have hs : Source.starImage H K ⊔ Source.starImage H T = ⊤ := by
    unfold Source.starImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup hKH hTH, ← hH, subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact isPGroup_quotient_of_sup_eq_top _ _ (hT.comap_subtype.map _) hs

/-- The isomorphism in 13.8.21(3) is induced by conjugation on the
actual K*. It is conditional only on H=KT and the earlier whole-quotient
exclusion; it does not exclude K*≅L₃(2). -/
theorem binary_automorphism_of_supplement
    (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hH : H = K ⊔ T) (hT : IsPGroup 2 T)
    (eK : Source.starImage H K ≃* Matrix.PSL3Two.PSL)
    (hnot : ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL)) :
    ∃ e : Source.Hstar H ≃* MulAut Matrix.PSL3Two.PSL,
      ∀ h, e h = MulAut.congr eK (MulAut.conjNormal h) := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup (Source.starImage H K) := eK.isSimpleGroup
  have hkcard : Nat.card (Source.starImage H K) = 168 :=
    (Nat.card_congr eK.toEquiv).trans Matrix.PSL3Two.card_PSL
  have ha : ¬ IsMulCommutative (Source.starImage H K) := by
    intro hc
    have hz := Nat.card_congr (centerCongr eK).toEquiv
    rw [center_eq_top_iff.mpr hc, Nat.card_congr (Subgroup.topEquiv (G := Source.starImage H K)).toEquiv,
      Matrix.PSL3Two.Automorphisms.center_psl_eq_bot, card_bot, hkcard] at hz
    omega
  have hC := centralizer_eq_bot_of_simple_two_quotient (Source.starImage H K) ha
    (star_quotient_isTwoGroup_of_supplement H K T hH hT)
    (pCore_quotient_pCore_eq_bot 2)
  let f : Source.Hstar H →* MulAut Matrix.PSL3Two.PSL :=
    (MulAut.congr eK).toMonoidHom.comp MulAut.conjNormal
  have hf : Function.Injective f := (MulAut.congr eK).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot _ hC)
  have hmul := (Source.starImage H K).card_mul_index
  rw [hkcard] at hmul
  have hdvd : Nat.card (Source.Hstar H) ∣ 336 := by
    rw [← Matrix.PSL3Two.Automorphisms.card_aut]
    exact card_dvd_of_injective f hf
  have hi : (Source.starImage H K).index ∣ 2 := by
    rw [← hmul] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 168) hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
  · have htop : Source.starImage H K = ⊤ := index_eq_one.mp hi
    exact (hnot ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop).symm.trans eK)⟩).elim
  · have hcard : Nat.card (Source.Hstar H) = Nat.card (MulAut Matrix.PSL3Two.PSL) := by
      rw [Matrix.PSL3Two.Automorphisms.card_aut, ← hmul, hi]
    exact ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩),
      fun _ => rfl⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents
