module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.LocalNormality

/-!
# Identifying radicals in maximal normal overgroups

A member X of Ξ*_rad may be defined using a different component from the
maximal component L in which it is normal. We identify X with Ξ_p(L), rather
than identifying those two components.

Relative normality identifies the kernel of X → L/O₂(L) with O₂(X). Its
image is a normal p-group of exponent p, hence lies in Ω₁(O_p(L/O₂(L))).
Two-perfectness then gives X ≤ Ξ_p(L). Nested normal members of Ξ are equal:
the smaller one's noncyclic odd quotient cannot lie in the cyclic Frattini
subgroup of the larger one's odd quotient. Irreducibility, Frattini
nongeneration and two-perfectness finish the equality. Characteristicity
now follows from the construction of Ξ_p(L).

The full A.3.6 common conclusion excludes a quasisimple quotient of L,
since p > 3 divides its Fitting subgroup. Uniform radical irreducibility
and X ∈ Ξ are explicit inputs from Lemma 1.3.3; its assembly owner must
discharge them. The argument works for any T satisfying these local inputs,
in particular the Sylow two-subgroup in the genuine Chapter 1 setup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6,
printed pp.43–45; 1.2.1(4), p.504; and the definition of Ξ*_rad and the
beginning of the proof of Proposition 1.3.8, p.512.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter1.RadicalIdentification
variable {G : Type*} [Group G]

private def normalQuotientMap {X L : Subgroup G} (hXL : X ≤ L) : X →* XiQuotient L :=
  (QuotientGroup.mk' (pCore 2 L)).comp (inclusion hXL)

/-- Both directions use the actual restricted kernel; normality supplies
O₂(X) ≤ O₂(L), and the reverse inclusion follows from the two-group kernel. -/
private theorem normalQuotientMap_ker {X L : Subgroup G} (hXL : X ≤ L)
    (hN : (X.subgroupOf L).Normal) : (normalQuotientMap hXL).ker = pCore 2 X := by
  have hker : IsPGroup 2 (normalQuotientMap hXL).ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hXL)).ker)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hXL)
  refine le_antisymm ?_ ?_
  · exact le_sSup ⟨inferInstance, hker⟩
  have hcore := pCoreIn_mono_of_normalizes (p := 2) hXL
    ((normal_subgroupOf_iff_le_normalizer hXL).mp hN)
  intro x hx
  have hmem := hcore (mem_map_of_mem X.subtype hx)
  obtain ⟨y, hy, he⟩ := hmem
  have he' : inclusion hXL x = y := Subtype.ext he.symm
  change QuotientGroup.mk' (pCore 2 L) (inclusion hXL x) = 1
  exact (QuotientGroup.eq_one_iff _).mpr (he' ▸ hy)

private noncomputable def normalQuotientEquiv {X L : Subgroup G} (hXL : X ≤ L)
    (hN : (X.subgroupOf L).Normal) : XiQuotient X ≃* (normalQuotientMap hXL).range :=
  (QuotientGroup.quotientMulEquivOfEq (normalQuotientMap_ker hXL hN).symm).trans
    (QuotientGroup.quotientKerEquivRange (normalQuotientMap hXL))

private theorem normalQuotientMap_range {X L : Subgroup G} (hXL : X ≤ L) :
    (normalQuotientMap hXL).range =
      (X.subgroupOf L).map (QuotientGroup.mk' (pCore 2 L)) := by
  rw [normalQuotientMap, MonoidHom.range_comp, inclusion_range]

private theorem odd_frattini_cyclic {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] (hQ : XiOddQuotient p Q) : IsCyclic (frattini Q) := by
  rcases hQ with ⟨hE, _⟩ | ⟨hE, _, _⟩
  · let := hE
    let : Fact (IsPGroup p Q) := ⟨IsElementaryAbelian.isPGroup p Q⟩
    rw [frattini_eq_bot_of_isElementaryAbelian (R := Q) (p := p)]
    infer_instance
  · let := hE.quotient_elementary_abelian
    let : Fact (IsPGroup p (Q ⧸ center Q)) := ⟨IsElementaryAbelian.isPGroup p _⟩
    have hphi : frattini Q ≤ center Q := by
      have h := frattini_le_comap_frattini_of_surjective
        (QuotientGroup.mk'_surjective (center Q))
      rw [frattini_eq_bot_of_isElementaryAbelian (R := Q ⧸ center Q) (p := p),
        MonoidHom.comap_bot, QuotientGroup.ker_mk'] at h
      exact h
    let : IsCyclic (center Q) := isCyclic_of_prime_card hE.center_order_p
    exact isCyclic_of_injective (inclusion hphi) (inclusion_injective hphi)

/-- Two members of Ξ coincide whenever one is a normal subgroup of the other.
Normality is relative to the larger member. The two odd primes need not be
identified before applying irreducibility. -/
public theorem eq_of_normal_le [Finite G] {T X Y : Subgroup G} (hX : XiMember T X)
    (hY : XiMember T Y) (hXY : X ≤ Y) (hN : (X.subgroupOf Y).Normal) : X = Y := by
  let f := normalQuotientMap hXY
  let q := QuotientGroup.mk' (frattini (XiQuotient Y))
  let A := f.range.map q
  have hA : ∀ t : T, ∀ a ∈ A, xiFrattiniAction T Y hY.invariant t a ∈ A := by
    rintro t a ⟨b, ⟨x, rfl⟩, rfl⟩
    let z : X := ⟨(t : G) * x * (t : G)⁻¹,
      (mem_normalizer_iff.mp (hX.invariant t.property) x).mp x.property⟩
    refine ⟨f z, ⟨z, rfl⟩, ?_⟩
    simp only [q, f, normalQuotientMap, xiFrattiniAction, MonoidHom.comp_apply,
      quotientAut_apply_mk]
    rfl
  have htop : A = ⊤ := by
    rcases hY.irreducible A hA with hb | ht
    · have hle : f.range ≤ frattini (XiQuotient Y) := by
        intro x hx
        have hh : q x = 1 := mem_bot.mp (hb ▸ mem_map_of_mem q hx)
        exact (QuotientGroup.eq_one_iff _).mp hh
      obtain ⟨p, hp, _, hqY⟩ := hY.odd_quotient
      let : Fact p.Prime := ⟨hp⟩
      let := odd_frattini_cyclic hqY
      let : IsCyclic f.range := isCyclic_of_injective (inclusion hle) (inclusion_injective hle)
      obtain ⟨r, hr, _, hqX⟩ := hX.odd_quotient
      let : Fact r.Prime := ⟨hr⟩
      exact (hqX.not_isCyclic (isCyclic_of_injective
        (normalQuotientEquiv hXY hN).toMonoidHom (normalQuotientEquiv hXY hN).injective)).elim
    · exact ht
  have hfrange : f.range = ⊤ := by
    apply frattini_nongenerating
    have hh := congrArg (Subgroup.comap q) htop
    simpa only [A, comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  have hgen : X.subgroupOf Y ⊔ pCore 2 Y = ⊤ := by
    rw [normalQuotientMap_range] at hfrange
    have hh := congrArg (Subgroup.comap (QuotientGroup.mk' (pCore 2 Y))) hfrange
    simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using hh
  let := hN
  have htwo : IsPGroup 2 (Y ⧸ X.subgroupOf Y) :=
    isPGroup_quotient_of_sup_eq_top _ _ pCore_isPGroup hgen
  have ht : X.subgroupOf Y = ⊤ := hY.perfect _ hN htwo
  exact le_antisymm hXY (subgroupOf_eq_top.mp ht)

private theorem odd_pow {Q : Type*} [Group Q] {p : ℕ} (hQ : XiOddQuotient p Q)
    (x : Q) : x ^ p = 1 := by
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mp _ x
  rcases hQ with ⟨he, _⟩ | ⟨_, _, he⟩
  · exact he.exponent_dvd_p
  · exact he ▸ dvd_rfl

private theorem normalQuotient_le_core {X L : Subgroup G} (hXL : X ≤ L)
    (hN : (X.subgroupOf L).Normal) {p : ℕ} [Fact p.Prime]
    (hX : XiOddQuotient p (XiQuotient X)) :
    (normalQuotientMap hXL).range ≤ pCore p (XiQuotient L) := by
  have hn : (normalQuotientMap hXL).range.Normal := by
    rw [normalQuotientMap_range]
    exact hN.map _ (QuotientGroup.mk'_surjective _)
  exact le_sSup ⟨hn, hX.isPGroup.of_equiv (normalQuotientEquiv hXL hN)⟩

/-- Exponent p places the image in the omega layer, even when the p-core
is homocyclic of higher exponent. -/
private theorem normalQuotient_le_omega {X L : Subgroup G} (hXL : X ≤ L)
    (hN : (X.subgroupOf L).Normal) {p : ℕ} [Fact p.Prime]
    (hX : XiOddQuotient p (XiQuotient X)) :
    (normalQuotientMap hXL).range ≤ xiOmegaCore p L := by
  have hle := normalQuotient_le_core hXL hN hX
  have hshape := hX.of_mulEquiv (normalQuotientEquiv hXL hN)
  intro x hx
  refine ⟨⟨x, hle hx⟩, subset_closure ?_, rfl⟩
  change (⟨x, hle hx⟩ : pCore p (XiQuotient L)) ^ (p ^ 1) = 1
  apply Subtype.ext
  simpa only [coe_pow, coe_one, pow_one] using
    congrArg Subtype.val (odd_pow hshape ⟨x, hx⟩)

private theorem le_XiP_of_normal [Finite G] {T X L : Subgroup G} (hX : XiMember T X)
    (hXL : X ≤ L) (hN : (X.subgroupOf L).Normal)
    {p : ℕ} [Fact p.Prime] (hq : XiOddQuotient p (XiQuotient X)) : X ≤ XiP p L := by
  have hpre : X ≤ (xiPPreimage p L).map L.subtype := by
    intro x hx
    refine ⟨inclusion hXL ⟨x, hx⟩, ?_, rfl⟩
    exact normalQuotient_le_omega hXL hN hq ⟨⟨x, hx⟩, rfl⟩
  have hr := embedded_pResidual_mono 2 hpre
  rw [(pResidual_eq_top_iff 2 X).mpr hX.perfect,
    ← MonoidHom.range_eq_map, range_subtype, ← map_embedded_pResidual] at hr
  exact hr

private theorem fitting_prime_of_normal [Finite G] {X L : Subgroup G} (hXL : X ≤ L)
    (hN : (X.subgroupOf L).Normal) {p : ℕ} [Fact p.Prime]
    (hX : XiOddQuotient p (XiQuotient X)) :
    p ∣ Nat.card (fittingSubgroup (XiQuotient L)) := by
  have hd : p ∣ Nat.card (normalQuotientMap hXL).range := by
    rw [← Nat.card_congr (normalQuotientEquiv hXL hN).toEquiv]
    rcases hX with ⟨_, he⟩ | ⟨_, he, _⟩
    · rw [he]; exact dvd_pow_self p (by decide)
    · rw [he]; exact dvd_pow_self p (by decide)
  exact hd.trans (card_dvd_of_le
    ((normalQuotient_le_core hXL hN hX).trans (pCore_le_fitting _ p)))

private theorem not_quasisimple_of_fitting_eq {K : Type*} [Group K] [Finite K]
    (h : generalizedFitting K = fittingSubgroup K) : ¬ IsQuasisimple K := by
  intro hK
  let := hK
  have htop : (⊤ : Subgroup K) ≤ generalizedFitting K :=
    component_le_generalizedFitting K ⊤
      ⟨(inferInstance : (⊤ : Subgroup K).Normal).isSubnormal,
        IsQuasisimple.of_mulEquiv topEquiv.symm⟩
  have hfit : fittingSubgroup K = ⊤ := top_unique (h ▸ htop)
  let : Group.IsNilpotent K := Group.nilpotent_of_mulEquiv
    ((MulEquiv.subgroupCongr hfit).trans topEquiv)
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (center K))
  exact Group.IsPerfect.not_isSolvable K inferInstance

/-- In the quasisimple branch of the common A.3.6 conclusions, the Fitting
subgroup has order one or three. The other branch has F* = F. -/
private theorem not_quasisimple_of_common {K : Type*} [Group K] [Finite K]
    (h : A36Common K) {p : ℕ} (hp3 : 3 < p)
    (hd : p ∣ Nat.card (fittingSubgroup K)) : ¬ IsQuasisimple K := by
  rcases h.2.2.1 with h | h
  · exact not_quasisimple_of_fitting_eq h.1.symm
  · rcases h.2.2 with he | he <;> rw [he] at hd
    · have := Nat.le_of_dvd (by decide : 0 < 1) hd
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) hd
      omega

private theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem not_quasisimple_local [Finite G] {E : Type*} [Group E] [Finite E]
    (L : Subgroup G) {C : Subgroup E} (e : XiQuotient L ≃* C)
    (h : A36Conclusion C) {p : ℕ} (hp3 : 3 < p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    ¬ IsQuasisimple (XiQuotient L) := by
  have hdC : p ∣ Nat.card (fittingSubgroup C) := by
    have hc := Nat.card_congr (e.subgroupMap (fittingSubgroup (XiQuotient L))).toEquiv
    rw [hc] at hd
    exact hd.trans (card_dvd_of_le (fitting_map_le e))
  intro hn
  let := hn
  exact not_quasisimple_of_common h.2 hp3 hdC (IsQuasisimple.of_mulEquiv e)

end CFSG.Quasithin.Chapter1.RadicalIdentification

namespace CFSG.Quasithin.Chapter1
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Conditional identification at the start of 1.3.8. The maximal normal
overgroup is the witness from Ξ*_rad; it need not be the component originally
defining X. The two inputs from 1.3.3 are membership in Ξ and the precise
uniform conjugation irreducibility on radical Frattini quotients. -/
public theorem XiRadStar_identification_of_source {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T : Subgroup G}
    (hQ : ∀ K ∈ L G T,
      IsSQTK 𝒦 ((K ⊔ T : Subgroup G) ⧸ pCore 2 (K ⊔ T : Subgroup G)))
    (hI : ∀ K ∈ L G T, ¬ IsQuasisimple (XiQuotient K) →
      ∀ (hTK : T ≤ normalizer (K : Set G)),
      ∀ q : ℕ, q.Prime → Odd q → q ∣ Nat.card (fittingSubgroup (XiQuotient K)) →
      ∀ A : Subgroup (XiFrattiniQuotient (XiP q K)),
        (∀ t : T, ∀ a ∈ A, xiFrattiniAction T (XiP q K) (XiP_invariant q hTK) t a ∈ A) →
          A = ⊥ ∨ A = ⊤)
    {X : Subgroup G} (hXrad : X ∈ XiRadStar G T) (hX : X ∈ Xi G T) :
    ∃ L₀ ∈ LStar G T, ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 < p ∧
      ¬ IsQuasisimple (XiQuotient L₀) ∧
      p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)) ∧
      X = XiP p L₀ ∧ (X.subgroupOf L₀).Characteristic := by
  obtain ⟨p, hp, ho, hp3, hodd⟩ := XiRad_oddQuotient_of_A36 hA36 hQ hXrad.1
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨L₀, hL, hXL, hN⟩ := hXrad.2
  have hd := RadicalIdentification.fitting_prime_of_normal hXL hN hodd
  have hn : ¬ IsQuasisimple (XiQuotient L₀) :=
    RadicalIdentification.not_quasisimple_local L₀ (radicalLocalQuotientEquiv hL.1)
      (proposition_1_2_1_four_earlier_conclusion hA36 (hQ L₀ hL.1) hL.1.1) hp3 hd
  have hT := radicalLocal_invariant_of_A38 hA38 hL.1 (hQ L₀ hL.1) hn
  have hY : XiMember T (XiP p L₀) :=
    { perfect := XiP_isPPerfect p L₀
      invariant := XiP_invariant p hT
      join_mem_H := XiP_join_mem_H p hL.1
      odd_quotient := ⟨p, hp, ho,
        (XiP_oddQuotient_of_A36 hA36 hL.1 (hQ L₀ hL.1) hn ho hd).2⟩
      irreducible := hI L₀ hL.1 hn hT p hp ho hd }
  have hXY := RadicalIdentification.le_XiP_of_normal hX hXL hN hodd
  have hNY : (X.subgroupOf (XiP p L₀)).Normal :=
    normal_subgroupOf_of_le_normalizer ((XiP_le p L₀).trans
      ((normal_subgroupOf_iff_le_normalizer hXL).mp hN))
  have he : X = XiP p L₀ := RadicalIdentification.eq_of_normal_le hX hY hXY hNY
  refine ⟨L₀, hL, p, hp, ho, hp3, hn, hd, he, ?_⟩
  rw [he]
  infer_instance

end CFSG.Quasithin.Chapter1
