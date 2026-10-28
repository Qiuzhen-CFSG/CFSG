module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.LocalData
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.ThreePrimary.NonsplitTorus
import all Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.ThreePrimary.NonsplitTwist
import all Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.Split
import all Theory.SpecificGroups.G2.MultiplierOrdinary.OddSplitTorus

/-!
# A full nonsplit Sylow three-normalizer in even-characteristic G₂

The published norm-one torus retains a Lang solution u. Conjugating the
Weyl cycle, swapping reflection and inverter by this same u gives
Frobenius-fixed elements: the inverter commutes with all three. Descent
through the literal field embedding puts them in the original Model F.
The injective conjugated embedding reflects their torus actions and the
cycle's order three and nonmembership in the torus.

The full torus has index q⁶(q−1)²(q⁴+q²+1). For q ≡ −1 modulo three,
this index is not divisible by nine. Adjoining the descended cycle to the
product of the two full Sylow three-subgroups of the norm-one coordinates
therefore gives a Sylow three-subgroup of Model F. This works for arbitrary
three-adic valuation of q+1. A cyclic generator of each coordinate supplies
the two generators exchanged by the reflection; the descended inverter
inverts the torus and commutes with the cycle.

Internal imports reuse the Weyl and field-embedding calculations without
changing the public boundaries of the existing ordinary-multiplier modules.
Sources: the ordinary G₂ entry underlying Aschbacher–Smith I.1.1–I.1.4,
printed pp.407–408, and GLS III §6.1; the twist uses Steinberg 8.5 and
10.7–10.8 in refs/KGroup/GLS3/Chapter2St2.tex. The octonion model and Weyl
maps are licensed ATLAS ports; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

open Subgroup Atlas.SplitOctonion
namespace Atlas.G2.MultiplierOrdinary.Nondefining.ThreePrimary
open PRegularClasses.FieldExtension PRegularClasses.RationalFusion

private theorem inverter_commute_swap {K : Type*} [Field K] :
    Commute ((weylR * weylS : Model K)^3) weylS := by
  change _ * _ = _ * _
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [pow_succ, weylR, weylS, weylREquiv, weylSEquiv,
    weylRLinear, weylSLinear, weylRApply, weylSApply]

variable {F : Type*} [Field F] [Finite F]
local notation "K" => AlgebraicClosure F
local notation "emb" => fieldEmbedding (algebraMap F K)

private theorem descent_of_twist (u : Model K)
    (hu : u * (frobenius F u)⁻¹ = (weylR * weylS)^3)
    (g : Model K)
    (hg : (weylR * weylS)^3 * frobenius F g * ((weylR * weylS)^3)⁻¹ = g) :
    ∃ d : Model F, emb d = u⁻¹ * g * u := by
  apply (frobenius_fixed_iff F _).mp
  have hfu : frobenius F u = ((weylR * weylS)^3)⁻¹ * u := by
    rw [← hu]
    group
  rw [map_mul, map_mul, map_inv, hfu]
  calc
    _ = u⁻¹ * ((weylR * weylS)^3 * frobenius F g * ((weylR * weylS)^3)⁻¹) * u := by group
    _ = u⁻¹ * g * u := by rw [hg]

private theorem exists_weyl_descents (u : Model K)
    (hu : u * (frobenius F u)⁻¹ = (weylR * weylS)^3) :
    ∃ c s v : Model F,
      emb c = u⁻¹ * (weylR * weylS)^2 * u ∧
      emb s = u⁻¹ * weylS * u ∧
      emb v = u⁻¹ * (weylR * weylS)^3 * u := by
  have hr : frobenius F (weylR : Model K) = weylR := by
    rw [← embedding_weylR (algebraMap F K)]
    exact frobenius_embedding F _
  have hs : frobenius F (weylS : Model K) = weylS := by
    rw [← embedding_weylS (algebraMap F K)]
    exact frobenius_embedding F _
  obtain ⟨c, hc⟩ := descent_of_twist u hu ((weylR * weylS)^2) (by
    rw [map_pow, map_mul, hr, hs]
    rw [((Commute.refl (weylR * weylS : Model K)).pow_pow 3 2).eq]
    simp [mul_assoc])
  obtain ⟨s, hs'⟩ := descent_of_twist u hu weylS (by
    rw [hs]
    rw [inverter_commute_swap.eq]
    simp [mul_assoc])
  obtain ⟨v, hv⟩ := descent_of_twist u hu ((weylR * weylS)^3) (by
    rw [map_pow, map_mul, hr, hs]
    simp [mul_assoc])
  exact ⟨c, s, v, hc, hs', hv⟩

private theorem nonsplit_index (j : NormOne F × NormOne F →* Model F)
    (hj : Nat.card j.range = (Nat.card F + 1)^2) :
    j.range.index = Nat.card F^6 * (Nat.card F - 1)^2 *
      (Nat.card F^4 + Nat.card F^2 + 1) := by
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hcard := j.range.card_mul_index
  rw [hj, card_Model] at hcard
  have h6 : Nat.card F^6 - 1 = (Nat.card F - 1) * (Nat.card F + 1) *
      (Nat.card F^4 + Nat.card F^2 + 1) := by
    apply Nat.sub_eq_of_eq_add
    set a := Nat.card F - 1
    have he : Nat.card F = a + 1 := (Nat.sub_add_cancel hq).symm
    rw [he]
    ring
  have h2 : Nat.card F^2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    apply Nat.sub_eq_of_eq_add
    nlinarith [Nat.sub_add_cancel hq]
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (by omega : 0 < Nat.card F + 1) 2)
  rw [hcard, h6, h2]
  ring

private theorem nine_not_dvd_nonsplit_index
    (j : NormOne F × NormOne F →* Model F)
    (hj : Nat.card j.range = (Nat.card F + 1)^2) (hd : 3 ∣ Nat.card F + 1) :
    ¬ 9 ∣ j.range.index := by
  rw [nonsplit_index j hj]
  have hq : Nat.card F % 3 = 2 := by omega
  intro he
  have hzero := (CharP.cast_eq_zero_iff (ZMod 9) 9 _).mpr he
  have hres : ∃ a : Fin 9, (a : ℕ) % 3 = 2 ∧ (Nat.card F : ZMod 9) = a := by
    refine ⟨⟨Nat.card F % 9, Nat.mod_lt _ (by decide)⟩, ?_, ?_⟩
    · simpa [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9)] using hq
    · rfl
  obtain ⟨a, ha, hqa⟩ := hres
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_sub (show 1 ≤ Nat.card F from Nat.card_pos)] at hzero
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one, hqa] at hzero
  have hcalc : ∀ a : Fin 9, a.val % 3 = 2 →
      (a : ZMod 9)^6 * (a-1)^2 * (a^4+a^2+1) ≠ 0 := by decide +kernel
  exact hcalc a ha hzero


private theorem pair_generates_image {A G : Type*} [CommGroup A] [Group G]
    (j : A × A →* G) (P : Subgroup A) (z : P)
    (hz : ∀ a : P, a ∈ zpowers z) :
    closure ({j (z, 1), j (1, z)} : Set G) = (P.prod P).map j := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨(z, 1), ⟨z.property, P.one_mem⟩, rfl⟩
    · exact ⟨(1, z), ⟨P.one_mem, z.property⟩, rfl⟩
  · rintro g ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hz ⟨a, ha⟩)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hz ⟨b, hb⟩)
    have hi' : (z : A) ^ i = a := congrArg Subtype.val hi
    have hk' : (z : A) ^ k = b := congrArg Subtype.val hk
    have hrep : j (a, b) = j (z, 1) ^ i * j (1, z) ^ k := by
      rw [← map_zpow, ← map_zpow, ← map_mul]
      congr 1
      ext <;> simp [hi', hk']
    rw [hrep]
    exact mul_mem (zpow_mem (subset_closure (by simp)) i)
      (zpow_mem (subset_closure (by simp)) k)

private theorem localData_of_descents
    (j : NormOne F × NormOne F →* Model F) (hj : Function.Injective j)
    (hcard : Nat.card j.range = (Nat.card F + 1)^2)
    (e : Model F →* Model K) (he : Function.Injective e)
    (ht : ∀ a : NormOne F × NormOne F, e (j a) = torus a.1 a.2)
    (c s v : Model F)
    (hc : e c = (weylR * weylS)^2) (hs : e s = weylS)
    (hv : e v = (weylR * weylS)^3) (hd : 3 ∣ Nat.card F + 1) :
    Nonempty (OddThreePrimary.LocalData F) := by
  let P : Sylow 3 (NormOne F) := Classical.choice inferInstance
  let T : Subgroup (Model F) :=
    ((P : Subgroup (NormOne F)).prod (P : Subgroup (NormOne F))).map j
  have hTle : T ≤ j.range := map_le_range _ _
  have hcout : c ∉ j.range := by
    rintro ⟨a, ha⟩
    have h := congrArg e ha
    rw [ht, hc] at h
    exact OddThreePrimary.cycle_not_mem_torus ⟨((a.1 : Kˣ), (a.2 : Kˣ)), h⟩
  have hc3 : c^3 = 1 := by
    apply he
    rw [map_pow, hc, map_one]
    exact OddThreePrimary.cycle_cube
  have hcne : c ≠ 1 := fun h => hcout (h ▸ j.range.one_mem)
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hcne
  have haction (l m : NormOne F) :
      c * j (l,m) * c⁻¹ = j (m*l⁻¹,l⁻¹) := by
    apply he
    simp only [map_mul, map_inv, hc, ht]
    exact OddThreePrimary.cycle_torus (l : Kˣ) (m : Kˣ)
  have hnorm : c ∈ normalizer (T : Set (Model F)) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨⟨l,m⟩,⟨hl,hm⟩,rfl⟩
      exact ⟨(m*l⁻¹,l⁻¹), ⟨P.mul_mem hm (P.inv_mem hl), P.inv_mem hl⟩,
        (haction l m).symm⟩
    · rintro ⟨⟨l,m⟩,⟨hl,hm⟩,hx⟩
      refine ⟨(m⁻¹,l*m⁻¹),⟨P.inv_mem hm,P.mul_mem hl (P.inv_mem hm)⟩,?_⟩
      apply (MulAut.conj c).injective
      change c * j (m⁻¹,l*m⁻¹) * c⁻¹ = c*x*c⁻¹
      rw [haction]
      change j (l,m) = _ at hx
      simpa using hx
  have hcnorm : zpowers c ≤ normalizer (T : Set (Model F)) := zpowers_le.mpr hnorm
  have hdis : Disjoint T (zpowers c) :=
    T.disjoint_zpowers_of_prime_order_not_mem c hcord (fun h => hcout (hTle h))
  let H := T ⊔ zpowers c
  have hcardH : Nat.card H = Nat.card T * 3 := by
    dsimp [H]
    rw [card_sup_eq_mul_of_normalizes_of_disjoint T _ hcnorm hdis, Nat.card_zpowers, hcord]
  have hindex : 3 * H.index = T.index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := T))
    rw [← mul_assoc, ← hcardH, H.card_mul_index, T.card_mul_index]
  have hTindex : T.index = (P : Subgroup (NormOne F)).index *
      (P : Subgroup (NormOne F)).index * j.range.index := by
    dsimp [T]
    rw [index_map_of_injective _ hj, index_prod]
  have hnotnine : ¬ 9 ∣ T.index := by
    rw [hTindex]
    have hcop : Nat.Coprime 9 ((P : Subgroup (NormOne F)).index *
        (P : Subgroup (NormOne F)).index) := by
      apply Nat.Coprime.pow_left (m := 3) (n := 2)
      exact (Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index).mul_right
        (Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index)
    exact fun hh => nine_not_dvd_nonsplit_index j hcard hd (hcop.dvd_mul_left.mp hh)
  have hHindex : ¬ 3 ∣ H.index := by
    intro hi
    apply hnotnine
    rw [← hindex]
    exact Nat.mul_dvd_mul_left 3 hi
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hTp : IsPGroup 3 T := by
    apply IsPGroup.map
    apply IsPGroup.of_card (n := k+k)
    rw [Nat.card_congr (Subgroup.prodEquiv (P : Subgroup (NormOne F))
      (P : Subgroup (NormOne F))).toEquiv, Nat.card_prod, hk, pow_add]
  have hcp : IsPGroup 3 (zpowers c) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hcord, pow_one])
  let Q : Sylow 3 (Model F) := (hTp.to_sup_of_normal_left' hcp hcnorm).toSylow hHindex
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := P)
  refine ⟨{
    sylow := Q
    torus := T
    first := j (z, 1)
    second := j (1, z)
    cycle := c
    swap := s
    inverter := v
    torus_generated := pair_generates_image j _ z hz
    generators_commute := (Commute.all ((z : NormOne F),1) (1,(z : NormOne F))).map j
    swap_first := ?_
    swap_second := ?_
    sylow_generated := rfl
    cycle_normalizes := hnorm
    inverts_torus := ?_
    fixes_cycle := ?_ }⟩
  · apply he
    simp only [map_mul, map_inv, hs, ht]
    exact OddSplitTorus.weylS_torus _ _
  · apply he
    simp only [map_mul, map_inv, hs, ht]
    exact OddSplitTorus.weylS_torus _ _
  · rintro t ⟨⟨l,m⟩,_,rfl⟩
    apply he
    simp only [map_mul, map_inv, hv, ht]
    exact OddThreePrimary.inverter_torus _ _
  · change v*c = c*v
    apply he
    simp only [map_mul, hv, hc]
    exact (Commute.refl (weylR*weylS : Model K)).pow_pow 3 2

/-- The descended norm-one torus and rational Weyl elements give a full
Sylow three-normalizer, with no restriction on the three-part of q + 1. -/
public theorem exists_nonsplit_localData [CharP F 2] (hd : 3 ∣ Nat.card F + 1) :
    Nonempty (OddThreePrimary.LocalData F) := by
  obtain ⟨u, j, hu, hj, ht, hcard⟩ := exists_nonsplit_torus F
  obtain ⟨c, s, v, hc, hs, hv⟩ := exists_weyl_descents u hu
  let e : Model F →* Model K := (MulAut.conj u).toMonoidHom.comp emb
  have he : Function.Injective e :=
    (MulAut.conj u).injective.comp (fieldEmbedding_injective (algebraMap F K))
  have heq (g : Model F) : e g = u * emb g * u⁻¹ := rfl
  have ht' (a : NormOne F × NormOne F) : e (j a) = torus a.1 a.2 := by
    rw [heq, ht]
    group
  apply localData_of_descents j hj hcard e he ht' c s v ?_ ?_ ?_ hd
  · rw [heq, hc]
    group
  · rw [heq, hs]
    group
  · rw [heq, hv]
    group

/-- The remaining even-characteristic source range, in the form required by
three-primary multiplier assembly. All local normalizer witnesses are supplied. -/
public theorem exists_nonsplit_localData_of_nine_dvd [CharP F 2]
    (_hF : 4 < Nat.card F) (h9 : 9 ∣ Nat.card F + 1) :
    Nonempty (OddThreePrimary.LocalData F) :=
  exists_nonsplit_localData (dvd_trans (by decide : 3 ∣ 9) h9)

end Atlas.G2.MultiplierOrdinary.Nondefining.ThreePrimary
