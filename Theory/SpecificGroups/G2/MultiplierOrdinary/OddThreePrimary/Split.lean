module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.LocalData
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddSplitTorus
import all Theory.SpecificGroups.G2.MultiplierOrdinary.OddSplitTorus
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.NormalizedSupCard

/-!
# A full split Sylow three-subgroup of the actual G₂ model

Take the product of two Sylow three-subgroups of the field units in the
published split torus. The square of the Coxeter Weyl element normalizes
this product, has order three, and lies outside the full split torus.
Adjoining it therefore multiplies the torus's three-part by three.

The full split-torus index is divisible by three but not nine when the
field order is one modulo three. The resulting subgroup is consequently
Sylow, without a bound on the three-adic valuation of the field-unit order.
The Weyl reflection swaps its torus generators, while the cube of the
Coxeter element inverts the torus and centralizes the cyclic supplement.

The internal import reuses `OddSplitTorus`'s generator and reflection proofs
without changing that module's public interface. The octonion torus and
Weyl matrices are licensed ATLAS ports (LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff). This gives the split local input for the
ordinary multiplier entry of Aschbacher–Smith I.1.1–I.1.4, pp.407–408,
and GLS III §6.1; `OddThreePrimary` applies it to the canonical cover.
-/

open Subgroup Atlas.SplitOctonion
namespace Atlas.G2.MultiplierOrdinary.OddThreePrimary
variable {F : Type*} [Field F]

private def cycle : Model F := (weylR * weylS)^2
private def inverter : Model F := (weylR * weylS)^3

private theorem cycle_cube : (cycle : Model F)^3 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [cycle, pow_succ, weylR, weylS, weylREquiv, weylSEquiv,
    weylRLinear, weylSLinear, weylRApply, weylSApply]

private theorem weylR_torus (l m : Fˣ) :
    weylR * torus l m * weylR⁻¹ = torus l (l*m⁻¹) := by
  have hi : (weylR : Model F)⁻¹ = weylR :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using weylR_sq (K := F))
  rw [hi]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [torus,torusEquiv,torusLinear,torusWeights,
    weylR,weylREquiv,weylRLinear,weylRApply]
  field_simp
  simp

private theorem coxeter_torus (l m : Fˣ) :
    (weylR*weylS) * torus l m * (weylR*weylS)⁻¹ = torus m (m*l⁻¹) := by
  calc
    _ = weylR * (weylS * torus l m * weylS⁻¹) * weylR⁻¹ := by group
    _ = _ := by rw [OddSplitTorus.weylS_torus,weylR_torus]

private theorem cycle_torus (l m : Fˣ) :
    cycle * torus l m * cycle⁻¹ = torus (m*l⁻¹) l⁻¹ := by
  have he : cycle * torus l m * cycle⁻¹ =
      (weylR*weylS) * ((weylR*weylS)*torus l m*(weylR*weylS)⁻¹)*(weylR*weylS)⁻¹ := by
    simp only [cycle,pow_two,mul_inv_rev,mul_assoc]
  rw [he, coxeter_torus, coxeter_torus]
  simp

private theorem inverter_torus (l m : Fˣ) :
    inverter * torus l m * inverter⁻¹ = (torus l m)⁻¹ := by
  have he : inverter * torus l m * inverter⁻¹ =
      (weylR*weylS)*(cycle*torus l m*cycle⁻¹)*(weylR*weylS)⁻¹ := by
    simp [inverter,cycle,pow_succ,mul_assoc]
  rw [he, cycle_torus, coxeter_torus]
  have hi : (torus l m)⁻¹ = torus l⁻¹ m⁻¹ := by
    change (torusHom (l,m))⁻¹ = torusHom (l⁻¹,m⁻¹)
    exact (map_inv torusHom (l,m)).symm
  rw [hi]
  simp

private theorem cycle_not_mem_torus : (cycle : Model F) ∉ splitTorus := by
  rintro ⟨⟨l,m⟩, h⟩
  have he := congrArg (fun g : Model F => g.val (basisVector 0) 6) h
  simp [cycle, pow_succ, torusHom, torus, torusEquiv, torusLinear,torusWeights,
    weylR,weylS,weylREquiv,weylSEquiv,weylRLinear,weylSLinear,weylRApply,weylSApply,
    basisVector] at he

private theorem torusThree_normalized (P : Subgroup Fˣ) :
    cycle ∈ normalizer ((((P.prod P).map torusHom) : Subgroup (Model F)) : Set (Model F)) := by
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨⟨l,m⟩,⟨hl,hm⟩,rfl⟩
    exact ⟨(m*l⁻¹,l⁻¹), ⟨P.mul_mem hm (P.inv_mem hl), P.inv_mem hl⟩,
      (cycle_torus l m).symm⟩
  · rintro ⟨⟨l,m⟩,⟨hl,hm⟩,he⟩
    refine ⟨(m⁻¹,l*m⁻¹),⟨P.inv_mem hm,P.mul_mem hl (P.inv_mem hm)⟩,?_⟩
    apply (MulAut.conj (cycle : Model F)).injective
    change cycle*torus m⁻¹ (l*m⁻¹)*cycle⁻¹ = cycle*x*cycle⁻¹
    rw [cycle_torus]
    change torus l m = _ at he
    simpa using he

private theorem nine_not_dvd_split_index [Finite F] (hd : 3 ∣ Nat.card F - 1) :
    ¬ 9 ∣ (splitTorus (K := F)).index := by
  rw [OddSplitTorus.splitTorus_index]
  have hq : Nat.card F % 3 = 1 := by
    have hqpos : 1 ≤ Nat.card F := Nat.card_pos
    obtain ⟨k,hk⟩ := hd
    omega
  intro he
  have hzero := (CharP.cast_eq_zero_iff (ZMod 9) 9 _).mpr he
  have hres : ∃ a : Fin 9, (a : ℕ) % 3 = 1 ∧ (Nat.card F : ZMod 9) = a := by
    refine ⟨⟨Nat.card F % 9, Nat.mod_lt _ (by decide)⟩, ?_, ?_⟩
    · simpa [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9)] using hq
    · rfl
  obtain ⟨a,ha,hqa⟩ := hres
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_one,hqa] at hzero
  have hcalc : ∀ a : Fin 9, a.val % 3 = 1 →
      (a : ZMod 9)^6 * (a^5+a^4+a^3+a^2+a+1) * (a+1) ≠ 0 := by decide +kernel
  exact hcalc a ha hzero

/-- The actual split torus and Weyl cycle give the required configuration. -/
public theorem exists_split_localData [Finite F] (hd : 3 ∣ Nat.card F - 1) : Nonempty (LocalData F) := by
  let P : Sylow 3 Fˣ := Classical.choice inferInstance
  let T : Subgroup (Model F) := ((P : Subgroup Fˣ).prod (P : Subgroup Fˣ)).map torusHom
  have hTle : T ≤ splitTorus := map_le_range _ _
  have hcne : (cycle : Model F) ≠ 1 := by
    intro he
    exact cycle_not_mem_torus (he ▸ (splitTorus (K := F)).one_mem)
  have hcord : orderOf (cycle : Model F) = 3 := orderOf_eq_prime cycle_cube hcne
  have hcnorm : zpowers (cycle : Model F) ≤ normalizer (T : Set (Model F)) :=
    zpowers_le.mpr (torusThree_normalized _)
  have hdis : Disjoint T (zpowers (cycle : Model F)) :=
    T.disjoint_zpowers_of_prime_order_not_mem cycle hcord (fun hc => cycle_not_mem_torus (hTle hc))
  let H := T ⊔ zpowers (cycle : Model F)
  have hcardH : Nat.card H = Nat.card T * 3 := by
    dsimp [H]
    rw [card_sup_eq_mul_of_normalizes_of_disjoint T _ hcnorm hdis, Nat.card_zpowers,hcord]
  have hindex : 3 * H.index = T.index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := T))
    rw [← mul_assoc, ← hcardH, H.card_mul_index, T.card_mul_index]
  have hTindex : T.index = (P : Subgroup Fˣ).index * (P : Subgroup Fˣ).index *
      (splitTorus (K := F)).index := by
    dsimp [T]
    rw [index_map_of_injective _ torusHom_injective,index_prod]
    rfl
  have hnotnine : ¬ 9 ∣ T.index := by
    rw [hTindex]
    have hc : Nat.Coprime 9 ((P : Subgroup Fˣ).index * (P : Subgroup Fˣ).index) := by
      apply Nat.Coprime.pow_left (m := 3) (n := 2)
      exact (Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index).mul_right
        (Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index)
    exact fun hh => nine_not_dvd_split_index hd (hc.dvd_mul_left.mp hh)
  have hHindex : ¬ 3 ∣ H.index := by
    intro hi
    apply hnotnine
    rw [← hindex]
    exact Nat.mul_dvd_mul_left 3 hi
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hTp : IsPGroup 3 T := by
    apply IsPGroup.map
    apply IsPGroup.of_card (n := k+k)
    rw [Nat.card_congr (Subgroup.prodEquiv (P : Subgroup Fˣ) (P : Subgroup Fˣ)).toEquiv,
      Nat.card_prod,hk,pow_add]
  have hcp : IsPGroup 3 (zpowers (cycle : Model F)) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hcord,pow_one])
  let Q : Sylow 3 (Model F) := (hTp.to_sup_of_normal_left' hcp hcnorm).toSylow hHindex
  obtain ⟨z,hz⟩ := IsCyclic.exists_generator (α := P)
  refine ⟨{
    sylow := Q
    torus := T
    first := torus z 1
    second := torus 1 z
    cycle := cycle
    swap := weylS
    inverter := inverter
    torus_generated := OddSplitTorus.pair_generates _ z hz
    generators_commute := (Commute.all ((z : Fˣ),1) (1,(z : Fˣ))).map torusHom
    swap_first := by simpa using OddSplitTorus.weylS_torus (z : Fˣ) 1
    swap_second := by simpa using OddSplitTorus.weylS_torus 1 (z : Fˣ)
    sylow_generated := rfl
    cycle_normalizes := torusThree_normalized _
    inverts_torus := ?_
    fixes_cycle := ?_ }⟩
  · rintro t ⟨⟨l,m⟩,_,rfl⟩
    exact inverter_torus l m
  · exact (Commute.refl (weylR*weylS : Model F)).pow_pow 3 2

end Atlas.G2.MultiplierOrdinary.OddThreePrimary
