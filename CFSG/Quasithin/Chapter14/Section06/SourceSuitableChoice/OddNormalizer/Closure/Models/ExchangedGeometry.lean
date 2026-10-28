module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Swapped
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.ExchangedResidual
public import Theory.SpecificGroups.PSL3Two.AlternatingFiveObstruction

/-!
# Literal product and field constraints for the exchanged closure

The index-two component normalizer identifies the original orbit with two
conjugates. The product uses the source inverse-conjugation convention.
The quotient product places the solvable Sylow overgroup in two binary
Borels, giving the original prime congruence. In the PSL₃(2) row the same
product and its order exclude an elementary quintic complement.

Models.Comparison applies these calculations to the original outside H,
discharging the corresponding exchanged-model requirements of 14.6.14.
Source: Aschbacher--Smith 1.3.4, pp.509--510, and 14.6.14, p.1033.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The exchanged intrinsic setup supplies the two actual factors, their
quotient product, and the original inverse-conjugation convention. -/
theorem swapped_closure_product
    {p : ℕ} {T X P J L : Subgroup G}
    (h : SwappedSylowInput KnownSimple.IsKnownSimple p T X P J L) :
    (∃ s ∈ T, s ∉ normalizer (L : Set G) ∧
      (componentOrbit L T : Set G) = (L : Set G) *
        (L.map (MulAut.conj s⁻¹).toMonoidHom : Set G)) ∧
    Nonempty (XiQuotient (componentOrbit L T) ≃* XiQuotient L × XiQuotient L) := by
  obtain ⟨hi,hm⟩ := SwappedSylow.nonnormal_model_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) h.toSwappedInput
  have hs := SwappedFactorsProof.quotient_simple h.toSwappedInput hm
  refine ⟨?_,SwappedFactorsProof.quotient_product
    ChapterA.Section03.CComponentCommutation.universal_A_3_7 h.toSwappedInput hi hs⟩
  obtain ⟨t,ht,hm⟩ := h.toSwappedInput.exists_swap
  refine ⟨t⁻¹,T.inv_mem ht.1,?_,?_⟩
  · intro hh
    exact hm (by simpa using (normalizer (L : Set G)).inv_mem hh)
  · rw [inv_inv,SwappedFactorsProof.orbit_eq_sup h.toSwappedInput hi ht.1 hm]
    apply coe_mul_of_right_le_normalizer_left
    exact (le_iSup (fun s : T => L.conjBy (s : G)) ⟨t,ht.1⟩).trans
      (cComponentOrbit_le_normalizer h.component (le_sup_right.trans h.overgroup))

/-- The binary component parameter satisfies the source congruence, obtained
from the solvable Sylow overgroup in the literal two-factor quotient. -/
theorem swapped_binary_congruence
    {p : ℕ} {T X P J L : Subgroup G}
    (h : SwappedSylowInput KnownSimple.IsKnownSimple p T X P J L)
    {m : ℕ} (hm : 2 ≤ m) (hbin : ClassicalGroup.IsPSL (XiQuotient L) 2 (2 ^ m)) :
    Nat.ModEq p (2 ^ m) 1 := by
  let : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨e⟩ := (swapped_closure_product h).2
  let R := SwappedSylow.imageInOrbit L T P
  obtain ⟨S,hS⟩ := SwappedSylow.orbit_quotient_sylow h
  let U := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let A := R.map e.toMonoidHom
  have hU : (U : Subgroup _) = (SwappedSylow.imageInOrbit L T T).map e.toMonoidHom := by
    change (S : Subgroup _).map e.toMonoidHom = _
    rw [hS]
  let : Group.IsSolvable (A ⊔ (U : Subgroup _) : Subgroup _) := by
    have he : A ⊔ (U : Subgroup _) =
        (SwappedSylow.imageInOrbit L T P ⊔ SwappedSylow.imageInOrbit L T T).map e.toMonoidHom := by
      rw [Subgroup.map_sup,hU]
    rw [he]
    let := SwappedSylow.quotient_solvable h.toSwappedInput
    exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)
  have hA : IsPGroup p A := (SwappedSylow.quotient_complement_odd h.toSwappedInput).isPGroup.map _
  have hne : A ≠ ⊥ := by
    intro hb
    have hz : SwappedSylow.imageInOrbit L T P = ⊥ :=
      Subgroup.map_injective e.injective (hb.trans (Subgroup.map_bot _).symm)
    apply SwappedSylow.quotient_complement_not_cyclic h.toSwappedInput
    rw [hz]
    infer_instance
  exact (SwappedSylow.binary_model_prod_restrictions hm hbin h.odd U A hA hne).2

/-- The PSL₃(2) exchanged row cannot carry the original quintic complement. -/
theorem swapped_linear_three_prime
    {p : ℕ} {T X P J L : Subgroup G}
    (h : SwappedSylowInput KnownSimple.IsKnownSimple p T X P J L)
    (hp : p = 3 ∨ p = 5) (hmodel : ClassicalGroup.IsPSL (XiQuotient L) 3 2) : p = 3 := by
  rcases hp with hp | rfl
  · exact hp
  exfalso
  obtain ⟨e⟩ := (swapped_closure_product h).2
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  have hdQ : Nat.card (XiQuotient L) ∣ 168 := by
    rw [Nat.card_congr (eF.trans (Atlas.fieldEquivPSL 3 ef)).toEquiv]
    exact Matrix.PSL3Two.card_PSL_dvd
  have hdP : 5 ∣ Nat.card P := h.odd_complement.isPGroup.card_eq_or_dvd.resolve_left
    (fun hh => h.complement_not_cyclic (by
      rw [(eq_bot_iff_card P).mpr hh]
      infer_instance))
  have hd : Nat.card P ∣ Nat.card (XiQuotient L) ^ 2 := by
    rw [Nat.card_congr (SwappedSylow.quotientComplementEquiv h.toSwappedInput).toEquiv]
    have hd := (SwappedSylow.imageInOrbit L T P).card_subgroup_dvd_card
    rwa [Nat.card_congr e.toEquiv,Nat.card_prod,←pow_two] at hd
  have hh : 5 ∣ 168 ^ 2 := hdP.trans (hd.trans (pow_dvd_pow_of_dvd hdQ 2))
  norm_num at hh
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
