module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.Interface
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.Model
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SylowCentralizerNonfusion
public import Theory.GroupTheory.FocalTransfer
public import Theory.GroupTheory.SylowTransferVanishing

/-!
# Held's normal subgroup of index four

For the actual Sylow subgroup T = C_K(p) supplied by `TransferFusion`,
the characteristic derived subgroup <p> forces N_K(T) = T. The three
nonidentity elements of the central complement <l,z> survive transfer:
transfer from every proper subgroup of T kills a central involution,
so the self-normalizer transfer formula leaves its abelianization image.
As the fused generators lt,zm lie in K', and <l,z> represents T/R, this
computes T ∩ K' = R. The focal transfer then has a normal kernel of index
four meeting T in R. This calculation uses no fusion bound beyond the two
specified conjugacies.

We also prove the exceptional nonfusion on printed p.234 by an invariant
product version of the elementary-eight normalizer argument. In
E = C_T(zm), the five possible conjugates of p are
p, zm, pzm, zlm, pzlm. They lie in <p,l,zm> and their product is p.
If exceptional fusion occurred, all five would be conjugate; every element
of N_K(E) would permute them and hence fix their product p. But
E = C_K(p) ∩ C_K(zm) has order 16, smaller than the order-32 Sylow
centralizer of either conjugate element. The normalizer condition inside
C_K(zm) contradicts N_K(E) ≤ C_K(p). This excludes the source's index-two
case directly in K, without first constructing a prospective subgroup.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, proof of Lemma 4.2, pp.233--234.
Constructing `TransferFusion` remains the source application's obligation.
-/

open Subgroup
open scoped commutatorElement BigOperators
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
open TransferModel

private theorem model_derived : commutator Model = zpowers TransferModel.p := by
  apply le_antisymm
  · rw [commutator_def, commutator_le]
    intro a _ b _
    have h : ∀ a b : Model, ⁅a,b⁆ = 1 ∨ ⁅a,b⁆ = TransferModel.p := by decide +kernel
    rcases h a b with he | he
    · rw [he]; exact one_mem _
    · rw [he]; exact mem_zpowers _
  · apply zpowers_le.mpr
    rw [← commutator_lt_zm]
    exact commutator_mem_commutator (mem_top _) (mem_top _)

private instance : DecidablePred (· ∈ R) := fun x => MonoidHom.decidableMemRange coreHom x

private theorem model_central_cosets :
    ∀ x : Model, x ∈ R ∨ x * l ∈ R ∨ x * z ∈ R ∨ x * (l * z) ∈ R := by
  decide +kernel

namespace IndexFourLocal
private abbrev E : Subgroup Model := centralizer ({z * m} : Set Model)
private instance : DecidablePred (· ∈ E) := fun x =>
  decidable_of_iff (x * (z * m) = (z * m) * x) mem_centralizer_singleton_iff.symm
private instance : CommGroup E := { E.toGroup with mul_comm := by decide +kernel }
private def pE : E := ⟨TransferModel.p, by decide +kernel⟩
private def aE : E := ⟨z * m, by decide +kernel⟩
private def bE : E := ⟨z * l * m, by decide +kernel⟩
private def five : Finset E := {pE, aE, pE * aE, bE, pE * bE}

private theorem five_product : ∏ x ∈ five, x = pE := by decide +kernel

private theorem five_of_bound (x : E)
    (hx : (x : Model) = TransferModel.p ∨ (x : Model) = l * t ∨
      (x : Model) = TransferModel.p * (l * t) ∨ (x : Model) = z * m ∨
      (x : Model) = TransferModel.p * (z * m) ∨ (x : Model) = z * l * m ∨
      (x : Model) = TransferModel.p * (z * l * m)) : x ∈ five := by
  rcases x with ⟨x, hxE⟩
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [five, pE]
  · exact ((by decide +kernel : l * t ∉ E) hxE).elim
  · exact ((by decide +kernel : TransferModel.p * (l * t) ∉ E) hxE).elim
  · simp [five, aE]
  · change pE * aE ∈ five
    simp [five]
  · simp [five, bE]
  · change pE * bE ∈ five
    simp [five]

private theorem auto_fixes_p (f : E ≃* E) (h : ∀ x, x ∈ five ↔ f x ∈ five) : f pE = pE := by
  calc
    f pE = f (∏ x ∈ five, x) := congrArg f five_product.symm
    _ = ∏ x ∈ five, f x := map_prod f _ _
    _ = ∏ x ∈ five, x := Finset.prod_equiv f.toEquiv h (fun _ _ => rfl)
    _ = pE := five_product
end IndexFourLocal

namespace TransferFusion
variable {K : Type*} [Group K] {p : K} (F : TransferFusion K p)

private theorem into_range : F.into.range = (F.sylow : Subgroup K) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (F.coordinates y).property
  · intro hx
    obtain ⟨y, hy⟩ := F.coordinates.surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

private theorem sylow_derived :
    (commutator F.sylow).map (F.sylow : Subgroup K).subtype = zpowers p := by
  rw [map_subtype_commutator, ← F.into_range, MonoidHom.range_eq_map,
    ← map_commutator, ← commutator_def, model_derived,
    MonoidHom.map_zpowers, F.into_p]

/-- The marked Sylow subgroup is self-normalizing. -/
public theorem normalizer_sylow [Finite K] :
    normalizer (F.sylow : Set K) = (F.sylow : Subgroup K) := by
  apply le_antisymm _ le_normalizer
  exact (normalizer_le_centralizer_of_characteristic_involution _ (commutator F.sylow)
    p F.p_order F.sylow_derived).trans F.centralizer_eq.le

/-- Distinct elements centralizing the Sylow subgroup cannot fuse. -/
public theorem eq_of_isConj_of_mem_centralizer [Finite K] (x y : K)
    (hx : x ∈ centralizer (F.sylow : Set K))
    (hy : y ∈ centralizer (F.sylow : Set K)) (hxy : IsConj x y) : y = x := by
  apply F.sylow.eq_of_isConj_of_normalizer_le_centralizer x y hx hy _ hxy
  rw [F.normalizer_sylow]
  intro a ha
  exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx a ha)

open IndexFourLocal

private theorem model_conj (x y w : Model) (h : w * x * w⁻¹ = y) : IsConj (F.into x) (F.into y) := by
  refine isConj_iff.mpr ⟨F.into w, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, h]

private theorem five_class (h : IsConj p (F.into (z * l * m))) (x : E) :
    x ∈ five ↔ IsConj p (F.into (x : Model)) := by
  constructor
  · intro hx
    simp only [five, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rw [show (pE : Model) = TransferModel.p from rfl, F.into_p]
    · exact F.conj_zm
    · exact F.conj_zm.trans (F.model_conj (z * m) (TransferModel.p * (z * m)) t (by decide +kernel))
    · exact h
    · exact h.trans (F.model_conj (z * l * m) (TransferModel.p * (z * l * m)) t (by decide +kernel))
  · intro hx
    exact five_of_bound x (F.class_bound x hx)

private theorem exceptional_normalizer (h : IsConj p (F.into (z * l * m))) :
    normalizer (E.map F.into : Set K) ≤ centralizer ({p} : Set K) := by
  intro n hn
  let e := E.equivMapOfInjective F.into F.into_injective
  let a := (E.map F.into).normalizerMonoidHom ⟨n, hn⟩
  let f := e.trans (a.trans e.symm)
  have hf (x : E) : F.into (f x : Model) = n * F.into (x : Model) * n⁻¹ := by
    have he : e (f x) = a (e x) := by simp [f]
    exact congrArg Subtype.val he
  have hclass (x : E) : x ∈ five ↔ f x ∈ five := by
    rw [F.five_class h, F.five_class h, hf]
    have hc : IsConj (F.into (x : Model)) (n * F.into (x : Model) * n⁻¹) :=
      isConj_iff.mpr ⟨n, rfl⟩
    exact ⟨fun hx => hx.trans hc, fun hx => hx.trans hc.symm⟩
  have he := hf pE
  rw [auto_fixes_p f hclass, show (pE : Model) = TransferModel.p from rfl, F.into_p] at he
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he.symm)

private theorem E_eq_common : E.map F.into =
    centralizer ({p} : Set K) ⊓ centralizer ({F.into (z * m)} : Set K) := by
  rw [F.centralizer_eq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(F.coordinates y).property, mem_centralizer_singleton_iff.mpr ?_⟩
    simpa only [map_mul] using congrArg F.into (mem_centralizer_singleton_iff.mp hy)
  · rintro ⟨hx, hc⟩
    obtain ⟨y, hy⟩ := F.coordinates.surjective ⟨x, hx⟩
    have he : F.into y = x := congrArg Subtype.val hy
    refine ⟨y, ?_, he⟩
    apply mem_centralizer_singleton_iff.mpr
    apply F.into_injective
    simpa only [map_mul, he] using mem_centralizer_singleton_iff.mp hc

/-- The exceptional fusion which would give only an index-two transfer kernel is impossible. -/
public theorem not_conj_zlm [Finite K] : ¬ IsConj p (F.into (z * l * m)) := by
  intro h
  have hEC : (F.sylow : Subgroup K) ≤ centralizer ({p} : Set K) := F.centralizer_eq.symm.le
  have hp : IsPGroup 2 (E.map F.into) := by
    have hET : E.map F.into ≤ (F.sylow : Subgroup K) := by
      rintro _ ⟨y, _, rfl⟩
      exact (F.coordinates y).property
    exact F.sylow.isPGroup'.of_injective (inclusion hET) (inclusion_injective hET)
  have hcardE : Nat.card (E.map F.into) = 16 := by
    rw [card_map_of_injective F.into_injective, Nat.card_eq_fintype_card]
    decide +kernel
  have hcardS : Nat.card (F.sylow.subtype hEC) = 32 := by
    change Nat.card ((F.sylow : Subgroup K).subgroupOf (centralizer ({p} : Set K))) = 32
    rw [Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv,
      ← Nat.card_congr F.coordinates.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hnot := normalizer_inf_centralizer_not_le_of_isConj
    p (F.into (z * m)) F.conj_zm (F.E_eq_common ▸ hp) (F.sylow.subtype hEC)
    (by rw [← F.E_eq_common, hcardE, hcardS]; decide)
  apply hnot
  change normalizer (↑(centralizer ({p} : Set K) ⊓ centralizer ({F.into (z * m)} : Set K)) : Set K) ≤ _
  rw [← F.E_eq_common]
  exact F.exceptional_normalizer h

private theorem central_not_derived [Finite K] (x : Model)
    (hx : x ≠ 1 ∧ x ≠ TransferModel.p)
    (hsq : x ^ 2 = 1) (hc : ∀ y : Model, Commute x y) :
    F.into x ∉ commutator K := by
  classical
  let u : F.sylow := F.coordinates x
  have hu : u ∉ commutator F.sylow := by
    intro hu
    have hm : F.into x ∈ zpowers p := by
      rw [← F.sylow_derived]
      exact mem_map_of_mem _ hu
    rw [mem_zpowers_iff_mem_range_orderOf, F.p_order] at hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    have hi2 : i < 2 := Finset.mem_range.mp hi
    interval_cases i
    · exact hx.1 (F.into_injective (by simpa using he.symm))
    · exact hx.2 (F.into_injective (by simpa only [pow_one, F.into_p] using he.symm))
  apply F.sylow.not_mem_commutator_of_maximal_transfer_vanishing
    F.normalizer_sylow u ⊥ hu
  · change u ^ 2 = 1
    exact (map_pow F.coordinates x 2).symm.trans (by rw [hsq, map_one])
  · intro v
    change ⁅u, v⁆ = 1
    apply commutatorElement_eq_one_iff_commute.mpr
    obtain ⟨y, rfl⟩ := F.coordinates.surjective v
    exact (hc y).map F.coordinates
  · intros
    exact bot_le

private theorem R_le_derived : R.map F.into ≤ commutator K := by
  have hp : p ∈ commutator K := by
    rw [← F.into_p, ← commutator_lt_zm, map_commutatorElement]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  rw [map_le_iff_le_comap]
  apply R_le
  · change (F.coordinates (l * t) : K) ∈ commutator K
    obtain ⟨g, hg⟩ := isConj_iff.mp F.conj_lt
    simpa only [hg] using (inferInstance : (commutator K).Normal).conj_mem p hp g
  · change (F.coordinates (z * m) : K) ∈ commutator K
    obtain ⟨g, hg⟩ := isConj_iff.mp F.conj_zm
    simpa only [hg] using (inferInstance : (commutator K).Normal).conj_mem p hp g

private theorem derived_inf [Finite K] :
    commutator K ⊓ (F.sylow : Subgroup K) = R.map F.into := by
  have hlocal : ∀ x : Model, x ∉ R → ∃ c : Model,
      (c ≠ 1 ∧ c ≠ TransferModel.p) ∧ c ^ 2 = 1 ∧
      (∀ y : Model, c * y = y * c) ∧ x * c ∈ R := by
    intro x hx
    rcases model_central_cosets x with h | h | h | h
    · exact (hx h).elim
    · exact ⟨l, by decide +kernel, by decide +kernel, by decide +kernel, h⟩
    · exact ⟨z, by decide +kernel, by decide +kernel, by decide +kernel, h⟩
    · exact ⟨l * z, by decide +kernel, by decide +kernel, by decide +kernel, h⟩
  apply le_antisymm
  · rintro a ⟨haD, haT⟩
    obtain ⟨x, he⟩ := F.coordinates.surjective ⟨a, haT⟩
    have he' : F.into x = a := congrArg Subtype.val he
    refine ⟨x, ?_, he'⟩
    by_contra hx
    obtain ⟨c, hc, hc2, hcentral, hxc⟩ := hlocal x hx
    have hmul := F.R_le_derived (mem_map_of_mem F.into hxc)
    rw [map_mul, he'] at hmul
    exact F.central_not_derived c hc hc2 (fun y => hcentral y)
      ((commutator K).mul_mem_cancel_left haD |>.mp hmul)
  · exact le_inf F.R_le_derived (by
      rintro _ ⟨x, _, rfl⟩
      exact (F.coordinates x).property)

private theorem index_four_model : R.index = 4 := by
  have hc : Nat.card R = 8 := by
    rw [← Nat.card_congr coreEquiv.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hm : Nat.card Model = 32 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hh := R.index_mul_card
  rw [hc, hm] at hh
  omega

/-- The focal subgroup is exactly the marked dihedral subgroup of order eight. -/
public theorem focal_subgroup_eq [Finite K] :
    (F.sylow : Subgroup K).focalSubgroup = R.map F.into := by
  rw [← commutator_inf_eq_focalSubgroup F.sylow, F.derived_inf]

/-- Held's actual normal index-four subgroup, with its prescribed Sylow intersection. -/
public theorem exists_normal_index_four [Finite K] :
    ∃ M : Subgroup K, M.Normal ∧ M.index = 4 ∧
      M ⊓ (F.sylow : Subgroup K) = R.map F.into := by
  let T : Subgroup K := F.sylow
  let M := T.transferFocal.ker
  have hf : T.focalSubgroup = R.map F.into := F.focal_subgroup_eq
  have hinter : M ⊓ T = R.map F.into :=
    (ker_transferFocal_inf_eq_focalSubgroup F.sylow).trans hf
  have hrel : (R.map F.into).relIndex T = 4 := by
    change (R.map F.into).relIndex (F.sylow : Subgroup K) = 4
    rw [← F.into_range, MonoidHom.range_eq_map,
      relIndex_map_map_of_injective _ _ F.into_injective, relIndex_top_right,
      index_four_model]
  have hq : Nat.card (T ⧸ T.focalSubgroupOf) = 4 := by
    rw [← index_eq_card]
    change T.focalSubgroup.relIndex T = 4
    rwa [hf]
  refine ⟨M, inferInstance, ?_, hinter⟩
  apply Nat.dvd_antisymm
  · rw [index_ker]
    exact hq ▸ card_subgroup_dvd_card T.transferFocal.range
  · rw [← hrel, ← hinter, inf_relIndex_right]
    exact relIndex_dvd_index_of_normal (H := M) (K := T)

end TransferFusion
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
