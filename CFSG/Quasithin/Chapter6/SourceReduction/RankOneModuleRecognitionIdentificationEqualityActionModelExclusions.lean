module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionModelNormalizers
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionModelResidual
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionModelLinear

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Excluding the symmetric equality-action models

An odd involution in S₆ or S₇ has two conjugates which centralize it,
fail to commute with each other, and have product of order three. The
corresponding literal layer pair lies in H ∩ M. Its extraspecial core,
provided by local analysis, forces z into O²(H ∩ M), contradicting the
previous residual disjointness theorem. Together with the linear-model
exclusion this leaves the actual natural GL₂(2) action.

Source: Aschbacher–Smith, 6.2.13, printed pp.686–687 (PDF pp.703–704).
The quotient maps and conjugation conventions are those of the canonical
involution centralizer; no abstract family label replaces an action model.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.EqualitySymmetricPair
open Equiv Equiv.Perm
private def rep (n k : ℕ) : Perm (Fin (n + 6)) :=
  if k = 0 then swap 0 1 else swap 0 1 * swap 2 3 * swap 4 5
private def left (n k : ℕ) : Perm (Fin (n + 6)) :=
  if k = 0 then swap 2 3 else swap 0 2 * swap 1 3 * swap 4 5
private def right (n k : ℕ) : Perm (Fin (n + 6)) :=
  if k = 0 then swap 3 4 else swap 0 4 * swap 1 5 * swap 2 3
private theorem certificate (n k : Fin 2) :
    (rep n k).cycleType = Multiset.replicate (if k = 0 then 1 else 3) 2 ∧
    (left n k).cycleType = (rep n k).cycleType ∧
    (right n k).cycleType = (rep n k).cycleType ∧
    Commute (left n k) (rep n k) ∧ Commute (right n k) (rep n k) ∧
    ¬ Commute (left n k) (right n k) ∧
    (left n k * right n k)^3 = 1 ∧ left n k * right n k ≠ 1 := by
  fin_cases n <;> fin_cases k <;> unfold Commute SemiconjBy <;> decide +kernel

private theorem rep_pair (n k : Fin 2) :
    ∃ b c : Perm (Fin (n.val + 6)), IsConj (rep n k) b ∧ IsConj (rep n k) c ∧
      Commute b (rep n k) ∧ Commute c (rep n k) ∧ ¬ Commute b c ∧ orderOf (b*c) = 3 := by
  obtain ⟨_, hb, hc, hba, hca, hbc, hp, hn⟩ := certificate n k
  exact ⟨left n k, right n k, isConj_of_cycleType_eq hb.symm,
    isConj_of_cycleType_eq hc.symm, hba, hca, hbc, orderOf_eq_prime_iff.mpr ⟨hp, hn⟩⟩

/-- Two conjugates of an odd involution centralize it and generate a non-two pair. -/
theorem exists_pair (n : Fin 2) (t : Perm (Fin (n.val + 6)))
    (ht2 : t ^ 2 = 1) (hodd : t.sign ≠ 1) :
    ∃ b c : Perm (Fin (n.val + 6)), IsConj t b ∧ IsConj t c ∧
      Commute b t ∧ Commute c t ∧ ¬ Commute b c ∧ orderOf (b*c) = 3 := by
  have ht : t ≠ 1 := fun he => hodd (he ▸ map_one sign)
  have hc := cycleType_of_pow_prime_eq_one ht2
  have hn : t.cycleType.card ≤ 3 := by
    have hsum := t.sum_cycleType_le
    rw [hc, Multiset.sum_replicate] at hsum
    simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hsum
    have := n.isLt
    omega
  have hpos := card_cycleType_pos.mpr ht
  have hnot : t.cycleType.card ≠ 2 := by
    intro he
    apply hodd
    rw [sign_of_cycleType', hc, he]
    decide +kernel
  have hcases : t.cycleType.card = 1 ∨ t.cycleType.card = 3 := by omega
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, t.cycleType.card = if k = 0 then 1 else 3 := by
    rcases hcases with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hrep : IsConj (rep n k) t :=
    isConj_of_cycleType_eq ((certificate n k).1.trans (by rw [hc, hk]))
  obtain ⟨g, hg⟩ := isConj_iff.mp hrep
  let e := MulAut.conj g
  obtain ⟨b, c, hb, hc, hbt, hct, hbc, ho⟩ := rep_pair n k
  have he : e (rep n k) = t := hg
  refine ⟨e b, e c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← he]
    exact e.toMonoidHom.map_isConj hb
  · rw [← he]
    exact e.toMonoidHom.map_isConj hc
  · rw [← he]
    exact hbt.map e
  · rw [← he]
    exact hct.map e
  · intro hh
    apply hbc
    exact e.injective (by simpa only [map_mul] using hh.eq)
  · rw [← map_mul, e.orderOf_eq, ho]
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.EqualitySymmetricPair

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
section Transport
variable {G B : Type*} [Group G] [Group B]
private theorem conjugate_comp (V : Subgroup G) (x y : G) :
    (V.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      V.map (MulAut.conj (x*y)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext v
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
  group

private theorem image_conjugate_in (H V : Subgroup G) (hV : V ≤ H) (f : H →* B) (x : H) :
    ((V.map (MulAut.conj (x : G)).toMonoidHom).subgroupOf H).map f =
      ((V.subgroupOf H).map f).map (MulAut.conj (f x)).toMonoidHom := by
  have hs : (V.map (MulAut.conj (x : G)).toMonoidHom).subgroupOf H =
      (V.subgroupOf H).map (MulAut.conj x).toMonoidHom := by
    exact (Subgroup.conj_smul_subgroupOf hV x).symm
  rw [hs, map_map, map_map]
  congr 1
  ext v
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

private theorem image_commute_of_normalizes (H V W : Subgroup G) (f : H →* B)
    (hn : V ≤ normalizer (W : Set G))
    (hc : Nat.card ((W.subgroupOf H).map f) = 2)
    {b c : B} (hb : b ∈ (V.subgroupOf H).map f) (hc' : c ∈ (W.subgroupOf H).map f) :
    Commute b c := by
  apply Commute.symm
  apply normalizer_le_centralizer_of_card_two _ hc ?_ c hc'
  obtain ⟨v, hv, rfl⟩ := hb
  exact (W.subgroupOf H).le_normalizer_map f (mem_map_of_mem _
    (W.le_normalizer_comap H.subtype (hn hv)))
end Transport

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The other literal normalizer index is transported from the inverse conjugator. -/
theorem LocalAnalysis.equality_pair_normalizer_relIndex_right
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R)
    (g : G) (hg : g ∈ centralizer ({z} : Set G))
    (hn : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ normalizer (layer L R : Set G)) :
    ((layer L R).map (MulAut.conj g).toMonoidHom ⊓ normalizer (layer L R : Set G)).relIndex
      ((layer L R).map (MulAut.conj g).toMonoidHom) = 2 := by
  have hi := A.equality_pair_normalizer_relIndex h611 hnatural hz g⁻¹
    ((centralizer ({z} : Set G)).inv_mem hg) (by
      intro h
      apply hn
      have hh := map_mono (f := (MulAut.conj g).toMonoidHom) h
      rw [map_equiv_normalizer_eq, conjugate_comp, mul_inv_cancel] at hh
      simpa using hh)
  rw [← relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) _ _ (MulAut.conj g).injective] at hi
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    map_equiv_normalizer_eq, conjugate_comp, mul_inv_cancel] at hi
  simpa using hi

section Transport
variable {B : Type*} [Group B]
private theorem card_two_elements (W : Subgroup B) (hW : Nat.card W = 2)
    {a : B} (ha : a ∈ W) (ha1 : a ≠ 1) {b : B} (hb : b ∈ W) : b = 1 ∨ b = a := by
  by_cases h : b = 1
  · exact Or.inl h
  · right
    exact congrArg Subtype.val (((Nat.card_eq_two_iff' (1 : W)).mp hW).unique
      (show (⟨b, hb⟩ : W) ≠ 1 from fun he => h (congrArg Subtype.val he))
      (show (⟨a, ha⟩ : W) ≠ 1 from fun he => ha1 (congrArg Subtype.val he)))

private theorem not_two_of_cubic (W : Subgroup B) {b : B} (hb : b ∈ W)
    (ho : orderOf b = 3) : ¬ IsPGroup 2 W := by
  intro hp
  obtain ⟨k, hk⟩ := hp.exists_orderOf_dvd_pow (⟨b, hb⟩ : W)
  rw [← Subgroup.orderOf_coe, ho] at hk
  have hh := Nat.prime_three.dvd_of_dvd_pow hk
  norm_num at hh
end Transport

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- A pair in the centralizer of the marked actor lifts to the literal source
pair, with both normalizer indices and its order-three obstruction. -/
theorem LocalAnalysis.equality_lift_pair
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    (a : EqualityActor z) (ha : a ∈ equalityActorImage z (layer L R)) (ha1 : a ≠ 1)
    (b c : EqualityActor z) (hb : IsConj a b) (hc : IsConj a c)
    (hba : Commute b a) (hca : Commute c a) (hbc : ¬ Commute b c) (ho : orderOf (b*c) = 3) :
    ∃ g x : G, g ∈ centralizer ({z} : Set G) ∧ x ∈ centralizer ({z} : Set G) ∧
      (layer L R ⊓ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)).relIndex
        (layer L R) = 2 ∧
      ((layer L R).map (MulAut.conj g).toMonoidHom ⊓ normalizer (layer L R : Set G)).relIndex
        ((layer L R).map (MulAut.conj g).toMonoidHom) = 2 ∧
      ¬ IsPGroup 2 (layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom : Subgroup G) ∧
      (layer L R ⊔ (layer L R).map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj x).toMonoidHom ≤ centralizer ({z} : Set G) ⊓ M := by
  let H := centralizer ({z} : Set G)
  let V := layer L R
  let f : H →* EqualityActor z := QuotientGroup.mk' (pCore 2 H)
  have hVH : V ≤ H := layer_le_involution_centralizer h611 hz
  have hcard : Nat.card ((V.subgroupOf H).map f) = 2 := A.equalityActorImage_card h611 hnatural hz
  obtain ⟨xb, hxb⟩ := isConj_iff.mp hb
  obtain ⟨yc, hyc⟩ := isConj_iff.mp hc
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (pCore 2 H) xb
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (pCore 2 H) yc
  have hxb' : f x * a * (f x)⁻¹ = b := by simpa only [f, hx] using hxb
  have hyc' : f y * a * (f y)⁻¹ = c := by simpa only [f, hy] using hyc
  let g : G := (x : G)⁻¹ * (y : G)
  let W := V.map (MulAut.conj g).toMonoidHom
  let X := V.map (MulAut.conj (x : G)).toMonoidHom
  let Y := V.map (MulAut.conj (y : G)).toMonoidHom
  have hXY : W.map (MulAut.conj (x : G)).toMonoidHom = Y := by
    rw [conjugate_comp]
    simp only [g, mul_inv_cancel_left]
    rfl
  have hXH : X ≤ H := by
    rintro _ ⟨v, hv, rfl⟩
    exact H.mul_mem (H.mul_mem x.property (hVH hv)) (H.inv_mem x.property)
  have hYH : Y ≤ H := by
    rintro _ ⟨v, hv, rfl⟩
    exact H.mul_mem (H.mul_mem y.property (hVH hv)) (H.inv_mem y.property)
  have hXmap : (X.subgroupOf H).map f =
      ((V.subgroupOf H).map f).map (MulAut.conj (f x)).toMonoidHom :=
    image_conjugate_in H V hVH f x
  have hYmap : (Y.subgroupOf H).map f =
      ((V.subgroupOf H).map f).map (MulAut.conj (f y)).toMonoidHom :=
    image_conjugate_in H V hVH f y
  have hbX : b ∈ (X.subgroupOf H).map f := by
    rw [hXmap, ← hxb']
    exact mem_map_of_mem _ ha
  have hcY : c ∈ (Y.subgroupOf H).map f := by
    rw [hYmap, ← hyc']
    exact mem_map_of_mem _ ha
  have hb1 : b ≠ 1 := fun he => ha1 ((MulAut.conj (f x)).injective
    ((hxb'.trans he).trans (map_one _).symm))
  have hc1 : c ≠ 1 := fun he => ha1 ((MulAut.conj (f y)).injective
    ((hyc'.trans he).trans (map_one _).symm))
  have hXcard : Nat.card ((X.subgroupOf H).map f) = 2 := by
    rw [hXmap, card_map_of_injective (MulAut.conj (f x)).injective, hcard]
  have hYcard : Nat.card ((Y.subgroupOf H).map f) = 2 := by
    rw [hYmap, card_map_of_injective (MulAut.conj (f y)).injective, hcard]
  have hnonleft : ¬ V ≤ normalizer (W : Set G) := by
    intro hh
    have hm := map_mono (f := (MulAut.conj (x : G)).toMonoidHom) hh
    rw [map_equiv_normalizer_eq, hXY] at hm
    exact hbc (image_commute_of_normalizes H X Y f hm hYcard hbX hcY)
  have hnonright : ¬ W ≤ normalizer (V : Set G) := by
    intro hh
    have hm := map_mono (f := (MulAut.conj (x : G)).toMonoidHom) hh
    rw [map_equiv_normalizer_eq, hXY] at hm
    exact hbc (image_commute_of_normalizes H Y X f hm hXcard hcY hbX).symm
  have hlocal (D : Subgroup G) (hDH : D ≤ H) (hDc : Nat.card ((D.subgroupOf H).map f) = 2)
      (d : EqualityActor z) (hd : d ∈ (D.subgroupOf H).map f) (hd1 : d ≠ 1)
      (hda : Commute d a) : D ≤ H ⊓ M := by
    apply le_inf hDH
    apply le_trans ?_ A.normalizer_layer
    intro v hv
    let vH : H := ⟨v, hDH hv⟩
    have hfv : f vH ∈ normalizer ((V.subgroupOf H).map f : Set (EqualityActor z)) := by
      apply Subgroup.centralizer_le_normalizer
      intro w hw
      rcases card_two_elements _ hDc hd hd1 (mem_map_of_mem f (show vH ∈ D.subgroupOf H from hv)) with he | he
      · simp [he]
      rcases card_two_elements _ hcard ha ha1 hw with hw | hw
      · simp [hw]
      · rw [he, hw]
        exact hda.symm.eq
    have hn : vH ∈ (normalizer (equalityActorImage z V : Set (EqualityActor z))).comap f := hfv
    rw [A.equalityActorImage_normalizer_preimage h611 hnatural hz horder hTH hbranch] at hn
    exact hn
  have hpair : (V ⊔ W).map (MulAut.conj (x : G)).toMonoidHom = X ⊔ Y := by
    rw [Subgroup.map_sup, hXY]
  have hpairH : X ⊔ Y ≤ H := sup_le hXH hYH
  have hnot : ¬ IsPGroup 2 (V ⊔ W : Subgroup G) := by
    intro hp
    have hpxy : IsPGroup 2 (X ⊔ Y : Subgroup G) := hpair ▸ hp.map (MulAut.conj (x : G)).toMonoidHom
    have hpimage := hpxy.comap_subtype.map f
    apply not_two_of_cubic (((X ⊔ Y).subgroupOf H).map f) (b := b*c) ?_ ho hpimage
    exact mul_mem (map_mono (subgroupOf_mono H le_sup_left) hbX)
      (map_mono (subgroupOf_mono H le_sup_right) hcY)
  exact ⟨g, x, H.mul_mem (H.inv_mem x.property) y.property, x.property,
    A.equality_pair_normalizer_relIndex h611 hnatural hz g
      (H.mul_mem (H.inv_mem x.property) y.property) hnonleft,
    A.equality_pair_normalizer_relIndex_right h611 hnatural hz g
      (H.mul_mem (H.inv_mem x.property) y.property) hnonright,
    hnot, hpair ▸ sup_le (hlocal X hXH hXcard b hbX hb1 hba)
      (hlocal Y hYH hYcard c hcY hc1 hca)⟩


/-- The symmetric actors in G.6.4 contradict the literal local residual. -/
theorem LocalAnalysis.equality_not_symmetric_actor
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R)
    (m : Fin 2) (e : EqualityActor z ≃* Equiv.Perm (Fin (m.val + 6))) : False := by
  let := A.sourceEqualityVectorQuotient_elementary h611 hz
  obtain ⟨a, ha, ha1, _, _, hgen, _⟩ :=
    A.equality_action_classification h611 hnatural hz horder hTH hbranch
  have ha2 : a ^ 2 = 1 := by
    obtain ⟨v, hv, rfl⟩ := ha
    let := h611.layer_elementary
    have hv2 : v ^ 2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := layer L R) (v : G) hv)
    rw [← map_pow, hv2, map_one]
  let χ : EqualityActor z →* ℤˣ := Equiv.Perm.sign.comp e.toMonoidHom
  have hodd : (e a).sign ≠ 1 := by
    intro he
    have hker : normalClosure ({a} : Set (EqualityActor z)) ≤ χ.ker :=
      normalClosure_le_normal (Set.singleton_subset_iff.mpr he)
    rw [hgen] at hker
    have hsurj : Function.Surjective χ :=
      (Equiv.Perm.sign_surjective (Fin (m.val + 6))).comp e.surjective
    obtain ⟨b, hb⟩ := hsurj (-1)
    have hb1 : χ b = 1 := hker (mem_top b)
    rw [hb] at hb1
    exact (by decide : (-1 : ℤˣ) ≠ 1) hb1
  obtain ⟨b, c, hb, hc, hba, hca, hbc, ho⟩ :=
    EqualitySymmetricPair.exists_pair m (e a) (by rw [← map_pow, ha2, map_one]) hodd
  have hb' : IsConj a (e.symm b) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using e.symm.toMonoidHom.map_isConj hb
  have hc' : IsConj a (e.symm c) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using e.symm.toMonoidHom.map_isConj hc
  have hba' : Commute (e.symm b) a := by
    simpa only [MulEquiv.symm_apply_apply] using hba.map e.symm
  have hca' : Commute (e.symm c) a := by
    simpa only [MulEquiv.symm_apply_apply] using hca.map e.symm
  have hbc' : ¬ Commute (e.symm b) (e.symm c) := by
    intro h
    apply hbc
    simpa only [MulEquiv.apply_symm_apply] using h.map e
  have ho' : orderOf (e.symm b * e.symm c) = 3 := by
    rw [← map_mul, e.symm.orderOf_eq, ho]
  obtain ⟨g, x, hg, hx, hl, hr, hn, hpair⟩ :=
    A.equality_lift_pair h611 hnatural hz horder hTH hbranch a ha ha1
      (e.symm b) (e.symm c) hb' hc' hba' hca' hbc' ho'
  have hmem : z ∈ layer L R ⊓ equalityLocalResidual M z :=
    ⟨hz.1, A.equalityLocalResidual_contains_involution_of_pair hz g hg hl hr hn x hx hpair⟩
  have hd := A.equalityLocalResidual_disjoint_of_symmetric_actor h611 hnatural hz horder
    hTH hbranch (m.val + 4) e
  rw [hd, mem_bot] at hmem
  rw [hmem, orderOf_one] at horder
  norm_num at horder

/-- The actual faithful equality action is the natural two-dimensional binary
linear action. All larger alternatives of the full G.6.4 theorem are excluded. -/
theorem LocalAnalysis.equality_natural_action
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    EqualityNaturalAction A h611 hz := by
  let := A.sourceEqualityVectorQuotient_elementary h611 hz
  rcases A.equality_action_reduced_classification h611 hnatural hz horder hTH hbranch with
    hn | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩
  · exact hn
  · exact (A.equality_not_symmetric_actor h611 hnatural hz horder hTH hbranch
      0 (Subgroup.topEquiv.symm.trans e)).elim
  · exact (A.equality_not_symmetric_actor h611 hnatural hz horder hTH hbranch
      1 (Subgroup.topEquiv.symm.trans e)).elim
  · exact (A.equality_not_symmetric_actor h611 hnatural hz horder hTH hbranch
      0 (Subgroup.topEquiv.symm.trans e)).elim

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
