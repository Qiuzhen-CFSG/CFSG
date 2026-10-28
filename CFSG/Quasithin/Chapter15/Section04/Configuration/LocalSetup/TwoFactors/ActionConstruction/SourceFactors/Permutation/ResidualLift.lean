module

public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Lifting the order-three factors by two-residuals

For a specified local quotient with two-group kernel, pull back each
order-three factor and take its two-residual. Residual functoriality retains
the quotient factor and every conjugation relation. The kernel on the lift
is exactly its two-core, giving a compatible quotient isomorphism.

A relatively normal subgroup of a two-perfect group which covers its image
modulo a two-group kernel is the whole group. This gives generation by the
two residual factors and lifts commutator saturation. For distinct invariant
order-three factors, saturation of the whole group already implies saturation
of each factor. If the quotient kernel centralizes V, the actual modules
[V, preimage] and [V, residual preimage] coincide.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
E.2.3(1–2), printed pp.216–217; 15.4.12(5–6), pp.1160–1161; and the first
paragraph of 15.4.18, p.1162. These are conditional lifting lemmas. The actual
quotient, its factor decomposition and its compatible action still have to
be supplied by the source construction; this module does not prove E.2.3
or construct a member of the source Y-family.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G Q : Type*} [Group G] [Group Q] [Finite G]

/-- The actual two-residual of the preimage of a quotient factor. -/
def residualPreimage (q : G →* Q) (A : Subgroup Q) : Subgroup G :=
  (pResidual 2 (A.comap q)).map (A.comap q).subtype

/-- The residual preimage is two-perfect. -/
theorem residualPreimage_perfect (q : G →* Q) (A : Subgroup Q) :
    IsPPerfect 2 (residualPreimage q A) :=
  isPPerfect_embedded_pResidual 2 _

/-- Taking the two-residual preserves the specified two-perfect quotient factor. -/
theorem residualPreimage_image (q : G →* Q) (hq : Function.Surjective q)
    (A : Subgroup Q) (hA : IsPPerfect 2 A) : (residualPreimage q A).map q = A := by
  rw [residualPreimage, map_embedded_pResidual,
    map_comap_eq_self_of_surjective hq, (pResidual_eq_top_iff 2 A).mpr hA,
    ← MonoidHom.range_eq_map, range_subtype]

omit [Finite G] in
private theorem comap_conj (q : G →* Q) (A : Subgroup Q) (g : G) :
    (A.comap q).map (MulAut.conj g).toMonoidHom =
      (A.map (MulAut.conj (q g)).toMonoidHom).comap q := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_map.mpr ⟨q y, hy, by simp [MulAut.conj_apply]⟩
  · intro hx
    obtain ⟨y, hy, he⟩ := mem_map.mp hx
    refine mem_map.mpr ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    change q (g⁻¹ * x * g) ∈ A
    have he' : q g * y * (q g)⁻¹ = q x := he
    rw [map_mul, map_mul, map_inv, ← he']
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hy

/-- Conjugation of residual preimages agrees with conjugation through the given quotient map. -/
theorem residualPreimage_conj (q : G →* Q) (A : Subgroup Q) (g : G) :
    (residualPreimage q A).map (MulAut.conj g).toMonoidHom =
      residualPreimage q (A.map (MulAut.conj (q g)).toMonoidHom) := by
  rw [residualPreimage, map_embedded_pResidual, comap_conj]
  rfl

/-- Normalization of a quotient factor lifts to its residual preimage. -/
theorem residualPreimage_normalized (q : G →* Q) (A : Subgroup Q) (U : Subgroup G)
    (hn : U.map q ≤ normalizer (A : Set Q)) :
    U ≤ normalizer (residualPreimage q A : Set G) := by
  intro u hu
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (residualPreimage q A).map (MulAut.conj u).toMonoidHom = _
  rw [residualPreimage_conj]
  exact congrArg (residualPreimage q)
    (mem_normalizer_iff_map_conj_eq.mp (hn (mem_map.mpr ⟨u, hu, rfl⟩)))

omit [Finite G] in
/-- A quotient factor inside the image of a normal two-perfect group lifts inside that group. -/
theorem residualPreimage_le (q : G →* Q) (hk : IsPGroup 2 q.ker)
    (X : Subgroup G) (hp : IsPPerfect 2 X)
    (hn : q.ker ≤ normalizer (X : Set G))
    {A : Subgroup Q} (hA : A ≤ X.map q) : residualPreimage q A ≤ X := by
  have hc : A.comap q ≤ X ⊔ q.ker := by
    simpa only [comap_map_eq] using comap_mono (f := q) hA
  exact (embedded_pResidual_mono 2 hc).trans_eq
    (embedded_pResidual_join_pGroup X q.ker hp hk hn)

/-- A group of order three has no nontrivial two-group quotient. -/
theorem three_isPPerfect (A : Subgroup Q) (hA : Nat.card A = 3) : IsPPerfect 2 A := by
  apply (pResidual_eq_top_iff 2 A).mp
  apply top_unique
  intro a _
  apply mem_pResidual_of_orderOf_coprime
  exact (show Nat.Coprime 2 3 by decide).of_dvd_right (hA ▸ orderOf_dvd_natCard a)

/-- The intrinsic two-core quotient is the selected order-three factor, compatibly with the original map. -/
theorem residualPreimage_quotient (q : G →* Q) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (A : Subgroup Q) (hA : Nat.card A = 3) :
    ∃ e : residualPreimage q A ⧸ pCore 2 (residualPreimage q A) ≃* A,
      ∀ x : residualPreimage q A,
        (e (QuotientGroup.mk' (pCore 2 (residualPreimage q A)) x) : Q) = q x := by
  let L := residualPreimage q A
  have him : L.map q = A := residualPreimage_image q hq A (three_isPPerfect A hA)
  let f := q.subgroupMap L
  have hf := q.subgroupMap_surjective L
  have hfk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let _ : Finite (L.map q) := Finite.of_surjective _ hf
  have hc : Nat.card (L.map q) = 3 := him ▸ hA
  have hp3 : IsPGroup 3 (L.map q) := IsPGroup.of_card (n := 1) (by simpa using hc)
  have hcore : pCore 2 (L.map q) = ⊥ := by
    have hd := IsPGroup.disjoint_of_coprime (pCore_isPGroup (p := 2))
      (hp3.to_subgroup ⊤) (by decide : Nat.Coprime 2 3)
    simpa using hd
  have hker : f.ker = pCore 2 L := by
    simpa only [hcore, MonoidHom.comap_bot] using f.comap_pCore_of_ker_isPGroup hf hfk
  let e : L ⧸ pCore 2 L ≃* A :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).trans (MulEquiv.subgroupCongr him))
  exact ⟨e, fun x => rfl⟩

/-- The residual preimage has two-core quotient of order three. -/
theorem residualPreimage_quotient_card (q : G →* Q) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (A : Subgroup Q) (hA : Nat.card A = 3) :
    Nat.card (residualPreimage q A ⧸ pCore 2 (residualPreimage q A)) = 3 := by
  obtain ⟨e, _⟩ := residualPreimage_quotient q hq hk A hA
  exact (Nat.card_congr e.toEquiv).trans hA

omit [Finite G] in
private theorem perfect_le_normal_of_map_le
    (q : G →* Q) (hk : IsPGroup 2 q.ker) (X N : Subgroup G) [N.Normal]
    (hp : IsPPerfect 2 X) (hi : X.map q ≤ N.map q) : X ≤ N := by
  let f := QuotientGroup.mk' N
  have hle : X ≤ N ⊔ q.ker := by
    simpa only [comap_map_eq] using (le_comap_map q X).trans (comap_mono hi)
  have hfi : X.map f ≤ q.ker.map f := by
    simpa only [Subgroup.map_sup, f, QuotientGroup.map_mk'_self, bot_sup_eq] using
      map_mono (f := f) hle
  have hfp : IsPPerfect 2 (X.map f) :=
    hp.of_surjective (f.subgroupMap X) (f.subgroupMap_surjective X)
  have hfg : IsPGroup 2 (X.map f) := (hk.map f).to_le hfi
  have he := hfp ⊥ inferInstance
    (hfg.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥))
  have hb : X.map f = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hh : (⟨x, hx⟩ : X.map f) ∈ (⊥ : Subgroup (X.map f)) := he ▸ mem_top _
    exact congrArg Subtype.val (mem_bot.mp hh)
  simpa only [Subgroup.map_eq_bot_iff, f, QuotientGroup.ker_mk'] using hb

omit [Finite G] in
/-- A relatively normal subgroup covering a two-perfect group modulo a two-group kernel is the whole group. -/
theorem eq_of_perfect_of_map_eq (q : G →* Q) (hk : IsPGroup 2 q.ker)
    {X N : Subgroup G} (hp : IsPPerfect 2 X) (hNX : N ≤ X)
    (hn : X ≤ normalizer (N : Set G)) (he : N.map q = X.map q) : N = X := by
  let f := q.comp X.subtype
  let R := N.subgroupOf X
  let _ : R.Normal := (normal_subgroupOf_iff_le_normalizer hNX).mpr hn
  have hf : IsPGroup 2 f.ker := hk.comap_subtype
  have htop : IsPPerfect 2 (⊤ : Subgroup X) :=
    hp.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).symm.toMonoidHom
      (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).symm.surjective
  have him : (⊤ : Subgroup X).map f ≤ R.map f := by
    have hh : R.map f = N.map q := by
      rw [← map_map, map_subgroupOf_eq_of_le hNX]
    rw [hh, he, ← map_map, ← MonoidHom.range_eq_map, range_subtype]
  have hb := perfect_le_normal_of_map_le f hf ⊤ R htop him
  have hh := congrArg (Subgroup.map X.subtype) (top_unique hb)
  simpa only [R, map_subgroupOf_eq_of_le hNX, ← MonoidHom.range_eq_map,
    range_subtype] using hh

/-- The two lifted residual factors generate the specified two-perfect group. -/
theorem residualPreimage_pair_join (q : G →* Q) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (X : Subgroup G) (hp : IsPPerfect 2 X)
    (hX : q.ker ≤ normalizer (X : Set G)) (A : Bool → Subgroup Q)
    (hA : ∀ i, Nat.card (A i) = 3) (hgen : A false ⊔ A true = X.map q)
    (hn : ∀ i, X.map q ≤ normalizer (A i : Set Q)) :
    residualPreimage q (A false) ⊔ residualPreimage q (A true) = X := by
  have hl (i : Bool) : residualPreimage q (A i) ≤ X := by
    apply residualPreimage_le q hk X hp hX
    rw [← hgen]
    cases i
    · exact le_sup_left
    · exact le_sup_right
  apply eq_of_perfect_of_map_eq q hk hp (sup_le (hl false) (hl true))
  · exact (le_inf (residualPreimage_normalized q (A false) X (hn false))
      (residualPreimage_normalized q (A true) X (hn true))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · rw [Subgroup.map_sup, residualPreimage_image q hq _ (three_isPPerfect _ (hA false)),
      residualPreimage_image q hq _ (three_isPPerfect _ (hA true)), hgen]

/-- A full quotient commutator lifts to a full commutator in the residual preimage. -/
theorem residualPreimage_commutator (q : G →* Q) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (A : Subgroup Q) (hA : Nat.card A = 3)
    (J : Subgroup G) (hn : J.map q ≤ normalizer (A : Set Q))
    (hc : ⁅A, J.map q⁆ = A) : ⁅residualPreimage q A, J⁆ = residualPreimage q A := by
  apply eq_of_perfect_of_map_eq q hk (residualPreimage_perfect q A)
    (le_normalizer_iff_commutator_le_left.mp (residualPreimage_normalized q A J hn))
    (normalizer_commutator_ge_left _ _)
  rw [map_commutator, residualPreimage_image q hq A (three_isPPerfect A hA), hc]

omit [Finite G] in
private theorem prime_factor_commutator (A B J : Subgroup G)
    (hA : Nat.card A = 3) (hB : Nat.card B = 3) (hne : A ≠ B)
    (hn : A ⊔ B ≤ normalizer (B : Set G))
    (hJA : J ≤ normalizer (A : Set G)) (hJB : J ≤ normalizer (B : Set G))
    (hc : ⁅A ⊔ B, J⁆ = A ⊔ B) : ⁅A, J⁆ = A := by
  let _ : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; decide)
  have hle : ⁅A, J⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp hJA
  have hnonzero : ⁅A, J⁆ ≠ ⊥ := by
    intro hb
    have hpre : A ⊔ B ≤ commutatorPreimage (A ⊔ B) J B :=
      sup_le (le_commutatorPreimage le_sup_left (hb ▸ bot_le))
        (le_commutatorPreimage le_sup_right
          (le_normalizer_iff_commutator_le_left.mp hJB))
    have hbound : A ⊔ B ≤ B := hc ▸
      (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hn)
    exact hne (eq_of_le_of_card_ge (le_sup_left.trans hbound) (by rw [hA, hB]))
  let _ : Fact (Nat.card A).Prime := ⟨hA ▸ by decide⟩
  rcases (⁅A, J⁆.subgroupOf A).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have hh := congrArg (Subgroup.map A.subtype) hb
    rw [map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at hh
    exact (hnonzero hh).elim
  · have hh := congrArg (Subgroup.map A.subtype) ht
    simpa only [map_subgroupOf_eq_of_le hle, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- Whole-group commutator saturation forces saturation in each distinct invariant order-three factor, then in its residual lift. -/
theorem residualPreimage_pair_commutator (q : G →* Q) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (X J : Subgroup G) (A : Bool → Subgroup Q)
    (hA : ∀ i, Nat.card (A i) = 3) (hinj : Function.Injective A)
    (hgen : A false ⊔ A true = X.map q)
    (hn : ∀ i, X.map q ≤ normalizer (A i : Set Q))
    (hJ : ∀ i, J.map q ≤ normalizer (A i : Set Q)) (hc : ⁅X, J⁆ = X) :
    ∀ i, ⁅residualPreimage q (A i), J⁆ = residualPreimage q (A i) := by
  have him : ⁅A false ⊔ A true, J.map q⁆ = A false ⊔ A true := by
    rw [hgen, ← map_commutator, hc]
  have hne : A false ≠ A true := fun he => Bool.false_ne_true (hinj he)
  intro i
  apply residualPreimage_commutator q hq hk _ (hA i) J (hJ i)
  cases i with
  | false =>
      exact prime_factor_commutator _ _ _ (hA false) (hA true) hne
        (hgen ▸ hn true) (hJ false) (hJ true) him
  | true =>
      exact prime_factor_commutator _ _ _ (hA true) (hA false) hne.symm
        (by simpa only [sup_comm] using hgen ▸ hn false) (hJ true) (hJ false)
        (by simpa only [sup_comm] using him)

/-- A centralizing kernel makes the preimage and its two-residual have the same actual commutator module. -/
theorem residualPreimage_module (q : G →* Q) (hq : Function.Surjective q)
    (A : Subgroup Q) (hA : Nat.card A = 3) (V : Subgroup G)
    (hkV : q.ker ≤ centralizer (V : Set G))
    (hnV : A.comap q ≤ normalizer (V : Set G)) :
    ⁅V, residualPreimage q A⁆ = ⁅V, A.comap q⁆ := by
  have hgen : q.ker ⊔ residualPreimage q A = A.comap q := by
    have hh := congrArg (Subgroup.comap q)
      (residualPreimage_image q hq A (three_isPPerfect A hA))
    simpa only [comap_map_eq, sup_comm] using hh
  exact commutator_eq_of_centralizing_sup hgen hkV ((map_subtype_le _).trans hnV)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.SourceFactors.Permutation
