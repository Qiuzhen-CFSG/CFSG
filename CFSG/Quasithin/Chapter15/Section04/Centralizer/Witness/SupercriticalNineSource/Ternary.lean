module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SupercriticalNineSource.Selection
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer

/-!
# The faithful ternary core action in 15.4.10

The original two-core image centralizes O₅ after the positive-family
exclusion. In the solvable {2,3,5} quotient with trivial two-core, Fitting
is O₃O₅. Its centralizer is contained in its odd core. Thus a two-subgroup
centralizing O₅ acts faithfully on O₃. Nontriviality and supercritical
selection produce the normal ternary source subgroup with its actual action.

Source: Aschbacher--Smith 15.4.10, third paragraph, printed p.1159.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
open FamilySource

/-- The literal quotient by a two-core has trivial two-core. -/
theorem quotient_twoCore_eq_bot {G : Type*} [Group G] [Finite G] (M : Subgroup G) :
    pCore 2 (CoreQuotient M) = ⊥ := by
  let q := quotientMap M
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 M)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have he := q.comap_pCore_of_ker_isPGroup hq hk
  have hm := congrArg (Subgroup.map q) he
  rw [map_comap_eq_self_of_surjective hq] at hm
  exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by
    change pCore 2 M ≤ (QuotientGroup.mk' (pCore 2 M)).ker
    rw [QuotientGroup.ker_mk']))

/-- The original maps identify the ambient and intrinsic descriptions of
the two-core image. -/
theorem core_image_eq {G : Type*} [Group G] (M X : Subgroup G) (hXM : X ≤ M) :
    (pCore 2 X).map ((quotientMap M).comp (inclusion hXM)) = image M (X.pCoreIn 2) := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨inclusion hXM x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨m, ⟨x, hx, hm⟩, rfl⟩
    exact ⟨x, hx, congrArg (quotientMap M) (Subtype.ext hm)⟩

/-- Fitting has exactly its two odd prime cores in the source quotient. -/
theorem fitting_eq_threeCore_sup_fiveCore {Q : Type*} [Group Q] [Finite Q]
    (h2 : pCore 2 Q = ⊥)
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card Q → p = 2 ∨ p = 3 ∨ p = 5) :
    fittingSubgroup Q = pCore 3 Q ⊔ pCore 5 Q := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply le_antisymm ?_ (sup_le (pCore_le_fitting Q 3) (pCore_le_fitting Q 5))
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun p => ?_
  rcases hp p.val.val (Nat.prime_of_mem_primeFactors p.val.property)
    (Nat.dvd_of_mem_primeFactors p.val.property) with h | h | h
  · rw [h, h2]
    exact bot_le
  · rw [h]
    exact le_sup_left
  · rw [h]
    exact le_sup_right

/-- A two-subgroup centralizing O₅ acts faithfully on O₃ in the actual
solvable source quotient. -/
theorem threeCore_action_faithful {Q : Type*} [Group Q] [Finite Q]
    (hs : Group.IsSolvable Q) (h2 : pCore 2 Q = ⊥)
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card Q → p = 2 ∨ p = 3 ∨ p = 5)
    (R : Subgroup Q) (hR : IsPGroup 2 R)
    (hR5 : R ≤ centralizer (pCore 5 Q : Set Q)) :
    Function.Injective ((MulAut.conjNormal : Q →* MulAut (pCore 3 Q)).comp R.subtype) := by
  let a := (MulAut.conjNormal : Q →* MulAut (pCore 3 Q)).comp R.subtype
  apply (MonoidHom.ker_eq_bot_iff a).mp
  apply eq_bot_iff.mpr
  intro r hr
  have h3 (z : Q) (hz : z ∈ pCore 3 Q) : z * (r : Q) = (r : Q) * z := by
    have hh := congrArg (fun c : MulAut (pCore 3 Q) => (c ⟨z, hz⟩ : Q)) hr
    change (r : Q) * z * (r : Q)⁻¹ = z at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hjoin : pCore 3 Q ⊔ pCore 5 Q ≤ centralizer ({(r : Q)} : Set Q) :=
    sup_le (fun z hz => mem_centralizer_singleton_iff.mpr (h3 z hz))
      (fun z hz => mem_centralizer_singleton_iff.mpr ((hR5 r.property) z hz))
  have hrF : (r : Q) ∈ centralizer (fittingSubgroup Q : Set Q) := by
    intro z hz
    exact (mem_centralizer_singleton_iff.mp
      (hjoin ((fitting_eq_threeCore_sup_fiveCore h2 hp).le hz)))
  have hrOdd : (r : Q) ∈ pPrimeCore 2 Q :=
    (fitting_le_pPrimeCore_of_pCore_eq_bot 2 h2)
      (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs hrF)
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  have hcop : Nat.Coprime (Nat.card R) (Nat.card (pPrimeCore 2 Q)) := by
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := Q)).pow_left n
  exact Subtype.ext (Subgroup.disjoint_def.mp (disjoint_of_coprime_natCard hcop) r.property hrOdd)

variable {G : Type*} [Group G] [Finite G]

/-- The first three source reductions select a normal ternary subgroup
with elementary-nine or exponent-three extraspecial shape and nontrivial
original core action. The extraspecial exclusion is the remaining step. -/
theorem exists_ternary_source_shape
    (T : Sylow 2 G) (M X : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M) (hM : HasCharacteristicTwo M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G)
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)))
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (hcounter : ¬ X ≤ centralizer (localV (T : Subgroup G) M : Set G))
    (hs : Group.IsSolvable M)
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3 ∨ p = 5)
    (hr3 : primeRank 3 M ≤ 2) (hr5 : primeRank 5 M ≤ 2)
    (hex : ∀ Y ∈ Chapter1.Xi G (T : Subgroup G), Y ∉ Chapter3.XiPlus G (T : Subgroup G)) :
    ∃ P : Subgroup (CoreQuotient M), ∃ hP : P.Normal,
      Chapter1.XiOddQuotient 3 P ∧ P ≤ pCore 3 (CoreQuotient M) ∧
        (pCore 2 X).map ((@MulAut.conjNormal (CoreQuotient M) _ P hP).comp
          ((quotientMap M).comp (inclusion hXM))) ≠ ⊥ := by
  let Q := CoreQuotient M
  let f := (quotientMap M).comp (inclusion hXM)
  let R := (pCore 2 X).map f
  have hRne : R ≠ ⊥ := by
    dsimp only [R, f]
    rw [core_image_eq]
    exact twoCore_image_ne_bot T M X hTM hXM hM hX hX3 hcounter
  have hR5 : R ≤ centralizer (pCore 5 Q : Set Q) := by
    dsimp only [R, f]
    rw [core_image_eq]
    exact twoCore_image_centralizes_fiveCore T M X _ hTM hXM hM hX hX3 hr5 hex
  let : Group.IsSolvable M := hs
  have hpQ : ∀ p : ℕ, p.Prime → p ∣ Nat.card Q → p = 2 ∨ p = 3 ∨ p = 5 := by
    intro p hp' hd
    exact hp p hp' (hd.trans (card_quotient_dvd_card (pCore 2 M)))
  have hfaith := threeCore_action_faithful (Q := Q) inferInstance (quotient_twoCore_eq_bot M)
    hpQ R (pCore_isPGroup.map f) hR5
  have hmove : (pCore 2 X).map ((MulAut.conjNormal : Q →* MulAut (pCore 3 Q)).comp f) ≠ ⊥ := by
    intro hb
    apply hRne
    apply eq_bot_iff.mpr
    rintro q ⟨x, hx, rfl⟩
    have hh := mem_bot.mp (hb ▸ mem_map_of_mem
      ((MulAut.conjNormal : Q →* MulAut (pCore 3 Q)).comp f) hx)
    have he : (⟨f x, mem_map_of_mem f hx⟩ : R) = 1 := hfaith (by simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_one] using hh)
    exact congrArg Subtype.val he
  have hr : primeRank 3 Q ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 M) pCore_isPGroup).trans hr3
  exact exists_normal_source_shape (Or.inl rfl) hr hX.1.2.1 f hmove

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
