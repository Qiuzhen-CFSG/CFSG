module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Setup
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.FittingPrimes

/-!
# The normalizer image in the two-prime Thompson argument

When XR factors through the normalizer of J(R) and the centralizer of
Ω₁(Z(R)), both factors contain R. Splitting an element into its X and R
parts proves that one intersection with X has nonzero image modulo
O₂,Φ(X). Irreducibility on the actual iterated quotient, followed by
Frattini nongeneration, makes that intersection all of X. Commutator
generation then puts X in N_L(C)^∞.

The final theorem applies the full universal B.2.16 alternatives, excludes
the exceptional alternative by prime support, and transfers both prescribed
odd Fitting primes to F(N_L(C)^∞/O₂(N_L(C)^∞)). In the source's distinct-prime
case this constructs the required characteristic subgroup with two odd
Fitting primes. Quotient nontriviality follows from the original Fitting prime.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed p.513. The universal B.2.16 theorem, the earlier
local characteristic-two condition, and the residual containment and action
statements remain explicit inputs to be discharged by the source-theorem owner.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
universe u
variable {G : Type u} [Group G] [Finite G]

open scoped Pointwise
omit [Finite G] in
private theorem factor_le_sup (X R N F : Subgroup G)
    (hRX : R ≤ normalizer (X : Set G)) (hRN : R ≤ N)
    (hNF : X ⊓ N ≤ F) : (X ⊔ R) ⊓ N ≤ F ⊔ R := by
  intro g hg
  have hgXR : g ∈ ((X ⊔ R : Subgroup G) : Set G) := hg.1
  rw [coe_mul_of_right_le_normalizer_left X R hRX] at hgXR
  obtain ⟨x, hx, r, hr, rfl⟩ := hgXR
  have hxN : x ∈ N := by
    simpa using N.mul_mem hg.2 (N.inv_mem (hRN hr))
  exact (F ⊔ R).mul_mem (Subgroup.mem_sup_left (hNF ⟨hx, hxN⟩)) (Subgroup.mem_sup_right hr)

omit [Finite G] in
/-- In a factorization of XR by two overgroups of R, at least one factor
has nonzero intersection image in X/F. The escape cannot be supplied by R. -/
theorem factorization_intersection_not_le (X R F N₁ N₂ : Subgroup G)
    (hRX : R ≤ normalizer (X : Set G)) (hRF : R ≤ normalizer (F : Set G))
    (hFX : F ≤ X) (hXR : X ⊓ R ≤ F) (hproper : ¬ X ≤ F)
    (hR₁ : R ≤ N₁) (hR₂ : R ≤ N₂)
    (hfactor : ((X ⊔ R : Subgroup G) : Set G) =
      (((X ⊔ R) ⊓ N₁ : Subgroup G) : Set G) *
      (((X ⊔ R) ⊓ N₂ : Subgroup G) : Set G)) :
    ¬ X ⊓ N₁ ≤ F ∨ ¬ X ⊓ N₂ ≤ F := by
  by_contra! hn
  have h₁ := factor_le_sup X R N₁ F hRX hR₁ hn.1
  have h₂ := factor_le_sup X R N₂ F hRX hR₂ hn.2
  have hle : X ⊔ R ≤ F ⊔ R := by
    intro x hx
    change x ∈ ((X ⊔ R : Subgroup G) : Set G) at hx
    rw [hfactor] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact (F ⊔ R).mul_mem (h₁ ha) (h₂ hb)
  apply hproper
  intro x hx
  have hm : x ∈ ((F ⊔ R : Subgroup G) : Set G) := hle (Subgroup.mem_sup_left hx)
  rw [coe_mul_of_right_le_normalizer_left F R hRF] at hm
  obtain ⟨f, hf, r, hr, hfr⟩ := hm
  have hrX : r ∈ X := by
    have hh := X.mul_mem (X.inv_mem (hFX hf)) hx
    rw [← hfr, inv_mul_cancel_left] at hh
    exact hh
  rw [← hfr]
  exact F.mul_mem hf (hXR ⟨hrX, hr⟩)

/-- Irreducibility on the iterated quotient converts a nonzero normalizer
intersection into normalization of the characteristic subgroup. -/
theorem le_normalizer_of_irreducible (X Y C : Subgroup G)
    (hYX : Y ≤ normalizer (X : Set G)) (hYC : Y ≤ normalizer (C : Set G))
    (hcore : X.pCoreIn 2 ≤ normalizer (C : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ y : Y, ∀ a ∈ A, xiFrattiniAction Y X hYX y a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hne : ¬ X ⊓ normalizer (C : Set G) ≤ twoFrattini X) :
    X ≤ normalizer (C : Set G) := by
  let N := normalizer (C : Set G)
  let A := (X ⊓ N).subgroupOf X
  let f : X →* XiFrattiniQuotient X :=
    (QuotientGroup.mk' (frattini (XiQuotient X))).comp
      (QuotientGroup.mk' (pCore 2 X))
  have hker : f.ker = twoFrattiniIn X := by
    ext x
    exact QuotientGroup.eq_one_iff _
  let _ := conjMulDistribMulActionOfLeNormalizer Y X hYX
  have hstable : ∀ y : Y, ∀ a ∈ A.map f,
      xiFrattiniAction Y X hYX y a ∈ A.map f := by
    rintro y a ⟨x, hx, rfl⟩
    refine ⟨(MulDistribMulAction.toMulAut Y X y) x, ?_, ?_⟩
    · refine ⟨((MulDistribMulAction.toMulAut Y X y) x).property, ?_⟩
      change (y : G) * (x : G) * (y : G)⁻¹ ∈ N
      exact N.mul_mem (N.mul_mem (hYC y.property) hx.2) (N.inv_mem (hYC y.property))
    · simp only [f, xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk]
  rcases hirr (A.map f) hstable with hb | ht
  · exfalso
    apply hne
    intro x hx
    have hxk : (⟨x, hx.1⟩ : X) ∈ f.ker := (Subgroup.map_eq_bot_iff A).mp hb hx
    rw [hker] at hxk
    exact mem_map.mpr ⟨⟨x, hx.1⟩, hxk, rfl⟩
  · have hsup : (X ⊓ N) ⊔ twoFrattini X = X := by
      have hh := congrArg (comap f) ht
      rw [comap_map_eq, hker, comap_top] at hh
      have hm := congrArg (map X.subtype) hh
      simpa only [A, Subgroup.map_sup, map_subgroupOf_eq_of_le inf_le_left,
        ← MonoidHom.range_eq_map, range_subtype, twoFrattini] using hm
    have he := eq_of_sup_twoFrattini X (X ⊓ N) inf_le_left
      (le_inf (pCoreIn_le 2 X) hcore) hsup
    exact he ▸ inf_le_right

omit [Finite G] in
/-- Commutator generation puts a normalized radical factor in the actual
solvable residual of its characteristic-subgroup normalizer. -/
theorem XiP_le_normalizerResidual_of_commutator (p q : ℕ) (L T : Subgroup G)
    (C : Subgroup (radicalCore p L T)) [C.Characteristic]
    (hXC : XiP q L ≤ normalizer (C.map (radicalCore p L T).subtype : Set G))
    (hcomm : ⁅XiP q L, normalizerResidual L (radicalCore p L T)⁆ = XiP q L) :
    XiP q L ≤ normalizerResidual L (C.map (radicalCore p L T).subtype) := by
  rw [← hcomm]
  apply (commutator_mono le_rfl (normalizerResidual_le_of_characteristic L _ C)).trans
  exact le_normalizer_iff_commutator_le_right.mp
    (le_normalizer_normalizerResidual ((XiP_le q L).trans L.le_normalizer) hXC)

omit [Finite G] in
private theorem le_centralizer_omegaCenterIn (R : Subgroup G) :
    R ≤ centralizer ((omegaCenterIn R).map R.subtype : Set G) := by
  intro r hr
  apply mem_centralizer_iff.mpr
  rintro z ⟨a, ⟨b, hb, rfl⟩, rfl⟩
  exact congrArg Subtype.val ((mem_center_iff.mp b.property) (⟨r, hr⟩ : R)).symm

/-- The factorization yields a nonzero image of X_q ∩ N_G(C) in the
actual Frattini quotient. In particular, elements from R alone do not suffice. -/
theorem exists_thompsonChoice_nonzero (p q : ℕ) [Fact q.Prime] (hq : Odd q)
    (L T : Subgroup G) (hT : T ≤ normalizer (L : Set G))
    [Nontrivial (XiQuotient (XiP q L))]
    (hf : ThompsonFactorization (XiP q L) (radicalCore p L T)) :
    ∃ C : Subgroup (radicalCore p L T), IsThompsonChoice (radicalCore p L T) C ∧
      ¬ XiP q L ⊓ normalizer (C.map (radicalCore p L T).subtype : Set G) ≤
        twoFrattini (XiP q L) := by
  let X := XiP q L
  let R := radicalCore p L T
  have hRX := radicalCore_normalizes_XiP p q hT
  have hN := factorization_intersection_not_le X R (twoFrattini X)
    (normalizer ((elementaryThompsonIn R).map R.subtype : Set G))
    (centralizer ((omegaCenterIn R).map R.subtype : Set G)) hRX
    (hRX.trans (normalizer_le_normalizer_twoFrattini X)) (twoFrattini_le X)
    ((XiP_inf_twoGroup_le_core q hq L R (radicalCore_isTwoGroup p L T)).trans
      (twoCore_le_twoFrattini X)) (not_le_twoFrattini X)
    (R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R _))
    (le_centralizer_omegaCenterIn R) hf
  rcases hN with hJ | hZ
  · exact ⟨elementaryThompsonIn R, Or.inl rfl, hJ⟩
  · refine ⟨omegaCenterIn R, Or.inr rfl, fun hh => hZ ?_⟩
    exact (inf_le_inf_left X (Subgroup.centralizer_le_normalizer _)).trans hh

/-- The characteristic-subgroup construction from the exact factorization.
The final theorem below supplies this factorization from B.2.16.
Irreducibility and commutator generation are the residual owner's conclusions. -/
theorem exists_thompsonChoice_contains_radicals_of_factorization
    (p q : ℕ) [Fact q.Prime] (hq : Odd q) (L T : Subgroup G)
    (hL : L ∈ Chapter1.L G T) (hT : T ≤ normalizer (L : Set G))
    [Nontrivial (XiQuotient (XiP q L))]
    (hX : XiP p L ≤ normalizerResidual L (radicalCore p L T))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
      (∀ y : normalizerResidual L (radicalCore p L T), ∀ a ∈ A,
        xiFrattiniAction _ _ (Y_normalizes_XiP p q L T) y a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hcomm : ⁅XiP q L, normalizerResidual L (radicalCore p L T)⁆ = XiP q L)
    (hf : ThompsonFactorization (XiP q L) (radicalCore p L T)) :
    ∃ C : Subgroup (radicalCore p L T), IsThompsonChoice (radicalCore p L T) C ∧
      C ≠ ⊥ ∧ C.Characteristic ∧
      (¬ XiP q L ⊓ normalizer (C.map (radicalCore p L T).subtype : Set G) ≤
        twoFrattini (XiP q L)) ∧
      XiP p L ≤ normalizerResidual L (C.map (radicalCore p L T).subtype) ∧
      XiP q L ≤ normalizerResidual L (C.map (radicalCore p L T).subtype) := by
  obtain ⟨C, hC, hn⟩ := exists_thompsonChoice_nonzero p q hq L T hT hf
  let : C.Characteristic := hC.characteristic
  have hRN := (radicalCore p L T).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (radicalCore p L T) C)
  have hXC : XiP q L ≤ normalizer (C.map (radicalCore p L T).subtype : Set G) :=
    le_normalizer_of_irreducible (XiP q L) _ _ (Y_normalizes_XiP p q L T)
      ((normalizerResidual_le_normalizer _ _).trans
        (normalizer_le_normalizer_characteristic_image _ C))
      ((twoCore_XiP_le_radicalCore p q hL.2.1 hT).trans hRN) hirr hn
  exact ⟨C, hC, hC.ne_bot (radicalCore_isTwoGroup p L T) (radicalCore_ne_bot p hL),
    inferInstance, hn, hX.trans (normalizerResidual_le_of_characteristic L _ C),
    XiP_le_normalizerResidual_of_commutator p q L T C hXC hcomm⟩

/-- The two-prime construction on p.513, using the exact universal B.2.16.
The witness is a nontrivial characteristic J(R) or Ω₁(Z(R)); its normalizer
intersection has nonzero image in the actual Frattini quotient, and its
normalizer residual contains both radical factors and retains both specified
odd Fitting primes. Distinctness of p and q is needed only when interpreting
these divisibilities as two distinct primes.

The local characteristic-two input and the three residual inputs are the
earlier source obligations. Factorization and quotient nontriviality are
proved here from B.2.16 and the original Fitting-prime hypotheses. -/
theorem exists_thompsonChoice_fittingPrimes_of_B216 (hB : ThompsonSource.TheoremB216.{u})
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : Odd p) (hq : Odd q) (hlarge : 5 ≤ q)
    (L T : Subgroup G) (hL : L ∈ Chapter1.L G T)
    (hT : T ≤ normalizer (L : Set G))
    (hlocal : HOver G (T : Set G) ⊆ He G)
    (hpdiv : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hqdiv : q ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hX : XiP p L ≤ normalizerResidual L (radicalCore p L T))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP q L)),
      (∀ y : normalizerResidual L (radicalCore p L T), ∀ a ∈ A,
        xiFrattiniAction _ _ (Y_normalizes_XiP p q L T) y a ∈ A) → A = ⊥ ∨ A = ⊤)
    (hcomm : ⁅XiP q L, normalizerResidual L (radicalCore p L T)⁆ = XiP q L) :
    ∃ C : Subgroup (radicalCore p L T), IsThompsonChoice (radicalCore p L T) C ∧
      C ≠ ⊥ ∧ C.Characteristic ∧
      (¬ XiP q L ⊓ normalizer (C.map (radicalCore p L T).subtype : Set G) ≤
        twoFrattini (XiP q L)) ∧
      XiP p L ≤ normalizerResidual L (C.map (radicalCore p L T).subtype) ∧
      XiP q L ≤ normalizerResidual L (C.map (radicalCore p L T).subtype) ∧
      p ∣ Nat.card (fittingSubgroup
        (XiQuotient (normalizerResidual L (C.map (radicalCore p L T).subtype)))) ∧
      q ∣ Nat.card (fittingSubgroup
        (XiQuotient (normalizerResidual L (C.map (radicalCore p L T).subtype)))) := by
  let := XiP_quotient_nontrivial_of_fittingPrime q hq hqdiv
  have hf := thompsonFactorization_of_B216 hB p q hq hlarge hL hT hlocal
  obtain ⟨C, hC, hne, hchar, hn, hpC, hqC⟩ :=
    exists_thompsonChoice_contains_radicals_of_factorization p q hq L T hL hT
      hX hirr hcomm hf
  exact ⟨C, hC, hne, hchar, hn, hpC, hqC,
    fittingPrimes_dvd_of_XiP_le p q hp hq hpdiv hqdiv hpC hqC
      (normalizerResidual_le L _)⟩

end CFSG.Quasithin.Chapter1.RadicalNormalizers
