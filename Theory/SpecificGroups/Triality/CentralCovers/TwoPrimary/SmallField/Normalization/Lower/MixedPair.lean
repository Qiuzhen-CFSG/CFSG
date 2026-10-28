module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.Lower.Relations
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.ShortRoots.Additivity
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.ShortRoots.Model

/-!
# The mixed lower exchange in the smallest triality cover

Assume arms-torus normalization, the commuting pairs, the upper collection
relations and the exact short–short exchange. Upper correction words collect
into the last two long roots; uniqueness of the genuine positive coordinates
recovers their precise trace coefficients. These trace formulas and the
short–short exchange prove additivity of the mixed polynomial word, including
cancellation of its highest-root term.

An arms actor of order seven fixes all long sections and scales the three
short sections by a², a² and a⁻¹. The identities a⁶ = a⁻¹ and N(a²s) = N(s)
make the polynomial word equivariant. Scalar-equivariant uniqueness in a
central extension identifies it with actual conjugation. The base identity
is `RootSections.ShortPolynomial.base_mixed`, proved by the checked D₄
sum/nonsum calculation in `LargeFields/Exchanges/ShortRoots/Model.lean`.

This discharges the mixed calculation in `exists_lowerNormalized_of_torus_calculations`;
the short–short identity remains the explicit hypothesis of this conditional result.
Sources: GLS3 §2.4.5(b)(5) and §6.1; Aschbacher–Smith A.2.4 and I.1.3
(`refs/quasithin.pdf`, PDF pp.44 and 418).
-/

public section

open Triality.Standard PerfectCentralCovering
open Triality.Standard.Parabolics Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.CentralCovers.TwoPrimary.RootSections.ShortPolynomial
set_option linter.unusedSimpArgs false
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField.LowerNormalization
noncomputable section
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
variable {E : Type*} [Group E] {f : E →* G}

private def sp (s : ExtensionField P) : PositiveParameters 1 Nat.zero_lt_one :=
  (fun _ => s, 0)
private def lp (s : fixedField P) : PositiveParameters 1 Nat.zero_lt_one :=
  (0, fun _ => s)

private theorem commutingRelations (M : RootSections 1 Nat.zero_lt_one f)
    (hc : CommutingPairs M) : M.CommutingRelations := by
  constructor
  · intro s t; exact hc 0 4 (sp s) (lp t) (by decide) (by unfold interactingPair; decide)
  · intro s t; exact hc 0 5 (sp s) (lp t) (by decide) (by unfold interactingPair; decide)
  · intro s t; exact hc 1 2 (lp s) (sp t) (by decide) (by unfold interactingPair; decide)
  · intro s t; exact hc 1 3 (lp s) (sp t) (by decide) (by unfold interactingPair; decide)
  · intro s t; exact hc 1 5 (lp s) (lp t) (by decide) (by unfold interactingPair; decide)
  · intro s t; exact hc 2 4 (sp s) (lp t) (by decide) (by unfold interactingPair; decide)
  · intro s t; exact hc 2 5 (sp s) (lp t) (by decide) (by unfold interactingPair; decide)
  · intro s t; exact hc 3 4 (sp s) (lp t) (by decide) (by unfold interactingPair; decide)
  · intro s t; exact hc 3 5 (sp s) (lp t) (by decide) (by unfold interactingPair; decide)
  · intro s t; exact hc 4 5 (lp s) (lp t) (by decide) (by unfold interactingPair; decide)

private theorem tail_word (M : RootSections 1 Nat.zero_lt_one f)
    (hc : M.CommutingRelations) (w : List (Fin 6 × PositiveParameters 1 Nat.zero_lt_one))
    (hw : ∀ z ∈ w, 3 < height z.1) :
    ∃ a b, FilteredCollection.wordProduct M.factor w = M.longValue 1 a * M.longValue 2 b := by
  induction w with
  | nil => exact ⟨0, 0, by simp [FilteredCollection.wordProduct, RootSections.longValue]⟩
  | cons z w ih =>
    obtain ⟨a, b, hab⟩ := ih (fun x hx => hw x (List.mem_cons_of_mem z hx))
    have hz := hw z (List.mem_cons_self)
    rcases z with ⟨i, v⟩
    fin_cases i <;> simp [height] at hz
    · refine ⟨v.2 1 + a, b, ?_⟩
      change M.longValue 1 (v.2 1) * FilteredCollection.wordProduct M.factor w = _
      rw [hab, ← mul_assoc, ← RootSections.ShortPolynomial.long_add]
    · refine ⟨a, v.2 2 + b, ?_⟩
      change M.longValue 2 (v.2 2) * FilteredCollection.wordProduct M.factor w = _
      rw [hab, (hc.long1_long2 a (v.2 2)).symm.left_comm, ← RootSections.ShortPolynomial.long_add]

private theorem tail_eq_of_project (M : RootSections 1 Nat.zero_lt_one f)
    (a b c d : fixedField P)
    (h : f (M.longValue 1 a * M.longValue 2 b) =
      f (M.longValue 1 c * M.longValue 2 d)) :
    M.longValue 1 a * M.longValue 2 b = M.longValue 1 c * M.longValue 2 d := by
  have he : baseProduct 1 Nat.zero_lt_one (0, ![0,a,b]) =
      baseProduct 1 Nat.zero_lt_one (0, ![0,c,d]) := by
    rw [← M.project_product, ← M.project_product]
    simpa [RootSections.product, RootSections.factor, List.ofFn_succ,
      RootSections.longValue] using h
  have hv := baseProduct_injective 1 Nat.zero_lt_one he
  have ha : a = c := congrArg (fun v => v.2 1) hv
  have hb : b = d := congrArg (fun v => v.2 2) hv
  rw [ha, hb]

private theorem exchange_of_projection (M : RootSections 1 Nat.zero_lt_one f)
    (hc : M.CommutingRelations) {i j : Fin 6} (hh : 3 ≤ max (height i) (height j))
    (he : PairExchange M i j) (v w : PositiveParameters 1 Nat.zero_lt_one)
    (a b : fixedField P)
    (hp : f (M.factor i v * M.factor j w) =
      f (M.factor j w * M.factor i v * (M.longValue 1 a * M.longValue 2 b))) :
    M.factor i v * M.factor j w =
      M.factor j w * M.factor i v * (M.longValue 1 a * M.longValue 2 b) := by
  obtain ⟨l, hl, he⟩ := he v w
  obtain ⟨c, d, hcd⟩ := tail_word M hc l (fun z hz => lt_of_le_of_lt hh (hl z hz))
  rw [hcd] at he
  have hp' : f (M.longValue 1 c * M.longValue 2 d) =
      f (M.longValue 1 a * M.longValue 2 b) := by
    rw [he] at hp
    simp only [map_mul] at hp ⊢
    exact mul_left_cancel hp
  rw [tail_eq_of_project M c d a b hp'] at he
  exact he

private theorem upper_trace (M : RootSections 1 Nat.zero_lt_one f)
    (hc : CommutingPairs M) (hu : UpperRelations M) :
    (∀ s t, M.shortValue 0 s * M.shortValue 2 t =
      M.shortValue 2 t * M.shortValue 0 s *
        M.longValue 1 (cubicTrace P (fieldFrobenius P (fieldFrobenius P s)*t))) ∧
    (∀ s t, M.shortValue 1 s * M.shortValue 2 t =
      M.shortValue 2 t * M.shortValue 1 s *
        M.longValue 2 (cubicTrace P (fieldFrobenius P (fieldFrobenius P s)*t))) := by
  constructor
  · intro s t
    have h := exchange_of_projection M (commutingRelations M hc) (by decide : 3 ≤ max (height 0) (height 3))
      hu.1 (sp s) (sp t) (cubicTrace P (fieldFrobenius P (fieldFrobenius P s)*t)) 0 (by
        change f (M.shortValue 0 s * M.shortValue 2 t) =
          f (M.shortValue 2 t * M.shortValue 0 s * (M.longValue 1 _ * M.longValue 2 0))
        simpa only [RootSections.shortValue, RootSections.longValue,
          ofAdd_zero, map_one, mul_one, map_mul, M.project_short, M.project_long]
          using base_trace02 P rfl s t)
    simpa [RootSections.factor, sp, RootSections.longValue] using h
  · intro s t
    have h := exchange_of_projection M (commutingRelations M hc) (by decide : 3 ≤ max (height 2) (height 3))
      hu.2.2 (sp s) (sp t) 0 (cubicTrace P (fieldFrobenius P (fieldFrobenius P s)*t)) (by
        change f (M.shortValue 1 s * M.shortValue 2 t) =
          f (M.shortValue 2 t * M.shortValue 1 s * (M.longValue 1 0 * M.longValue 2 _))
        simpa only [RootSections.shortValue, RootSections.longValue,
          ofAdd_zero, map_one, one_mul, map_mul, M.project_short, M.project_long]
          using base_trace12 P rfl s t)
    simpa [RootSections.factor, sp, RootSections.longValue] using h

private theorem seventh_power (a : (ExtensionField P)ˣ) : a.val ^ 7 = 1 := by
  have h := pow_card_eq_one' (x := a)
  rw [Nat.card_units, card_extensionField] at h
  exact congrArg Units.val h

private theorem quadratic_scale (a : (ExtensionField P)ˣ) (s : ExtensionField P) :
    (a.val^2*s) * fieldFrobenius P (a.val^2*s) =
      a.val⁻¹ * (s*fieldFrobenius P s) := by
  have h6 : a.val ^ 6 = a.val⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using seventh_power a
  have hF (x : ExtensionField P) : fieldFrobenius P x = x^2 := rfl
  simp only [hF]
  calc
    (a.val^2*s) * (a.val^2*s)^2 = a.val^6 * (s*s^2) := by ring
    _ = _ := by rw [h6]

private theorem norm_scale (a : (ExtensionField P)ˣ) (s : ExtensionField P) :
    cubicNorm P (a.val^2*s) = cubicNorm P s := by
  apply Subtype.ext
  have hF (x : ExtensionField P) : fieldFrobenius P x = x^2 := rfl
  simp only [cubicNorm, hF]
  calc
    (a.val^2*s) * (a.val^2*s)^2 * ((a.val^2*s)^2)^2 =
      (a.val^7)^2 * (s*s^2*(s^2)^2) := by ring
    _ = _ := by rw [seventh_power, one_pow, one_mul]

private theorem exists_moving_scalar : ∃ a : (ExtensionField P)ˣ, a.val^2 ≠ 1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ExtensionField P)ˣ)
  refine ⟨a, ?_⟩
  intro h
  have hd := orderOf_dvd_of_pow_eq_one (show a^2 = 1 from Units.ext h)
  rw [ha, Nat.card_units, card_extensionField] at hd
  change 7 ∣ 2 at hd
  norm_num at hd

private theorem conj_mul (z x y : E) :
    z*(x*y)*z⁻¹ = (z*x*z⁻¹)*(z*y*z⁻¹) := by group

private theorem mixed_of_normalized
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (M : RootSections 1 Nat.zero_lt_one f) (hT : ArmsTorusNormalized M)
    (hc : CommutingPairs M) (hu : UpperRelations M) (hs : ShortPairRelation M) :
    MixedPairRelation M := by
  have hC := commutingRelations M hc
  obtain ⟨h02, h12⟩ := upper_trace M hc hu
  obtain ⟨a, ha⟩ := exists_moving_scalar
  obtain ⟨z, hz⟩ := hf (torusActor P rfl .arms a)
  intro s t
  let v : Multiplicative (ExtensionField P) →* E := {
    toFun := fun u => M.shortValue 0 u.toAdd * M.shortValue 1 (u.toAdd*t.val) *
      M.shortValue 2 (u.toAdd*fieldFrobenius P u.toAdd*t.val) *
        M.longValue 1 (cubicNorm P u.toAdd*t)
    map_one' := by
      have hN : cubicNorm P 0 = 0 := by apply Subtype.ext; simp [cubicNorm]
      simp [RootSections.shortValue, RootSections.longValue, hN, -fieldFrobenius_apply]
    map_mul' := fun u w => candidate00_add M hC h02 h12 hs t u.toAdd w.toAdd }
  have hx : (M.longValue 0 t)⁻¹ = M.longValue 0 t := long_inv M 0 t
  have hx2 : M.longValue 0 t * M.longValue 0 t = 1 := by
    simpa only [hx] using inv_mul_cancel (M.longValue 0 t)
  have hp (u : ExtensionField P) :
      f (M.shortValue 0 u) * f (M.longValue 0 t) = f (M.longValue 0 t) * f (v (.ofAdd u)) := by
    change f (M.shortValue 0 u) * f (M.longValue 0 t) =
      f (M.longValue 0 t) * f (M.shortValue 0 u * M.shortValue 1 (u*t.val) *
        M.shortValue 2 (u*fieldFrobenius P u*t.val) * M.longValue 1 (cubicNorm P u*t))
    simp only [map_mul, RootSections.shortValue, RootSections.longValue,
      M.project_short, M.project_long]
    simpa only [mul_assoc] using base_mixed P rfl u t
  have he := RootSections.conjugation_eq_of_scalar hk (M.shortRoot 0) v
    (M.longValue 0 t) z (a.val^2) ha (hT.2 a z hz 0 t) (by
      intro u
      change f (M.longValue 0 t * M.shortValue 0 u * (M.longValue 0 t)⁻¹) = f (v (.ofAdd u))
      calc
        _ = f (M.longValue 0 t) * (f (M.shortValue 0 u) * f (M.longValue 0 t)) := by
          simp only [hx, map_mul, mul_assoc]
        _ = f (M.longValue 0 t) * (f (M.longValue 0 t) * f (v (.ofAdd u))) := by rw [hp]
        _ = _ := by rw [← mul_assoc, ← map_mul, hx2, map_one, one_mul])
    (by intro u; exact hT.1 a z hz 0 u) (by
      intro u
      change z * (M.shortValue 0 u * M.shortValue 1 (u*t.val) *
        M.shortValue 2 (u*fieldFrobenius P u*t.val) * M.longValue 1 (cubicNorm P u*t)) * z⁻¹ =
        M.shortValue 0 (a.val^2*u) * M.shortValue 1 (a.val^2*u*t.val) *
          M.shortValue 2 ((a.val^2*u)*fieldFrobenius P (a.val^2*u)*t.val) *
            M.longValue 1 (cubicNorm P (a.val^2*u)*t)
      simp only [conj_mul, RootSections.shortValue, RootSections.longValue,
        hT.1 a z hz, hT.2 a z hz]
      simp only [shortWeight, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [quadratic_scale, norm_scale]
      simp only [mul_assoc]) s
  change M.shortValue 0 s * M.longValue 0 t = _
  calc
    _ = M.longValue 0 t * (M.longValue 0 t * M.shortValue 0 s * (M.longValue 0 t)⁻¹) := by
      simp only [hx, ← mul_assoc, hx2, one_mul]
    _ = M.longValue 0 t * v (.ofAdd s) := congrArg (M.longValue 0 t * ·) (he)
    _ = _ := by simp only [v, MonoidHom.coe_mk, OneHom.coe_mk, mul_assoc]; rfl

local notation "π" => universalProjection G

/-- The exact mixed exchange in the canonical cover, with the short–short
relation as its only remaining polynomial input. -/
theorem mixedPairRelation_of_armsTorusNormalized
    (M : RootSections 1 Nat.zero_lt_one π) (hT : ArmsTorusNormalized M)
    (hc : CommutingPairs M) (hu : UpperRelations M) (hs : ShortPairRelation M) :
    MixedPairRelation M :=
  mixed_of_normalized (universalProjection_surjective G)
    (universalProjection_ker_le_center G) M hT hc hu hs

/-- Application to the literal `(0,1)` collector exchange used in lower normalization. -/
theorem mixedPairExchange_of_armsTorusNormalized
    (M : RootSections 1 Nat.zero_lt_one π) (hT : ArmsTorusNormalized M)
    (hc : CommutingPairs M) (hu : UpperRelations M) (hs : ShortPairRelation M) :
    PairExchange M 0 1 :=
  (mixedPairRelation_of_armsTorusNormalized M hT hc hu hs).pairExchange

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField.LowerNormalization
