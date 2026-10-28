module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Lifts.Tori
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Collection
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-!
# Positive unitary root relations from torus equivariance

Four separating fixed-field tori force the lifted commuting relations. For
both crossing relations, the torus diag(c,c,c⁻¹,c⁻¹) fixes the short root
and scales the other three roots by c². The matrix crossing identities give
two additive lifts with equal projections; their commutators with the torus
lift coincide because the kernel is central. Surjectivity of multiplication
by c²−1 then makes the lifts equal, for both field and trace-zero parameters.

The supplied root homomorphisms are retained, including the skew trace,
norm multiple, and negative middle-root parameter in the unitary formulas.
The resulting compatible roots give a section over the actual positive
subgroup. This is conditional on the explicit equivariant lifts, whose
construction belongs to the defining-prime source assembly.

Source: the SU₄ covering calculation underlying Aschbacher–Smith I.1.4(3),
printed p.408, and GLS3 §6.1. The scalar argument adapts the symplectic
central-cover relations to the actual unitary parameter groups.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open scoped commutatorElement
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
open Theory.SpecificGroups.ClassicalUnitary.OddFourRanks.Defining

private theorem additive_lifts_eq_of_shift {A E G : Type*}
    [AddCommGroup A] [Group E] [Group G]
    (f : E →* G) (hk : f.ker ≤ Subgroup.center E)
    (u v : A → E) (hu : ∀ x y, u (x+y) = u x * u y)
    (hv : ∀ x y, v (x+y) = v x * v y) (hp : ∀ x, f (u x) = f (v x))
    (z : E) (s : A → A) (hs : Function.Surjective fun x => s x - x)
    (htu : ∀ x, z * u x * z⁻¹ = u (s x))
    (htv : ∀ x, z * v x * z⁻¹ = v (s x)) (x : A) : u x = v x := by
  have hcomm (w : A → E) (ha : ∀ a b, w (a+b) = w a * w b)
      (ht : ∀ a, z * w a * z⁻¹ = w (s a)) (a : A) :
      ⁅z,w a⁆ = w (s a-a) := by
    rw [commutatorElement_def, ht]
    calc
      w (s a) * (w a)⁻¹ = (w (s a-a) * w a) * (w a)⁻¹ := by
        rw [← ha, sub_add_cancel]
      _ = w (s a-a) := by group
  obtain ⟨y,hy⟩ := hs x
  have h := CentralExtension.commutator_eq_of_image_eq f hk
    (x := z) (x' := z) rfl (hp y)
  simpa only [hcomm u hu htu, hcomm v hv htv, hy] using h

private theorem commute_of_fixed_shift {A E G : Type*}
    [AddCommGroup A] [Group E] [Group G]
    (f : E →* G) (hk : f.ker ≤ Subgroup.center E)
    (u : Multiplicative A →* E) (v z : E)
    (s : A → A) (hs : Function.Surjective fun x => s x - x)
    (hc : ∀ x, Commute (f (u (.ofAdd x))) (f v))
    (hu : ∀ x, z * u (.ofAdd x) * z⁻¹ = u (.ofAdd (s x)))
    (hv : z * v * z⁻¹ = v) (x : A) : Commute (u (.ofAdd x)) v := by
  let B : A → E := fun x => ⁅u (.ofAdd x), v⁆
  have hB (y : A) : B y ∈ Subgroup.center E := by
    apply hk
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact (hc y).commutator_eq
  have hBa (a b : A) : B (a+b) = B a * B b := by
    dsimp [B]
    rw [map_mul, commutatorElement_mul_left_eq_conj_mul]
    change u (.ofAdd a) * B b * (u (.ofAdd a))⁻¹ * B a = B a * B b
    rw [Subgroup.mem_center_iff.mp (hB b) _, mul_assoc (B b), mul_inv_cancel,
      mul_one, Subgroup.mem_center_iff.mp (hB a) _]
  have hBs (y : A) : B (s y) = B y := by
    dsimp [B]
    rw [← hu y, ← hv, ← conjugate_commutatorElement, hv]
    change z * B y * z⁻¹ = B y
    rw [Subgroup.mem_center_iff.mp (hB y) z, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨y,hy⟩ := hs x
  have h := hBs y
  rw [show s y = x+y by rw [← hy, sub_add_cancel], hBa] at h
  exact commutatorElement_eq_one_iff_commute.mp
    (mul_right_cancel (h.trans (one_mul _).symm))

private theorem additive_product {A E : Type*} [AddCommGroup A] [Group E]
    (u v : A → E) (hu : ∀ x y, u (x+y) = u x * u y)
    (hv : ∀ x y, v (x+y) = v x * v y)
    (hc : ∀ x y, Commute (u x) (v y)) (x y : A) :
    u (x+y) * v (x+y) = (u x*v x)*(u y*v y) := by
  rw [hu,hv]
  exact (hc y x).mul_mul_mul_comm _ _

variable {F : Type*} [Field F] (J : HermitianForm 4 F)

private theorem field_shift_surjective (c : F) (hc : c ≠ 1) :
    Function.Surjective (fun x : F => c*x-x) := by
  intro x
  refine ⟨(c-1)⁻¹*x, ?_⟩
  change c*((c-1)⁻¹*x) - ((c-1)⁻¹*x) = x
  rw [← sub_one_mul, mul_inv_cancel_left₀ (sub_ne_zero.mpr hc)]

private theorem trace_shift_surjective (c : fixedField J) (hc : c ≠ 1) :
    Function.Surjective (fun t : traceZero J => scaleTrace J c t-t) := by
  intro t
  refine ⟨scaleTrace J (c-1)⁻¹ t, ?_⟩
  apply Subtype.ext
  change (c : F) * ((((c-1)⁻¹ : fixedField J) : F) * (t : F)) -
      (((c-1)⁻¹ : fixedField J) : F) * (t : F) = (t : F)
  have hcF : (c : F) ≠ 1 := fun h => hc (Subtype.ext h)
  simp only [Subfield.coe_inv, Subfield.coe_sub, Subfield.coe_one]
  rw [← sub_one_mul, mul_inv_cancel_left₀ (sub_ne_zero.mpr hcF)]

private theorem exists_fixed_unit_sq_ne_one [Finite F]
    (hF : 3 < Nat.card (fixedField J)) :
    ∃ c : (fixedField J)ˣ, (c : fixedField J)^2 ≠ 1 := by
  classical
  let := Fintype.ofFinite (fixedField J)
  have hcard : ({0,1,-1} : Finset (fixedField J)).card <
      (Finset.univ : Finset (fixedField J)).card :=
    lt_of_le_of_lt Finset.card_le_three (by simpa only [Finset.card_univ,
      ← Nat.card_eq_fintype_card] using hF)
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  refine ⟨Units.mk0 c hc.1, ?_⟩
  intro h
  exact (sq_eq_one_iff.mp h).elim hc.2.1 hc.2.2


variable [Finite F] {E : Type*} [Group E] {f : E →* HyperbolicSU J}

private theorem lifted_commuting (L : EquivariantRootLifts J f)
    (hF : 3 < Nat.card (fixedField J))
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    (∀ a s, Commute (L.short (.ofAdd a)) (L.high (.ofAdd s))) ∧
    (∀ s b, Commute (L.high (.ofAdd s)) (L.middle (.ofAdd b))) ∧
    (∀ s t, Commute (L.high (.ofAdd s)) (L.long (.ofAdd t))) ∧
    (∀ b t, Commute (L.middle (.ofAdd b)) (L.long (.ofAdd t))) := by
  obtain ⟨c,hc⟩ := exists_fixed_unit_sq_ne_one J hF
  have hc1 : fixedUnitVal J c ≠ 1 := by
    intro h
    have he : (c : fixedField J) = 1 := Subtype.ext h
    exact hc (by rw [he, one_pow])
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a s
    obtain ⟨z,hz⟩ := hf (fixedDiagonal J 1 c)
    apply commute_of_fixed_shift f hk L.short (L.high (.ofAdd s)) z
      (fun x => (fixedUnitVal J c)⁻¹*x)
      (field_shift_surjective _ (by simpa using hc1)) ?_ ?_ ?_ a
    · intro x
      change Commute ((f.comp L.short) _) ((f.comp L.high) _)
      rw [L.project_short,L.project_high]
      exact short_high_commute J x s
    · intro x
      simpa using L.equiv_short 1 c z hz x
    · simpa using L.equiv_high 1 c z hz s
  · intro s b
    obtain ⟨z,hz⟩ := hf (fixedDiagonal J c c⁻¹)
    apply commute_of_fixed_shift f hk L.high (L.middle (.ofAdd b)) z
      (scaleTrace J ((c : fixedField J)^2))
      (trace_shift_surjective J _ hc) ?_ (L.equiv_high c c⁻¹ z hz) ?_ s
    · intro t
      change Commute ((f.comp L.high) _) ((f.comp L.middle) _)
      rw [L.project_high,L.project_middle]
      exact high_middle_commute J t b
    · simpa using L.equiv_middle c c⁻¹ z hz b
  · intro s t
    obtain ⟨z,hz⟩ := hf (fixedDiagonal J c 1)
    apply commute_of_fixed_shift f hk L.high (L.long (.ofAdd t)) z
      (scaleTrace J ((c : fixedField J)^2))
      (trace_shift_surjective J _ hc) ?_ (L.equiv_high c 1 z hz) ?_ s
    · intro x
      change Commute ((f.comp L.high) _) ((f.comp L.long) _)
      rw [L.project_high,L.project_long]
      exact high_long_commute J x t
    · simpa using L.equiv_long c 1 z hz t
  · intro b t
    obtain ⟨z,hz⟩ := hf (fixedDiagonal J c 1)
    apply commute_of_fixed_shift f hk L.middle (L.long (.ofAdd t)) z
      (fun x => fixedUnitVal J c*x) (field_shift_surjective _ hc1) ?_ ?_ ?_ b
    · intro x
      change Commute ((f.comp L.middle) _) ((f.comp L.long) _)
      rw [L.project_middle,L.project_long]
      exact middle_long_commute J x t
    · intro x
      simpa using L.equiv_middle c 1 z hz x
    · simpa using L.equiv_long c 1 z hz t

omit [Finite F] in
private theorem skew_add_right (a b d : F) :
    skew J a (b+d) = skew J a b + skew J a d := by
  apply Subtype.ext
  change a * J.conj (b+d) - (b+d) * J.conj a =
    (a * J.conj b - b * J.conj a) + (a * J.conj d - d * J.conj a)
  rw [map_add]
  ring

omit [Finite F] in
private theorem skew_scale_right (a b : F) (c : fixedField J) :
    skew J a ((c : F)*b) = scaleTrace J c (skew J a b) := by
  apply Subtype.ext
  change a * J.conj ((c : F)*b) - ((c : F)*b) * J.conj a =
    (c : F) * (a * J.conj b - b * J.conj a)
  rw [map_mul,conj_fixed]
  ring

omit [Finite F] in
private theorem normMul_add (a : F) (s t : traceZero J) :
    normMul J a (s+t) = normMul J a s + normMul J a t := by
  apply Subtype.ext
  exact mul_add _ _ _

omit [Finite F] in
private theorem normMul_scale (a : F) (t : traceZero J) (c : fixedField J) :
    normMul J a (scaleTrace J c t) = scaleTrace J c (normMul J a t) := by
  apply Subtype.ext
  change a * J.conj a * ((c : F)*t) = (c : F) * (a * J.conj a * t)
  ring

namespace EquivariantRootLifts
variable (L : EquivariantRootLifts J f)

private theorem lifted_crossing (hF : 3 < Nat.card (fixedField J))
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    (∀ b a, L.middle (.ofAdd b) * L.short (.ofAdd a) =
      L.short (.ofAdd a) * L.high (.ofAdd (skew J a b)) * L.middle (.ofAdd b)) ∧
    (∀ t a, L.long (.ofAdd t) * L.short (.ofAdd a) =
      L.short (.ofAdd a) * L.high (.ofAdd (normMul J a t)) *
        L.middle (.ofAdd (-a*(t : F))) * L.long (.ofAdd t)) := by
  obtain ⟨hSH,hHM,hHT,hMT⟩ := lifted_commuting J L hF hf hk
  let S : F → E := fun a => L.short (.ofAdd a)
  let H : traceZero J → E := fun s => L.high (.ofAdd s)
  let M : F → E := fun b => L.middle (.ofAdd b)
  let T : traceZero J → E := fun t => L.long (.ofAdd t)
  have hHa (s t : traceZero J) : H (s+t) = H s * H t := L.high.map_mul _ _
  have hMa (a b : F) : M (a+b) = M a * M b := L.middle.map_mul _ _
  have hTa (s t : traceZero J) : T (s+t) = T s * T t := L.long.map_mul _ _
  have hSp (a : F) : f (S a) = shortRoot J (.ofAdd a) :=
    DFunLike.congr_fun L.project_short (.ofAdd a)
  have hHp (s : traceZero J) : f (H s) = highRoot J (.ofAdd s) :=
    DFunLike.congr_fun L.project_high (.ofAdd s)
  have hMp (b : F) : f (M b) = middleRoot J (.ofAdd b) :=
    DFunLike.congr_fun L.project_middle (.ofAdd b)
  have hTp (t : traceZero J) : f (T t) = longRoot J (.ofAdd t) :=
    DFunLike.congr_fun L.project_long (.ofAdd t)
  obtain ⟨c,hc⟩ := exists_fixed_unit_sq_ne_one J hF
  obtain ⟨z,hz⟩ := hf (fixedDiagonal J c c)
  let e : E ≃* E := MulAut.conj z
  let k : fixedField J := (c : fixedField J)^2
  have hk1 : (k : F) ≠ 1 := fun h => hc (Subtype.ext h)
  have heS (a : F) : e (S a) = S a := by
    simpa [e,S,MulAut.conj_apply] using L.equiv_short c c z hz a
  have heH (s : traceZero J) : e (H s) = H (scaleTrace J k s) :=
    L.equiv_high c c z hz s
  have heM (b : F) : e (M b) = M ((k : F)*b) := by
    simpa [e,M,k,pow_two,fixedUnitVal,MulAut.conj_apply] using L.equiv_middle c c z hz b
  have heT (t : traceZero J) : e (T t) = T (scaleTrace J k t) :=
    L.equiv_long c c z hz t
  have crossMS (b a : F) : M b * S a = S a * H (skew J a b) * M b := by
    let C : F → E := fun x => (S a)⁻¹ * M x * S a
    let P : F → E := fun x => H (skew J a x) * M x
    have hCa (x y : F) : C (x+y) = C x * C y := by
      dsimp [C]
      rw [hMa]
      group
    have hPa (x y : F) : P (x+y) = P x * P y := by
      apply additive_product (fun x => H (skew J a x)) M
        (fun x y => by rw [skew_add_right,hHa]) hMa (fun x y => hHM _ _)
    have hp (x : F) : f (C x) = f (P x) := by
      simp only [C,P,map_mul,map_inv,hSp,hHp,hMp]
      rw [mul_assoc,middle_short_crossing]
      simp only [mul_assoc,inv_mul_cancel_left]
    have hCt (x : F) : z*C x*z⁻¹ = C ((k : F)*x) := by
      change e (C x) = _
      simp only [C,map_mul,map_inv,heS,heM]
    have hPt (x : F) : z*P x*z⁻¹ = P ((k : F)*x) := by
      change e (P x) = _
      simp only [P,map_mul,heH,heM,skew_scale_right]
    have h := additive_lifts_eq_of_shift f hk C P hCa hPa hp z
      (fun x => (k : F)*x) (field_shift_surjective _ hk1) hCt hPt b
    have h' := congrArg (fun g => S a * g) h
    simpa only [C,P,mul_assoc,mul_inv_cancel_left] using h'
  have crossTS (t : traceZero J) (a : F) : T t * S a =
      S a * H (normMul J a t) * M (-a*(t : F)) * T t := by
    let C : traceZero J → E := fun x => (S a)⁻¹ * T x * S a
    let P : traceZero J → E := fun x => H (normMul J a x) * M (-a*(x : F)) * T x
    have hCa (x y : traceZero J) : C (x+y) = C x * C y := by
      dsimp [C]
      rw [hTa]
      group
    have hPa (x y : traceZero J) : P (x+y) = P x * P y := by
      apply additive_product (fun x => H (normMul J a x) * M (-a*(x : F))) T
      · intro s t
        apply additive_product (fun x => H (normMul J a x)) (fun x => M (-a*(x : F)))
          (fun x y => by rw [normMul_add,hHa])
          (fun x y => by rw [AddSubgroup.coe_add,mul_add,hMa]) (fun x y => hHM _ _)
      · exact hTa
      · intro s t
        exact (hHT _ _).mul_left (hMT _ _)
    have hp (x : traceZero J) : f (C x) = f (P x) := by
      simp only [C,P,map_mul,map_inv,hSp,hHp,hMp,hTp]
      rw [mul_assoc,long_short_crossing]
      simp only [mul_assoc,inv_mul_cancel_left]
    have hCt (x : traceZero J) : z*C x*z⁻¹ = C (scaleTrace J k x) := by
      change e (C x) = _
      simp only [C,map_mul,map_inv,heS,heT]
    have hPt (x : traceZero J) : z*P x*z⁻¹ = P (scaleTrace J k x) := by
      change e (P x) = _
      simp only [P,map_mul,heH,heM,heT,normMul_scale,coe_scaleTrace]
      congr 2
      congr 1
      ring
    have h := additive_lifts_eq_of_shift f hk C P hCa hPa hp z
      (scaleTrace J k) (trace_shift_surjective J k hc) hCt hPt t
    have h' := congrArg (fun g => S a * g) h
    simpa only [C,P,mul_assoc,mul_inv_cancel_left] using h'
  exact ⟨crossMS,crossTS⟩

/-- Torus equivariance forces all six positive-root relations in a central cover.
The original four homomorphisms and their projection equations are retained. -/
def toPositiveRootLifts (L : EquivariantRootLifts J f) (hF : 3 < Nat.card (fixedField J))
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    PositiveRootLifts J f where
  short := L.short
  high := L.high
  middle := L.middle
  long := L.long
  project_short := L.project_short
  project_high := L.project_high
  project_middle := L.project_middle
  project_long := L.project_long
  commute_short_high := by exact (lifted_commuting J L hF hf hk).1
  commute_high_middle := by exact (lifted_commuting J L hF hf hk).2.1
  commute_high_long := by exact (lifted_commuting J L hF hf hk).2.2.1
  commute_middle_long := by exact (lifted_commuting J L hF hf hk).2.2.2
  crossing_middle_short := by exact (lifted_crossing J L hF hf hk).1
  crossing_long_short := by exact (lifted_crossing J L hF hf hk).2

/-- The compatible equivariant lifts give a section over the actual positive
matrix subgroup; no splitting assumption remains beyond the supplied lifts. -/
theorem exists_positive_section (L : EquivariantRootLifts J f) (hF : 3 < Nat.card (fixedField J))
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ∃ s : positive J →* E, f.comp s = (positive J).subtype :=
  (toPositiveRootLifts J L hF hf hk).exists_positive_section

/-- The prime-degree source hypotheses provide the required fixed-field size. -/
def toPositiveRootLifts_of_prime (L : EquivariantRootLifts J f) {q : ℕ} (hp : q.Prime) (hq : 3 < q)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    PositiveRootLifts J f :=
  toPositiveRootLifts J L (by rw [card_fixedField J hp hcard hconj]; exact hq) hf hk

/-- Application to the defining-prime input for the U₄ Mersenne branch. The
construction of the input `L` remains with the source assembly owner. -/
theorem exists_positive_section_of_prime (L : EquivariantRootLifts J f) {q : ℕ} (hp : q.Prime) (hq : 3 < q)
    (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    ∃ s : positive J →* E, f.comp s = (positive J).subtype :=
  (toPositiveRootLifts_of_prime J L hp hq hcard hconj hf hk).exists_positive_section

end EquivariantRootLifts

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
