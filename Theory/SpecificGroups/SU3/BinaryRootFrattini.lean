module

public import Theory.SpecificGroups.SU3.TorusWeightSpan
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.RootGeneration
public import Theory.Frattini.PGroup
public import Theory.Frattini.OmegaProducts

/-!
# The Frattini layer of a binary Hermitian root group

The first-coordinate kernel consists exactly of the elements whose square is
one. Norm surjectivity makes each of these elements a square, so the kernel
is the Frattini subgroup. Its zero first coordinate also proves centrality.
On the quotient, full-torus weights span the quadratic field. An invariant
subgroup with a nonzero first coordinate therefore covers all first
coordinates; squares then recover the central layer and the whole root.

Source: GLS4, Chapter 4, Lemma 3.5(a,c); Hermitian coordinates and trace/norm
surjectivity from Huppert II.10.4 and II.10.12. The transport lemmas retain
actual group isomorphisms and the literal ambient Frattini image.
-/

public section

open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BinaryRootFrattini
open EvenInner OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] [CharP E 2] (J : HermitianForm 3 E)

/-- The additive first coordinate, exposed for the root-layer calculations. -/
@[expose] def firstCoordinate : hermitianUnipotentCoord J →* Multiplicative E where
  toFun z := Multiplicative.ofAdd z.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

omit [CharP E 2] in
/-- Quadratic trace surjectivity supplies a root element over every first coordinate. -/
theorem firstCoordinate_surjective [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Function.Surjective (firstCoordinate J) := by
  intro a
  obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed
    (-(a.toAdd * J.conj a.toAdd)) (by
      rw [map_neg, map_mul, J.conj_involutive, mul_comm])
  exact ⟨⟨(a.toAdd, b), by dsimp only; rw [hb]; ring⟩, rfl⟩

theorem square_one_iff (z : hermitianUnipotentCoord J) :
    z ^ 2 = 1 ↔ z.val.1 = 0 := by
  constructor
  · intro hz
    have hs := congrArg (fun w : hermitianUnipotentCoord J => w.val.2) hz
    rw [square_coordinates] at hs
    have hm : z.val.1 * J.conj z.val.1 = 0 := hs
    exact (mul_eq_zero.mp hm).elim id ((map_eq_zero J.conj).mp)
  · intro hz
    apply Subtype.ext
    rw [square_coordinates, hz, zero_mul]
    rfl

theorem isTwoGroup : IsPGroup 2 (hermitianUnipotentCoord J) := by
  intro z
  refine ⟨2, ?_⟩
  change z ^ 4 = 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  apply (square_one_iff J _).mpr
  exact congrArg Prod.fst (square_coordinates J z)

omit [CharP E 2] in
theorem first_kernel_central : (firstCoordinate J).ker ≤ center (hermitianUnipotentCoord J) := by
  intro z hz
  have hz0 : z.val.1 = 0 := congrArg Multiplicative.toAdd hz
  apply mem_center_iff.mpr
  intro w
  apply Subtype.ext
  apply Prod.ext
  · change w.val.1 + z.val.1 = z.val.1 + w.val.1
    exact add_comm _ _
  · change w.val.2 + z.val.2 - w.val.1 * J.conj z.val.1 =
      z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1
    simp [hz0, add_comm]

variable [Finite E] {q : ℕ} (hcard : Nat.card E = q ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = q)

include hcard hfixed in
theorem frattini_eq_first_kernel : frattini (hermitianUnipotentCoord J) = (firstCoordinate J).ker := by
  let : Fact (IsPGroup 2 (hermitianUnipotentCoord J)) := ⟨isTwoGroup J⟩
  apply le_antisymm
  · let : IsElementaryAbelian 2 (Multiplicative E) := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
        change (2 : ℕ) • x.toAdd = 0
        rw [two_nsmul]
        exact CharTwo.add_self_eq_zero x.toAdd }
    let : Fact (IsPGroup 2 (Multiplicative E)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
    have hh := frattini_le_comap_frattini_of_surjective (firstCoordinate_surjective J hcard hfixed)
    rw [frattini_eq_bot_of_isElementaryAbelian (R := Multiplicative E) (p := 2)] at hh
    intro z hz
    exact mem_bot.mp (hh hz)
  · intro z hz
    have hz0 : z.val.1 = 0 := congrArg Multiplicative.toAdd hz
    by_cases hb : z.val.2 = 0
    · have he : z = 1 := Subtype.ext (Prod.ext hz0 hb)
      exact he ▸ (frattini (hermitianUnipotentCoord J)).one_mem
    have hfix : J.conj z.val.2 = z.val.2 := by
      have hp := z.property
      rw [hz0, zero_mul, add_zero] at hp
      exact (eq_neg_of_add_eq_zero_right hp).trans (CharTwo.neg_eq _)
    obtain ⟨a, _, ha⟩ := huppert_II_10_4_norm_surjective J q hcard hfixed z.val.2 hfix hb
    obtain ⟨w, hw⟩ := firstCoordinate_surjective J hcard hfixed (Multiplicative.ofAdd a)
    have hw0 : w.val.1 = a := congrArg Multiplicative.toAdd hw
    have hs : w ^ 2 = z := by
      apply Subtype.ext
      rw [square_coordinates, hw0, ha]
      exact Prod.ext hz0.symm rfl
    exact hs ▸ pth_power_mem_frattini_of_isPGroup (p := 2) w

include hcard hfixed in
theorem mem_frattini_iff_square_one (z : hermitianUnipotentCoord J) :
    z ∈ frattini (hermitianUnipotentCoord J) ↔ z ^ 2 = 1 := by
  rw [frattini_eq_first_kernel J hcard hfixed, square_one_iff]
  rfl

include hcard hfixed in
theorem frattini_central : frattini (hermitianUnipotentCoord J) ≤
    center (hermitianUnipotentCoord J) := by
  rw [frattini_eq_first_kernel J hcard hfixed]
  exact first_kernel_central J

include hcard hfixed in
theorem invariant_subgroup (hq : 2 < q) (W : Subgroup (hermitianUnipotentCoord J))
    (hW : ∀ k : Eˣ, ∀ z ∈ W, hermitianTorusAction J k z ∈ W) :
    W ≤ frattini (hermitianUnipotentCoord J) ∨ W = ⊤ := by
  by_cases hz : W ≤ (firstCoordinate J).ker
  · exact Or.inl ((frattini_eq_first_kernel J hcard hfixed).symm ▸ hz)
  right
  have he : ∃ z ∈ W, z.val.1 ≠ 0 := by
    by_contra! hh
    exact hz (fun z hzw => show firstCoordinate J z = 1 from congrArg Multiplicative.ofAdd (hh z hzw))
  obtain ⟨z, hzW, hz0⟩ := he
  let A : AddSubgroup E := (W.map (firstCoordinate J)).toAddSubgroup'
  have hzA : z.val.1 ∈ A := ⟨z, hzW, rfl⟩
  have hw (k : Eˣ) {a : E} (ha : a ∈ A) : (torusWeight J k : E) * a ∈ A := by
    obtain ⟨w, hwW, hw⟩ := ha
    refine ⟨hermitianTorusAction J k w, hW k w hwW, ?_⟩
    have hwa : w.val.1 = a := congrArg Multiplicative.toAdd hw
    apply Multiplicative.toAdd.injective
    change (hermitianTorusAction J k w).val.1 = (torusWeight J k : E) * a
    rw [hermitianTorusAction_fst, hwa, torusWeight_val]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  have hspan (b : E)
      (hb : b ∈ AddSubgroup.closure (Set.range (fun k : Eˣ => (torusWeight J k : E)))) :
      b * z.val.1 ∈ A := by
    induction hb using AddSubgroup.closure_induction with
    | mem b hb =>
      obtain ⟨k, rfl⟩ := hb
      exact hw k hzA
    | zero => simpa only [zero_mul] using A.zero_mem
    | add a b _ _ ha hb => simpa only [add_mul] using A.add_mem ha hb
    | neg a _ ha => simpa only [neg_mul] using A.neg_mem ha
  have hfull (a : E) : a ∈ A := by
    have hh := hspan (a / z.val.1) (by rw [TorusWeightSpan.additive_span J hq hcard]; trivial)
    simpa only [div_mul_cancel₀ _ hz0] using hh
  have hall := range_le_of_first_surjective J hcard hfixed (MonoidHom.id _) W (fun a => by
    obtain ⟨w, hwW, hw⟩ := hfull a
    exact ⟨w, congrArg Multiplicative.toAdd hw, hwW⟩)
  apply top_unique
  intro w _
  exact hall ⟨w, rfl⟩


include hcard hfixed in
/-- Transport of the Frattini and central-layer calculation through actual coordinates. -/
theorem equiv_structure {H : Type*} [Group H] (e : H ≃* hermitianUnipotentCoord J) :
    (∀ x : H, x ∈ frattini H ↔ x ^ 2 = 1) ∧ frattini H ≤ center H := by
  have hm (x : H) : x ∈ frattini H ↔ e x ∈ frattini (hermitianUnipotentCoord J) := by
    rw [← frattini_map_equiv e, mem_map_equiv]
    simp only [e.symm_apply_apply]
  constructor
  · intro x
    rw [hm, mem_frattini_iff_square_one J hcard hfixed,
      ← map_pow, ← e.map_one, e.injective.eq_iff]
  · intro x hx
    have hc := frattini_central J hcard hfixed ((hm x).mp hx)
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp hc (e y)

include hcard hfixed in
/-- Any injective realization of the root coordinates has the same full-torus
subgroup dichotomy, with its literal ambient Frattini image. -/
theorem image_invariant_subgroup {H : Type*} [Group H]
    (hq : 2 < q) (f : hermitianUnipotentCoord J →* H) (hf : Function.Injective f)
    (torus : Eˣ →* H)
    (hact : ∀ k z, torus k * f z * (torus k)⁻¹ = f (hermitianTorusAction J k z))
    (W : Subgroup H) (hW : W ≤ f.range)
    (hN : torus.range ≤ normalizer (W : Set H)) :
    W ≤ (frattini f.range).map f.range.subtype ∨ W = f.range := by
  have hphi : (frattini (hermitianUnipotentCoord J)).map f =
      (frattini f.range).map f.range.subtype := by
    rw [← frattini_map_equiv (MonoidHom.ofInjective hf), map_map]
    rfl
  have hstable (k : Eˣ) (z : hermitianUnipotentCoord J) (hz : z ∈ W.comap f) :
      hermitianTorusAction J k z ∈ W.comap f := by
    change f (hermitianTorusAction J k z) ∈ W
    rw [← hact]
    exact (mem_normalizer_iff.mp (hN ⟨k, rfl⟩) (f z)).mp hz
  obtain hsmall | hfull := invariant_subgroup J hcard hfixed hq (W.comap f) hstable
  · left
    rw [← hphi]
    intro x hx
    obtain ⟨z, rfl⟩ := hW hx
    exact ⟨z, hsmall hx, rfl⟩
  · right
    apply le_antisymm hW
    rintro x ⟨z, rfl⟩
    have hz : z ∈ W.comap f := hfull ▸ mem_top z
    exact hz

end BenderSuzuki.MatrixGroups.HermitianForm.BinaryRootFrattini
