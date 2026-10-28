module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime.Lifts.Preimages
public import Theory.GroupTheory.PerfectCentralCover
import Mathlib.Tactic.Ring

/-!
# Torus-equivariant sections of the four positive unitary roots

In a central extension with kernel of prime order q > 3, all four root
preimages are abelian. For a torus element with root weight c ≠ 1, the
commutator of a lift of that element with a lift of the root parameter
(c − 1)⁻¹x projects to the root element with parameter x. Independence
of these commutators from lift choices and abelianity of the preimages
make this an additive section. Commutativity of the literal diagonal
matrices gives equivariance under every lift of the full fixed-field torus.

For the long roots, the inverse scaling is the actual `scaleTrace` map.
The fixed field has q > 3 elements, so it contains a unit with square
unequal to one; this gives a nontrivial weight for each root. The final
application uses the actual map of a perfect central cover. Cross-root
relations are a separate step in the positive-subgroup section assembly.

Source: the defining-prime calculation underlying GLS3 §6.1 and
Aschbacher--Smith I.1.4(3), printed p.408.
-/

public noncomputable section

open scoped commutatorElement

/-- Commutating with a moving torus element splits an abelian root preimage. -/
private theorem exists_commutator_section
    {E G A I : Type*} [Group E] [Group G] [AddCommGroup A]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (r : Multiplicative A →* G)
    (hcomm : ∀ x y : E, f x ∈ r.range → f y ∈ r.range → Commute x y)
    (d : I → G) (w : I → A →+ A)
    (hd : ∀ i j, Commute (d i) (d j))
    (hw : ∀ i x, d i * r (.ofAdd x) * (d i)⁻¹ = r (.ofAdd (w i x)))
    (i : I) (v : A →+ A)
    (hv : ∀ x, w i (v x) - v x = x)
    (hvw : ∀ j x, w j (v x) = v (w j x)) :
    ∃ u : Multiplicative A →* E, f.comp u = r ∧
      ∀ j (z : E), f z = d j → ∀ x : A,
        z * u (.ofAdd x) * z⁻¹ = u (.ofAdd (w j x)) := by
  classical
  obtain ⟨a, ha⟩ := hf (d i)
  choose b hb using fun x : A => hf (r (.ofAdd x))
  let s : A → E := fun x => ⁅a, b (v x)⁆
  have hs (x : A) : f (s x) = r (.ofAdd x) := by
    dsimp [s]
    rw [map_commutatorElement, commutatorElement_def, ha, hb, hw,
      ← map_inv, ← map_mul]
    change r (.ofAdd (w i (v x) + -(v x))) = r (.ofAdd x)
    rw [← sub_eq_add_neg, hv]
  have hs0 : s 0 = 1 := by
    dsimp [s]
    rw [map_zero]
    have h0 : f (b 0) = f 1 := by simpa using hb 0
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl h0]
    simp
  have hsadd (x y : A) : s (x+y) = s x * s y := by
    have hsum : f (b (v (x+y))) = f (b (v x) * b (v y)) := by
      rw [map_mul, hb, hb, hb, map_add]
      exact r.map_mul (.ofAdd (v x)) (.ofAdd (v y))
    have hc : Commute (b (v x)) (s y) := hcomm _ _
      ⟨.ofAdd _, (hb _).symm⟩ ⟨.ofAdd _, (hs _).symm⟩
    change ⁅a, b (v (x+y))⁆ = _
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl hsum,
      commutatorElement_mul_right_eq_mul_conj]
    change s x * b (v x) * s y * (b (v x))⁻¹ = _
    rw [mul_assoc (s x), hc.eq, ← mul_assoc, mul_assoc (s x * s y),
      mul_inv_cancel, mul_one]
  refine ⟨{ toFun := fun x => s x.toAdd
            map_one' := hs0
            map_mul' := fun x y => hsadd x.toAdd y.toAdd },
    MonoidHom.ext (fun x => hs x.toAdd), ?_⟩
  intro j z hz x
  change z * s x * z⁻¹ = s (w j x)
  dsimp [s]
  rw [conjugate_commutatorElement]
  apply CentralExtension.commutator_eq_of_image_eq f hk
  · rw [map_mul, map_mul, map_inv, hz, ha, (hd j i).eq,
      mul_assoc, mul_inv_cancel, mul_one]
  · rw [map_mul, map_mul, map_inv, hz, hb, hb, hw, hvw]

open BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
variable {F : Type*} [Field F] (J : HermitianForm 4 F)

private theorem exists_fixed_unit_sq_ne_one [Finite F] {q : ℕ} (hp : q.Prime)
    (hq : 3 < q) (hcard : Nat.card F = q^2) (hconj : ∀ x, J.conj x = x^q) :
    ∃ c : (fixedField J)ˣ, (c : fixedField J)^2 ≠ 1 := by
  classical
  let := Fintype.ofFinite (fixedField J)
  have hlt : ({0, 1, -1} : Finset (fixedField J)).card <
      (Finset.univ : Finset (fixedField J)).card := by
    apply lt_of_le_of_lt Finset.card_le_three
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card,
      card_fixedField J hp hcard hconj] using hq
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨Units.mk0 c hc.1, fun h => (sq_eq_one_iff.mp h).elim hc.2.1 hc.2.2⟩

variable {E : Type*} [Group E] (f : E →* HyperbolicSU J)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
include hf hk

private theorem exists_field_root_section
    (r : Multiplicative F →* HyperbolicSU J)
    (hcomm : ∀ x y : E, f x ∈ r.range → f y ∈ r.range → Commute x y)
    (w : (fixedField J)ˣ × (fixedField J)ˣ → F)
    (hw : ∀ a b x, fixedDiagonal J a b * r (.ofAdd x) *
      (fixedDiagonal J a b)⁻¹ = r (.ofAdd (w (a,b)*x)))
    (a b : (fixedField J)ˣ) (hab : w (a,b) ≠ 1) :
    ∃ u : Multiplicative F →* E, f.comp u = r ∧
      ∀ a b (z : E), f z = fixedDiagonal J a b → ∀ x : F,
        z * u (.ofAdd x) * z⁻¹ = u (.ofAdd (w (a,b)*x)) := by
  let v := AddMonoidHom.mulLeft ((w (a,b)-1)⁻¹)
  obtain ⟨u, hu, he⟩ := exists_commutator_section (I := (fixedField J)ˣ × (fixedField J)ˣ) f hf hk r hcomm
    (fun i => fixedDiagonal J i.1 i.2)
    (fun i => AddMonoidHom.mulLeft (w i))
    (fun i j => fixedDiagonal_commute J i.1 i.2 j.1 j.2)
    (fun i => hw i.1 i.2) (a,b) v
    (fun x => by
      change w (a,b) * ((w (a,b)-1)⁻¹*x) - (w (a,b)-1)⁻¹*x = x
      calc
        _ = (w (a,b)-1) * ((w (a,b)-1)⁻¹*x) := by ring
        _ = x := mul_inv_cancel_left₀ (sub_ne_zero.mpr hab) x)
    (fun j x => by change w j * (_ * x) = _ * (w j * x); ring)
  exact ⟨u, hu, fun a b => he (a,b)⟩

private theorem exists_trace_root_section
    (r : Multiplicative (traceZero J) →* HyperbolicSU J)
    (hcomm : ∀ x y : E, f x ∈ r.range → f y ∈ r.range → Commute x y)
    (w : (fixedField J)ˣ × (fixedField J)ˣ → fixedField J)
    (hw : ∀ a b x, fixedDiagonal J a b * r (.ofAdd x) *
      (fixedDiagonal J a b)⁻¹ = r (.ofAdd (scaleTrace J (w (a,b)) x)))
    (a b : (fixedField J)ˣ) (hab : w (a,b) ≠ 1) :
    ∃ u : Multiplicative (traceZero J) →* E, f.comp u = r ∧
      ∀ a b (z : E), f z = fixedDiagonal J a b → ∀ x : traceZero J,
        z * u (.ofAdd x) * z⁻¹ = u (.ofAdd (scaleTrace J (w (a,b)) x)) := by
  have hn : ((w (a,b) : fixedField J) : F) - 1 ≠ 0 := by
    intro h
    exact hab (Subtype.ext (sub_eq_zero.mp h))
  obtain ⟨u, hu, he⟩ := exists_commutator_section (I := (fixedField J)ˣ × (fixedField J)ˣ) f hf hk r hcomm
    (fun i => fixedDiagonal J i.1 i.2) (fun i => scaleTrace J (w i))
    (fun i j => fixedDiagonal_commute J i.1 i.2 j.1 j.2)
    (fun i => hw i.1 i.2) (a,b) (scaleTrace J ((w (a,b)-1)⁻¹))
    (fun x => by
      apply Subtype.ext
      change (w (a,b) : F) * ((((w (a,b)-1)⁻¹ : fixedField J) : F) * (x : F)) -
        (((w (a,b)-1)⁻¹ : fixedField J) : F) * (x : F) = (x : F)
      simp only [Subfield.coe_inv, Subfield.coe_sub, Subfield.coe_one]
      calc
        _ = ((w (a,b) : F)-1) * (((w (a,b) : F)-1)⁻¹*(x : F)) := by ring
        _ = (x : F) := mul_inv_cancel_left₀ hn (x : F))
    (fun j x => by
      apply Subtype.ext
      change (w j : F) * (_ * (x : F)) = _ * ((w j : F) * (x : F))
      ring)
  exact ⟨u, hu, fun a b => he (a,b)⟩


/-- Four additive sections of the literal positive unitary roots, normalized
by every lift of every fixed-field diagonal matrix. The construction uses
central commutators and abelian full preimages, not a splitting hypothesis. -/
theorem equivariantRootLifts_of_prime_kernel [Finite F] {q : ℕ}
    (hp : q.Prime) (hq : 3 < q) (hcard : Nat.card F = q^2)
    (hconj : ∀ x, J.conj x = x^q) (hdegree : Nat.card f.ker = q) :
    Nonempty (EquivariantRootLifts J f) := by
  obtain ⟨c, hc⟩ := exists_fixed_unit_sq_ne_one J hp hq hcard hconj
  have hc1 : fixedUnitVal J c ≠ 1 := by
    intro h
    have he : (c : fixedField J) = 1 := Subtype.ext h
    exact hc (by rw [he, one_pow])
  obtain ⟨us, hps, hes⟩ := exists_field_root_section J f hf hk (shortRoot J)
    (fun _ _ => short_preimage_commute_of_prime_kernel J f hf hk hp hq hcard hdegree)
    (fun i => fixedUnitVal J (i.1*i.2⁻¹))
    (fixedDiagonal_short J) c 1 (by simpa using hc1)
  obtain ⟨um, hpm, hem⟩ := exists_field_root_section J f hf hk (middleRoot J)
    (fun _ _ => middle_preimage_commute_of_prime_kernel J f hf hk hp hq hcard hdegree)
    (fun i => fixedUnitVal J (i.1*i.2))
    (fixedDiagonal_middle J) c 1 (by simpa using hc1)
  obtain ⟨uh, hph, heh⟩ := exists_trace_root_section J f hf hk (highRoot J)
    (fun _ _ => high_preimage_commute J f hf hk hp hcard hconj)
    (fun i => (i.1 : fixedField J)^2) (fixedDiagonal_high J) c 1 hc
  obtain ⟨ul, hpl, hel⟩ := exists_trace_root_section J f hf hk (longRoot J)
    (fun _ _ => long_preimage_commute J f hf hk hp hcard hconj)
    (fun i => (i.2 : fixedField J)^2) (fixedDiagonal_long J) 1 c hc
  exact ⟨{ short := us, high := uh, middle := um, long := ul
           project_short := hps, project_high := hph
           project_middle := hpm, project_long := hpl
           equiv_short := hes, equiv_high := heh
           equiv_middle := hem, equiv_long := hel }⟩

omit hf hk in
/-- Application to the actual map of a perfect central cover. This supplies
the equivariant-root-section input for the positive-root relation assembly. -/
theorem equivariantRootLifts_of_prime_cover [Finite F] {q : ℕ}
    (hp : q.Prime) (hq : 3 < q) (hcard : Nat.card F = q^2)
    (hconj : ∀ x, J.conj x = x^q)
    (cover : PerfectCentralCovering.Cover E (HyperbolicSU J))
    (hdegree : Nat.card cover.toMonoidHom.ker = q) :
    Nonempty (EquivariantRootLifts J cover.toMonoidHom) := by
  exact equivariantRootLifts_of_prime_kernel J cover.toMonoidHom
    cover.surjective cover.ker_le_center hp hq hcard hconj hdegree

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.DefiningPrime
