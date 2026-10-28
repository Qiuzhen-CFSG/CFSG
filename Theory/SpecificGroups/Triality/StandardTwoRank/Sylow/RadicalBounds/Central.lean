module
public import Theory.SpecificGroups.Triality.StandardTwoRank.Sylow.RadicalBounds.Pairing
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ElementaryImage

/-!
# Elementary subgroups of the central radical

If the first cubic coordinate vanishes, the remaining two cubic coordinates
have isotropic span for the nondegenerate trace hyperbolic form. Their order
is at most q³, and the two singleton coordinates contribute at most q².

Otherwise the first-coordinate kernel lies in the elementary tail by
`central_elementary_kernel_mem_tail`. Commutation places its third coordinate
in the trace annihilator of the k-span W of the first image. Counting the
actual homomorphism kernel and range, and using |W| |Wᗮ| = q³, gives q⁵.
Neither normality nor scalar closure of the elementary subgroup is assumed.
All coordinates and multiplication belong to the actual descended radical,
and both arguments include q = 2.

Source: GLS3 2.4.5(b)(4) and §2.6 (`refs/KGroup/GLS3/chapter2.tex`),
for the triality rank used on printed p.356 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.Parabolics
open Triality.Standard.Parabolics.CentralRootSquare
open Triality.Standard.Parabolics.CentralRootSquare.ElementaryImage
namespace Triality.Standard.TwoRank.RadicalBounds

private theorem elementary_commute (P : Parameters) (E : Subgroup (radical P .central))
    [IsElementaryAbelian 2 E] (r s : E) : Commute r.val s.val := by
  let : CommGroup E := IsMulCommutative.instCommGroup
  exact congrArg (fun z : E => z.val) (mul_comm r s)

private theorem multiply_eq_of_commute (P : Parameters) (hp : P.prime = 2)
    (v w : RootOrbitParameters P .central)
    (h : Commute (coordinates P hp v) (coordinates P hp w)) :
    multiply P v w = multiply P w v :=
  (coordinates P hp).injective ((coordinates_multiply P hp v w).trans
    (h.eq.trans (coordinates_multiply P hp w v).symm))

/-- If the first cubic image vanishes, the two remaining cubic coordinates
have isotropic span for the trace hyperbolic form. -/
theorem central_card_le_of_first_zero (P : Parameters) (hp : P.prime = 2)
    (E : Subgroup (radical P .central)) [IsElementaryAbelian 2 E]
    (hzero : ∀ r : E, (firstLayer P hp r.val).1 = 0) : Nat.card E ≤ P.q ^ 5 := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  let v : E → RootOrbitParameters P .central := fun r => (coordinates P hp).symm r.val
  have hv0 (r : E) : (v r).1 0 = 0 := hzero r
  let x : E → ExtensionField P × ExtensionField P := fun r => ((v r).1 1, (v r).1 2)
  let W := Submodule.span (fixedField P) (Set.range x)
  have hpair (r s : E) : hyperbolic (traceForm P) (x r) (x s) = 0 := by
    have hc : Commute (coordinates P hp (v r)) (coordinates P hp (v s)) := by
      simpa only [v, Equiv.apply_symm_apply] using elementary_commute P E r s
    have h := congrArg (fun z : RootOrbitParameters P .central => z.2 1)
      (multiply_eq_of_commute P hp (v r) (v s) hc)
    simp only [multiply, Matrix.cons_val_one, Matrix.cons_val_zero, hv0, higherCoefficient, map_zero,
      zero_mul, mul_zero, add_zero, armsPairing_zero_right] at h
    change armsPairing P ((v r).1 1) ((v s).1 2) +
      armsPairing P ((v s).1 1) ((v r).1 2) = 0
    apply CharTwo.add_eq_zero.mpr
    linear_combination -h
  have hsq : Nat.card W ^ 2 ≤ P.q ^ 6 := by
    have h := card_span_sq_le (hyperbolic (traceForm P))
      (hyperbolic_nondegenerate _ (traceForm_nondegenerate P hp)) (Set.range x)
      (by rintro _ ⟨r, rfl⟩ _ ⟨s, rfl⟩; exact hpair r s)
    simpa only [Nat.card_prod, card_extensionField, ← pow_add] using h
  have hW : Nat.card W ≤ P.q ^ 3 := by
    have he : P.q ^ 6 = (P.q ^ 3) ^ 2 := by ring
    rw [he] at hsq
    exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsq
  let g : E → W × (Fin 2 → fixedField P) := fun r =>
    (⟨x r, Submodule.subset_span ⟨r, rfl⟩⟩, (v r).2)
  have hg : Function.Injective g := by
    intro r s hrs
    have hx : x r = x s := congrArg (fun z : W × (Fin 2 → fixedField P) => z.1.val) hrs
    have hz : (v r).2 = (v s).2 := congrArg (fun z : W × (Fin 2 → fixedField P) => z.2) hrs
    apply Subtype.ext
    apply (coordinates P hp).symm.injective
    apply Prod.ext
    · funext i
      fin_cases i
      · exact (hv0 r).trans (hv0 s).symm
      · exact congrArg Prod.fst hx
      · exact congrArg Prod.snd hx
    · exact hz
  calc
    Nat.card E ≤ Nat.card (W × (Fin 2 → fixedField P)) := Nat.card_le_card_of_injective g hg
    _ = Nat.card W * P.q ^ 2 := by
      rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, card_fixedField]
    _ ≤ P.q ^ 3 * P.q ^ 2 := Nat.mul_le_mul_right _ hW
    _ = P.q ^ 5 := by ring

private def firstHom (P : Parameters) (hp : P.prime = 2) :
    radical P .central →* Multiplicative (ExtensionField P) where
  toFun r := Multiplicative.ofAdd (firstLayer P hp r).1
  map_one' := by simp [firstLayer_one]
  map_mul' r s := by
    change (firstLayer P hp (r * s)).1 = (firstLayer P hp r).1 + (firstLayer P hp s).1
    rw [firstLayer_mul]
    rfl

/-- With nonzero first image, the kernel lies in the tail. Commutation
places its third coordinate in the annihilator of the span of that image. -/
theorem central_card_le_of_first_nonzero (P : Parameters) (hp : P.prime = 2)
    (E : Subgroup (radical P .central)) [IsElementaryAbelian 2 E]
    (r : E) (hr : (firstLayer P hp r.val).1 ≠ 0) : Nat.card E ≤ P.q ^ 5 := by
  let f : E →* Multiplicative (ExtensionField P) := (firstHom P hp).comp E.subtype
  let v : E → RootOrbitParameters P .central := fun s => (coordinates P hp).symm s.val
  let a : E → ExtensionField P := fun s => (f s).toAdd
  let W := Submodule.span (fixedField P) (Set.range a)
  let T := (traceForm P).orthogonal W
  have hu0 (u : f.ker) : (v u.val).1 0 = 0 :=
    congrArg Multiplicative.toAdd u.property
  have hu1 (u : f.ker) : (v u.val).1 1 = 0 := by
    obtain ⟨t, ht⟩ := central_elementary_kernel_mem_tail P hp E r.val u.val.val
      r.property u.val.property hr (hu0 u)
    change coordinates P hp (tailParameters P t.toAdd) = u.val.val at ht
    have he : tailParameters P t.toAdd = v u.val := by
      simpa only [Equiv.symm_apply_apply] using
        congrArg (coordinates P hp).symm ht
    rw [← he]
    rfl
  have hpair (s : E) (u : f.ker) : armsPairing P (a s) ((v u.val).1 2) = 0 := by
    have hc : Commute (coordinates P hp (v s)) (coordinates P hp (v u.val)) := by
      simpa only [v, Equiv.apply_symm_apply] using elementary_commute P E s u.val
    have h := congrArg (fun z : RootOrbitParameters P .central => z.2 0)
      (multiply_eq_of_commute P hp (v s) (v u.val) hc)
    simp only [multiply, Matrix.cons_val_zero, hu0, hu1, armsPairing_zero_left,
      map_zero, mul_zero, zero_mul, add_zero] at h
    change armsPairing P ((v s).1 0) ((v u.val).1 2) = 0
    linear_combination -h
  have hT (u : f.ker) : (v u.val).1 2 ∈ T := by
    intro z hz
    exact Submodule.span_induction
      (by rintro _ ⟨s, rfl⟩; exact hpair s u)
      (by simp)
      (fun x y _ _ hx hy => by simp [map_add, hx, hy])
      (fun t x _ hx => by simp [map_smul, hx]) hz
  let i : f.range → W := fun z => ⟨z.val.toAdd, by
    obtain ⟨s, hs⟩ := z.property
    exact Submodule.subset_span ⟨s, congrArg Multiplicative.toAdd hs⟩⟩
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact congrArg (fun z : W => z.val) h
  have hA : Nat.card f.range ≤ Nat.card W := Nat.card_le_card_of_injective i hi
  let j : f.ker → T × (Fin 2 → fixedField P) := fun u => (⟨(v u.val).1 2, hT u⟩, (v u.val).2)
  have hj : Function.Injective j := by
    intro u w huw
    have hx : (v u.val).1 2 = (v w.val).1 2 :=
      congrArg (fun z : T × (Fin 2 → fixedField P) => z.1.val) huw
    have hz : (v u.val).2 = (v w.val).2 := congrArg (fun z : T × (Fin 2 → fixedField P) => z.2) huw
    apply Subtype.ext
    apply Subtype.ext
    apply (coordinates P hp).symm.injective
    apply Prod.ext
    · funext k
      fin_cases k
      · exact (hu0 u).trans (hu0 w).symm
      · exact (hu1 u).trans (hu1 w).symm
      · exact hx
    · exact hz
  have hK : Nat.card f.ker ≤ Nat.card T * P.q ^ 2 := by
    simpa only [Nat.card_prod, Nat.card_fun, Nat.card_fin, card_fixedField] using
      Nat.card_le_card_of_injective j hj
  have hdual : Nat.card W * Nat.card T = P.q ^ 3 := by
    rw [← card_extensionField P]
    exact card_mul_card_orthogonal (traceForm P) (traceForm_nondegenerate P hp) W
  calc
    Nat.card E = Nat.card f.range * Nat.card f.ker := by
      rw [← Subgroup.index_ker f]
      exact f.ker.index_mul_card.symm
    _ ≤ Nat.card W * (Nat.card T * P.q ^ 2) := Nat.mul_le_mul hA hK
    _ = P.q ^ 5 := by rw [← mul_assoc, hdual]; ring

/-- The central-radical branch, including both possible first-coordinate images. -/
theorem central_radical_card_le (P : Parameters) (hp : P.prime = 2)
    (E : Subgroup (radical P .central)) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ P.q ^ 5 := by
  by_cases h : ∃ r : E, (firstLayer P hp r.val).1 ≠ 0
  · obtain ⟨r, hr⟩ := h
    exact central_card_le_of_first_nonzero P hp E r hr
  · push Not at h
    exact central_card_le_of_first_zero P hp E h

end Triality.Standard.TwoRank.RadicalBounds
