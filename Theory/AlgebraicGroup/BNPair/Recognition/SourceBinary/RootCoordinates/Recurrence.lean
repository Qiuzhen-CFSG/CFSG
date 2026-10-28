module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.ReducedProducts
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.SimpleCoordinates
/-!
# The split-root recurrence along reduced right steps

If `l(wsᵢ) = l(w)+1`, the literal intersections satisfy
`U_(wsᵢ) = Xᵢ (U_w)^nᵢ`, with disjoint factors and unique multiplication
coordinates. Reduced-product monotonicity first places Xᵢ in the larger
intersection. Carter's ascent intersection lemma places `(U_w)^nᵢ` in Vᵢ.
Intersecting the already proved factorization `U = Xᵢ Vᵢ` then gives the
recurrence directly, using the finite normal Sylow to pass from B to U.
Every lift belongs to the supplied N, and all conjugations are right
conjugations. The cardinality recurrence therefore uses the same two roots.

Source: Carter 2.5.7–2.5.10 in `refs/KGroup/GLS3/Chapter2Ca2.tex`.
No commutator law, field realization or prescribed dihedral order is used.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {T : TitsSystem (X := X)}

theorem rightConjugate_inf (A C : Subgroup X) (n : X) :
    rightConjugate (A ⊓ C) n = rightConjugate A n ⊓ rightConjugate C n := rfl

theorem unipotentConjugate_one (split : SplitData T) : unipotentConjugate split 1 = split.U := by
  rw [unipotentConjugate_eq split 1 1 (map_one _)]
  exact rightConjugate_one _

theorem unipotentConjugate_right (split : SplitData T)
    (v w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) (n : T.N)
    (hn : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n = w) :
    rightConjugate (unipotentConjugate split v) (n : X) = unipotentConjugate split (v*w) := by
  rw [unipotentConjugate, ← rightConjugate_mul,
    unipotentConjugate_eq split (v*w) (representative v*n)
      (by rw [map_mul, representative_spec, hn])]
  rfl

theorem two_subgroup_le_conjugate [Finite X] (split : SplitData T)
    (K : Subgroup X) (hK : IsPGroup 2 K)
    (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) (hKB : K ≤ borelConjugate w) :
    K ≤ unipotentConjugate split w := by
  let f := (MulAut.conj (representative w : X)).toMonoidHom
  have hmap : K.map f ≤ T.B := by
    rintro x ⟨y, hy, rfl⟩
    exact hKB hy
  have h := two_subgroup_le_unipotent split (K.map f) (hK.map f) hmap
  intro x hx
  exact h ⟨x, hx, rfl⟩

theorem card_rightConjugate (A : Subgroup X) (n : X) :
    Nat.card (rightConjugate A n) = Nat.card A := by
  rw [rightConjugate, comap_equiv_eq_map_symm']
  exact card_map_of_injective (MulAut.conj n).symm.injective

variable {P : Fin 2 → Subgroup X} (d : MarkedQuotient P) (split : SplitData d.tits)

private theorem simple_inv (i : Fin 2) : (d.simple i)⁻¹ = d.simple i :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem i)).2)

/-- Carter 2.5.7(i), with positivity expressed by the actual word length. -/
theorem simpleRoot_le_ascent_intersection (w : Weyl d) (i : Fin 2)
    (hlen : d.tits.wordLength (w*d.simple i) = d.tits.wordLength w+1) :
    simpleRoot d split i ≤ split.U ⊓ unipotentConjugate split w := by
  have hlen' : d.tits.wordLength ((longest d*d.simple i*w⁻¹)*w) =
      d.tits.wordLength (longest d*d.simple i*w⁻¹)+d.tits.wordLength w := by
    have he : longest d*d.simple i*w⁻¹ = longest d*(w*d.simple i)⁻¹ := by
      rw [mul_inv_rev, simple_inv, mul_assoc]
    rw [inv_mul_cancel_right, wordLength_longest_mul_simple, he, length_longest_mul_inv, hlen]
    have := wordLength_le_rotationOrder d (w*d.simple i)
    omega
  have hB := borel_intersection_reduced_mul_le d (longest d*d.simple i*w⁻¹) w hlen'
  rw [inv_mul_cancel_right] at hB
  apply le_inf (simpleRoot_le d split i)
  apply two_subgroup_le_conjugate split _ (rootIntersection_isTwo split _ _) w
  intro x hx
  apply (hB ?_).2
  exact ⟨split.U_le hx.1, (comap_mono split.U_le) hx.2⟩

/-- At a right ascent the conjugated old root intersection lies in Vᵢ. -/
theorem ascent_root_conjugate_le_remainder (w : Weyl d) (i : Fin 2)
    (hlen : d.tits.wordLength (w*d.simple i) = d.tits.wordLength w+1)
    (ni : d.tits.N)
    (hni : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) ni = d.simple i) :
    rightConjugate (rootIntersection split (longest d) w) (ni : X ⧸ d.D) ≤
      simpleRemainder d split i := by
  let a := longest d*w*d.simple i
  let nv := representative a⁻¹
  have hnv : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) nv = a⁻¹ :=
    representative_spec _
  have hstep : d.tits.wordLength a⁻¹ ≤ d.tits.wordLength (d.simple i*a⁻¹) := by
    have he : d.simple i*a⁻¹ = (longest d*w)⁻¹ := by
      have hss : d.simple i*d.simple i = 1 := by
        simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem i)).2
      simp only [a, mul_inv_rev, simple_inv, ← mul_assoc, hss, one_mul]
    rw [he, wordLength_inv, wordLength_inv]
    dsimp only [a]
    rw [mul_assoc, length_longest_mul, length_longest_mul, hlen]
    exact Nat.sub_le_sub_left (by omega) _
  have hB := ascent_conjugate_intersection_le (d.simple_mem i) hstep ni nv hni hnv
  have he : rightConjugate (rootIntersection split (longest d) w) (ni : X ⧸ d.D) =
      unipotentConjugate split (d.simple i) ⊓ unipotentConjugate split a := by
    rw [rootIntersection, rightConjugate_inf,
      ← unipotentConjugate_eq split (d.simple i) ni hni,
      unipotentConjugate_right split _ _ ni hni]
  have hUB : rightConjugate (rootIntersection split (longest d) w) (ni : X ⧸ d.D) ≤ d.tits.B := by
    rw [he]
    intro x hx
    apply hB
    constructor
    · have hx1 := hx.1
      rw [unipotentConjugate_eq split _ ni hni] at hx1
      exact (comap_mono split.U_le) hx1
    · change x ∈ rightConjugate d.tits.B (nv⁻¹ : d.tits.N)
      rw [← borelConjugate_eq a nv⁻¹ (by rw [map_inv, hnv, inv_inv])]
      exact (comap_mono split.U_le) hx.2
  have hU := two_subgroup_le_unipotent split _
    ((rootIntersection_isTwo split (longest d) w).comap_of_injective
      (MulAut.conj (ni : X ⧸ d.D)).toMonoidHom (MulAut.conj (ni : X ⧸ d.D)).injective) hUB
  exact le_inf hU (he ▸ inf_le_left)

/-- Carter 2.5.10: a right ascent adds the same actual simple root. -/
theorem rootIntersection_ascent_product (w : Weyl d) (i : Fin 2)
    (hlen : d.tits.wordLength (w*d.simple i) = d.tits.wordLength w+1)
    (ni : d.tits.N)
    (hni : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) ni = d.simple i) :
    (rootIntersection split (longest d) (w*d.simple i) : Set (X ⧸ d.D)) =
      (simpleRoot d split i : Set (X ⧸ d.D)) *
        (rightConjugate (rootIntersection split (longest d) w) (ni : X ⧸ d.D) : Set (X ⧸ d.D)) := by
  have hle := ascent_root_conjugate_le_remainder d split w i hlen ni hni
  have he : rightConjugate (rootIntersection split (longest d) w) (ni : X ⧸ d.D) =
      unipotentConjugate split (d.simple i) ⊓
        unipotentConjugate split (longest d*(w*d.simple i)) := by
    rw [rootIntersection, rightConjugate_inf,
      ← unipotentConjugate_eq split (d.simple i) ni hni,
      unipotentConjugate_right split _ _ ni hni, mul_assoc]
  have hpos : d.tits.wordLength ((longest d*(w*d.simple i))*d.simple i) =
      d.tits.wordLength (longest d*(w*d.simple i))+1 := by
    have hss : d.simple i*d.simple i = 1 := by
      simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem i)).2
    simp only [mul_assoc, hss, mul_one]
    rw [length_longest_mul, length_longest_mul, hlen]
    have := wordLength_le_rotationOrder d (w*d.simple i)
    omega
  have hX := simpleRoot_le_ascent_intersection d split (longest d*(w*d.simple i)) i hpos
  apply Set.Subset.antisymm
  · intro x hx
    have hu : x ∈ (split.U : Set (X ⧸ d.D)) := hx.1
    rw [← simpleRoot_mul_remainder d split i] at hu
    obtain ⟨r, hr, v, hv, hrv⟩ := hu
    have hvK : v ∈ rootIntersection split (longest d) (w*d.simple i) := by
      have hrK : r ∈ rootIntersection split (longest d) (w*d.simple i) := hX hr
      have hh := (rootIntersection split (longest d) (w*d.simple i)).mul_mem
        (inv_mem hrK) hx
      rwa [← hrv, inv_mul_cancel_left] at hh
    exact ⟨r, hr, v, he ▸ ⟨hv.2, hvK.2⟩, hrv⟩
  · rintro x ⟨r, hr, v, hv, rfl⟩
    exact (rootIntersection split (longest d) (w*d.simple i)).mul_mem (hX hr)
      ⟨(hle hv).1, (he ▸ hv).2⟩

theorem rootIntersection_ascent_disjoint (w : Weyl d) (i : Fin 2)
    (hlen : d.tits.wordLength (w*d.simple i) = d.tits.wordLength w+1)
    (ni : d.tits.N)
    (hni : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) ni = d.simple i) :
    Disjoint (simpleRoot d split i)
      (rightConjugate (rootIntersection split (longest d) w) (ni : X ⧸ d.D)) :=
  (simpleRoot_disjoint_remainder d split i).mono_right
    (ascent_root_conjugate_le_remainder d split w i hlen ni hni)

/-- Unique multiplication coordinates at a right ascent, for the supplied lift. -/
def ascentCoordinates (w : Weyl d) (i : Fin 2)
    (hlen : d.tits.wordLength (w*d.simple i) = d.tits.wordLength w+1)
    (ni : d.tits.N)
    (hni : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) ni = d.simple i) :
    simpleRoot d split i × rightConjugate (rootIntersection split (longest d) w) (ni : X ⧸ d.D) ≃
      rootIntersection split (longest d) (w*d.simple i) :=
  Equiv.ofBijective (fun p => ⟨(p.1 : X ⧸ d.D)*p.2,
    by
      change (p.1 : X ⧸ d.D)*p.2 ∈ (rootIntersection split (longest d) (w*d.simple i) : Set (X ⧸ d.D))
      rw [rootIntersection_ascent_product d split w i hlen ni hni]
      exact ⟨p.1, p.1.property, p.2, p.2.property, rfl⟩⟩) (by
    constructor
    · intro p q hpq
      exact mul_injective_of_disjoint (rootIntersection_ascent_disjoint d split w i hlen ni hni)
        (congrArg Subtype.val hpq)
    · intro x
      have hx : (x : X ⧸ d.D) ∈ (rootIntersection split (longest d) (w*d.simple i) : Set (X ⧸ d.D)) := x.property
      rw [rootIntersection_ascent_product d split w i hlen ni hni] at hx
      obtain ⟨r, hr, v, hv, he⟩ := hx
      exact ⟨(⟨r, hr⟩, ⟨v, hv⟩), Subtype.ext he⟩)

@[simp] theorem ascentCoordinates_apply (w : Weyl d) (i : Fin 2)
    (hlen : d.tits.wordLength (w*d.simple i) = d.tits.wordLength w+1)
    (ni : d.tits.N)
    (hni : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) ni = d.simple i)
    (r : simpleRoot d split i)
    (v : rightConjugate (rootIntersection split (longest d) w) (ni : X ⧸ d.D)) :
    (ascentCoordinates d split w i hlen ni hni (r,v) : X ⧸ d.D) = (r : X ⧸ d.D)*v := by rfl

theorem rootIntersection_card_ascent (w : Weyl d) (i : Fin 2)
    (hlen : d.tits.wordLength (w*d.simple i) = d.tits.wordLength w+1) :
    Nat.card (rootIntersection split (longest d) (w*d.simple i)) =
      Nat.card (simpleRoot d split i)*Nat.card (rootIntersection split (longest d) w) := by
  rw [← Nat.card_congr (ascentCoordinates d split w i hlen
    (representative (d.simple i)) (representative_spec _)), Nat.card_prod, card_rightConjugate]

theorem rootIntersection_one : rootIntersection split (longest d) 1 = ⊥ := by
  apply eq_bot_iff.mpr
  have h := inf_le_inf_right (unipotentConjugate split (longest d)) split.U_le
  rw [borel_inf_opposite_unipotent d split] at h
  simpa only [rootIntersection, mul_one] using h

theorem rootIntersection_longest : rootIntersection split (longest d) (longest d) = split.U := by
  rw [rootIntersection, longest_mul_self, unipotentConjugate_one, inf_idem]

theorem rootIntersection_complement (w : Weyl d) :
    rootIntersection split (longest d) (longest d*w) = split.U ⊓ unipotentConjugate split w := by
  rw [rootIntersection, ← mul_assoc, longest_mul_self, one_mul]

/-- Every nonidentity class has a reduced final letter among the original two markings. -/
theorem exists_right_reduced_step {w : Weyl d} (hw : w ≠ 1) :
    ∃ (v : Weyl d) (i : Fin 2), w = v*d.simple i ∧ d.tits.wordLength w = d.tits.wordLength v+1 := by
  obtain ⟨b, n, hn, he⟩ := exists_alternatingWord d w⁻¹
  cases n with
  | zero =>
    have hh : w⁻¹ = 1 := by simpa only [alternatingWord] using he.symm
    exact False.elim (hw (inv_eq_one.mp hh))
  | succ n =>
    refine ⟨(alternatingWord d (!b) n)⁻¹, if b then 1 else 0, ?_, ?_⟩
    · have hh := congrArg Inv.inv he
      simpa only [alternatingWord, mul_inv_rev, inv_inv, simple_inv] using hh.symm
    · rw [wordLength_inv, wordLength_alternatingWord d _ (by omega)]
      have hh := congrArg d.tits.wordLength he
      rw [wordLength_inv, wordLength_alternatingWord d b hn] at hh
      exact hh.symm

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
