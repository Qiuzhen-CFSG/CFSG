module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.Recurrence
/-!
# Unique unipotent and refined Bruhat coordinates

For every marked Weyl element w, multiplication gives an equivalence
`(U ∩ U^w) × U_w ≃ U`. The root recurrence proves the complementary
order identity by induction on length; opposite-Borel disjointness makes
multiplication injective. Factoring the right Borel as UH then yields
the literal equality `Bn_wB = Bn_wU_w` and a unique pair of coordinates
for any supplied representative n_w in the original N.

Source: Carter 2.5.12–2.5.13, `refs/KGroup/GLS3/Chapter2Ca2.tex`.
These are equivalences of types; no commuting-factor assertion is made.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (d : MarkedQuotient P) (split : SplitData d.tits)

/-- Opposite disjointness gives trivial root stabilizers for every Weyl class. -/
theorem rootIntersection_disjoint_conjugateBorel (w : Weyl d) :
    Disjoint (rootIntersection split (longest d) w) (borelConjugate w) := by
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro x hx
  let n₀ := representative (longest d)
  let nw := representative w
  have hxR := hx.1.2
  rw [unipotentConjugate_eq split _ (n₀*nw)
    (by rw [map_mul, representative_spec, representative_spec])] at hxR
  have hzero : (nw : X ⧸ d.D) * x * (nw : X ⧸ d.D)⁻¹ ∈
      d.tits.B ⊓ unipotentConjugate split (longest d) := by
    refine ⟨hx.2, ?_⟩
    change (n₀ : X ⧸ d.D) * ((nw : X ⧸ d.D) * x * (nw : X ⧸ d.D)⁻¹) *
      (n₀ : X ⧸ d.D)⁻¹ ∈ split.U
    change ((n₀ : X ⧸ d.D) * (nw : X ⧸ d.D)) * x *
      ((n₀ : X ⧸ d.D) * (nw : X ⧸ d.D))⁻¹ ∈ split.U at hxR
    simpa only [mul_inv_rev, mul_assoc] using hxR
  rw [borel_inf_opposite_unipotent d split, mem_bot] at hzero
  apply (MulAut.conj (nw : X ⧸ d.D)).injective
  simpa only [MulAut.conj_apply, map_one] using hzero

/-- The root and its complementary intersection have the full order of U. -/
theorem rootIntersection_card_complement (w : Weyl d) :
    Nat.card split.U = Nat.card (rootIntersection split (longest d) (longest d*w)) *
      Nat.card (rootIntersection split (longest d) w) := by
  generalize hn : d.tits.wordLength w = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hw : w = 1
    · subst w
      rw [mul_one, rootIntersection_longest, rootIntersection_one]
      simp
    · obtain ⟨v, i, rfl, hstep⟩ := exists_right_reduced_step d hw
      have hv : d.tits.wordLength v < n := by omega
      have hrec := ih _ hv v rfl
      have hs : d.simple i*d.simple i = 1 := by
        simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem i)).2
      have hcomp : d.tits.wordLength ((longest d*(v*d.simple i))*d.simple i) =
          d.tits.wordLength (longest d*(v*d.simple i))+1 := by
        simp only [mul_assoc, hs, mul_one]
        rw [length_longest_mul, length_longest_mul, hstep]
        have := wordLength_le_rotationOrder d (v*d.simple i)
        omega
      have hc := rootIntersection_card_ascent d split (longest d*(v*d.simple i)) i hcomp
      simp only [mul_assoc, hs, mul_one] at hc
      rw [hc] at hrec
      rw [rootIntersection_card_ascent d split v i hstep]
      exact hrec.trans (by ac_rfl)

private def unipotentMul (w : Weyl d) :
    (split.U ⊓ unipotentConjugate split w : Subgroup (X ⧸ d.D)) ×
      rootIntersection split (longest d) w → split.U :=
  fun p => ⟨(p.1 : X ⧸ d.D)*p.2, split.U.mul_mem p.1.property.1 p.2.property.1⟩

private theorem unipotentMul_bijective (w : Weyl d) : Function.Bijective (unipotentMul d split w) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro p q hpq
    have hd : Disjoint (split.U ⊓ unipotentConjugate split w)
        (rootIntersection split (longest d) w) :=
      (rootIntersection_disjoint_conjugateBorel d split w).symm.mono_left
        (inf_le_right.trans (comap_mono split.U_le))
    exact mul_injective_of_disjoint hd (congrArg Subtype.val hpq)
  · rw [Nat.card_prod, ← rootIntersection_complement, ← rootIntersection_card_complement]

/-- Carter 2.5.12, as a type equivalence rather than a direct product of groups. -/
def unipotentCoordinates (w : Weyl d) :
    (split.U ⊓ unipotentConjugate split w : Subgroup (X ⧸ d.D)) ×
      rootIntersection split (longest d) w ≃ split.U :=
  Equiv.ofBijective (unipotentMul d split w) (unipotentMul_bijective d split w)

@[simp] theorem unipotentCoordinates_apply (w : Weyl d)
    (v : (split.U ⊓ unipotentConjugate split w : Subgroup (X ⧸ d.D)))
    (u : rootIntersection split (longest d) w) :
    (unipotentCoordinates d split w (v,u) : X ⧸ d.D) = (v : X ⧸ d.D)*u := by rfl

theorem unipotent_complement_product (w : Weyl d) :
    ((split.U ⊓ unipotentConjugate split w : Subgroup (X ⧸ d.D)) : Set (X ⧸ d.D)) *
      (rootIntersection split (longest d) w : Set (X ⧸ d.D)) = split.U := by
  apply Set.Subset.antisymm
  · rintro x ⟨v, hv, u, hu, rfl⟩
    exact split.U.mul_mem hv.1 hu.1
  · intro x hx
    obtain ⟨p, hp⟩ := (unipotentCoordinates d split w).surjective ⟨x,hx⟩
    exact ⟨p.1, p.1.property, p.2, p.2.property, congrArg Subtype.val hp⟩

/-- Carter 2.5.13 with any representative in the actual N. -/
theorem bruhat_root_existence (w : Weyl d) (nw : d.tits.N)
    (hnw : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) nw = w)
    (x : X ⧸ d.D) (hx : x ∈ d.tits.bruhatCell w) :
    ∃ (b : d.tits.B) (u : rootIntersection split (longest d) w),
      (b : X ⧸ d.D)*nw*u = x := by
  rw [bruhatCell, B_mul_representativeSet_mul_B d.tits.B d.tits.N w nw hnw] at hx
  obtain ⟨b, hb, c, hc, he⟩ := DoubleCoset.mem_doubleCoset.mp hx
  have hc' : c ∈ (rightConjugate d.tits.B (1 : d.tits.N) : Set (X ⧸ d.D)) := by
    simpa only [coe_one, rightConjugate_one] using hc
  rw [borel_conjugate_factorization split 1, coe_one, rightConjugate_one] at hc'
  obtain ⟨u, hu, h, hh, huh⟩ := hc'
  have hu' : h⁻¹*u*h ∈ split.U :=
    by
    have hhN := split.normalizes (d.tits.B.inv_mem hh.1)
    have hhU := (mem_normalizer_iff.mp hhN u).mp hu
    simpa only [inv_inv] using hhU
  have hcH : c = h*(h⁻¹*u*h) := by rw [← huh]; simp only [mul_assoc, mul_inv_cancel_left]
  obtain ⟨p, hp⟩ := (unipotentCoordinates d split w).surjective ⟨h⁻¹*u*h, hu'⟩
  have hprod : (p.1 : X ⧸ d.D)*p.2 = h⁻¹*u*h := congrArg Subtype.val hp
  have hv : (nw : X ⧸ d.D)*(p.1 : X ⧸ d.D)*(nw : X ⧸ d.D)⁻¹ ∈ split.U := by
    have hle : split.U ⊓ unipotentConjugate split w ≤
        rightConjugate split.U (nw : X ⧸ d.D) := by
      rw [unipotentConjugate_eq split w nw hnw]
      exact inf_le_right
    exact hle p.1.property
  have ht : (nw : X ⧸ d.D)*h*(nw : X ⧸ d.D)⁻¹ ∈ d.tits.B ⊓ d.tits.N :=
    (mem_normalizer_iff.mp (torus_normalizes nw) h).mp hh
  refine ⟨⟨b*((nw : X ⧸ d.D)*h*(nw : X ⧸ d.D)⁻¹)*
    ((nw : X ⧸ d.D)*(p.1 : X ⧸ d.D)*(nw : X ⧸ d.D)⁻¹),
    d.tits.B.mul_mem (d.tits.B.mul_mem hb ht.1) (split.U_le hv)⟩, p.2, ?_⟩
  change b*((nw : X ⧸ d.D)*h*(nw : X ⧸ d.D)⁻¹)*
    ((nw : X ⧸ d.D)*(p.1 : X ⧸ d.D)*(nw : X ⧸ d.D)⁻¹)*nw*p.2 = x
  rw [he, hcH, ← hprod]
  simp only [mul_assoc, inv_mul_cancel_left]

private def bruhatMul (w : Weyl d) (nw : d.tits.N)
    (hnw : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) nw = w) :
    d.tits.B × rootIntersection split (longest d) w → d.tits.bruhatCell w :=
  fun p => ⟨(p.1 : X ⧸ d.D)*nw*p.2,
    mul_mem_doubleCoset d.tits.B d.tits.N w p.1.property (split.U_le p.2.property.1)
      (d.tits.representative_mem_bruhatCell w nw hnw)⟩

private theorem bruhatMul_bijective (w : Weyl d) (nw : d.tits.N)
    (hnw : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) nw = w) :
    Function.Bijective (bruhatMul d split w nw hnw) := by
  constructor
  · rintro ⟨b,u⟩ ⟨c,v⟩ h
    have he : (b : X ⧸ d.D)*nw*u = (c : X ⧸ d.D)*nw*v := congrArg Subtype.val h
    have hdiff : (u : X ⧸ d.D)*(v : X ⧸ d.D)⁻¹ ∈ borelConjugate w := by
      rw [borelConjugate_eq w nw hnw]
      change (nw : X ⧸ d.D)*((u : X ⧸ d.D)*(v : X ⧸ d.D)⁻¹)*(nw : X ⧸ d.D)⁻¹ ∈ d.tits.B
      have hd : (nw : X ⧸ d.D)*((u : X ⧸ d.D)*(v : X ⧸ d.D)⁻¹)*(nw : X ⧸ d.D)⁻¹ =
          (b : X ⧸ d.D)⁻¹*c := by
        have hz := congrArg (fun z : X ⧸ d.D => (b : X ⧸ d.D)⁻¹*z*(v : X ⧸ d.D)⁻¹*(nw : X ⧸ d.D)⁻¹) he
        simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hz
      rw [hd]
      exact d.tits.B.mul_mem (d.tits.B.inv_mem b.property) c.property
    have huv : u = v := by
      apply Subtype.ext
      apply mul_inv_eq_one.mp
      exact mem_bot.mp ((disjoint_iff.mp (rootIntersection_disjoint_conjugateBorel d split w)) ▸
        (show (u : X ⧸ d.D)*(v : X ⧸ d.D)⁻¹ ∈
          rootIntersection split (longest d) w ⊓ borelConjugate w from
            ⟨mul_mem u.property ((rootIntersection split (longest d) w).inv_mem v.property), hdiff⟩))
    subst v
    have hbc : b = c := Subtype.ext (mul_right_cancel (mul_right_cancel he))
    subst c
    rfl
  · intro x
    obtain ⟨b,u,he⟩ := bruhat_root_existence d split w nw hnw x x.property
    exact ⟨(b,u), Subtype.ext he⟩

/-- Unique actual B n_w U_w coordinates, with no group direct-product claim. -/
def bruhatCoordinates (w : Weyl d) (nw : d.tits.N)
    (hnw : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) nw = w) :
    d.tits.B × rootIntersection split (longest d) w ≃ d.tits.bruhatCell w :=
  Equiv.ofBijective (bruhatMul d split w nw hnw) (bruhatMul_bijective d split w nw hnw)

@[simp] theorem bruhatCoordinates_apply (w : Weyl d) (nw : d.tits.N)
    (hnw : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) nw = w)
    (b : d.tits.B) (u : rootIntersection split (longest d) w) :
    (bruhatCoordinates d split w nw hnw (b,u) : X ⧸ d.D) = (b : X ⧸ d.D)*nw*u := by rfl

/-- The literal refined Bruhat-cell set identity. -/
theorem bruhatCell_eq_borel_representative_root (w : Weyl d) (nw : d.tits.N)
    (hnw : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) nw = w) :
    d.tits.bruhatCell w = (d.tits.B : Set (X ⧸ d.D)) *
      {(nw : X ⧸ d.D)} * (rootIntersection split (longest d) w : Set (X ⧸ d.D)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨b,u,he⟩ := bruhat_root_existence d split w nw hnw x hx
    exact ⟨(b : X ⧸ d.D)*nw, ⟨b,b.property,nw,rfl,rfl⟩,u,u.property,he⟩
  · rintro ⟨z, ⟨b,hb,n,hn,rfl⟩,u,hu,rfl⟩
    obtain rfl : n = (nw : X ⧸ d.D) := hn
    exact (bruhatMul d split w nw hnw (⟨b,hb⟩,⟨u,hu⟩)).property

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
