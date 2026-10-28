module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Defs
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.SpecificGroups.HeisenbergPrime.Recognition
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Geometry
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.Coordinates
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus

/-!
# Four inner conjugates of entrywise conjugation on PSU₃

For a prime p > 5, choose k of order p+1 in the norm-one subgroup of
Eˣ. Its cube is not fixed by Hermitian conjugation, since otherwise k⁶=1.
The elementary identity (k+1)/conj(k+1)=k realizes its projective torus
matrix as a displacement of the entrywise actor.

Choose an upper root coordinate z with nonfixed first coordinate. Its
displacement d=z*conj(z)⁻¹ has nonzero trace-zero first coordinate.
The torus scales that coordinate by k³, so d and its torus conjugate do
not commute. A noncommuting pair generates a group of order p³. The
norm-one torus commutes with the Weyl element, which entrywise conjugation
fixes, so the same argument recovers the entire opposite root group.
The two root groups generate the inherited simple projective matrix group.

Thus the four conjugators are the identity, the torus matrix at k+1,
one upper root matrix, and its Weyl conjugate. Every conjugator lies in
PSU₃ itself. Padding this tuple supplies the five-conjugate bound without
any extra congruence restriction or assumption about automorphism classes.

This is a direct sufficient bound for the outer-involution generation input
in Guralnick–Malle, Classification of 2F-modules I, §2 and Proposition 4.3,
used in Aschbacher–Smith K.2, printed p.453. The coordinate and root-geometry
conventions are Huppert, Endliche Gruppen I, II.10.12. The four-conjugate
bound here is proved by the calculation above, rather than attributed to
the source's separate p=5 assertion.
-/

public section

open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Outer
open OddPrimeSylow.NormalizedOuter OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

private def coordConj (z : hermitianUnipotentCoord J) : hermitianUnipotentCoord J :=
  ⟨(J.conj z.val.1, J.conj z.val.2), by
    have h := congrArg J.conj z.property
    simpa only [map_add, map_mul, map_zero, J.conj_involutive] using h⟩

private def displacement (z : hermitianUnipotentCoord J) : hermitianUnipotentCoord J :=
  z * (coordConj J z)⁻¹

private theorem displacement_fst (z : hermitianUnipotentCoord J) :
    (displacement J z).val.1 = z.val.1 - J.conj z.val.1 := by
  change z.val.1 + -J.conj z.val.1 = _
  exact (sub_eq_add_neg _ _).symm

private def unitConj (k : Eˣ) : Eˣ := Units.map J.conj.toMonoidHom k

private theorem exists_torus_parameter [Finite E] {p : ℕ} (hp : 5 < p)
    (hcard : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p) :
    ∃ k l : Eˣ, J.conj (k : E) = (k : E)⁻¹ ∧
      J.conj ((k : E) ^ 3) ≠ (k : E) ^ 3 ∧ l * (unitConj J l)⁻¹ = k := by
  obtain ⟨k, hk⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := EvenInner.normOne J)
  rw [EvenInner.normOne_card J hcard hc] at hk
  have h6 : (k.val : E) ^ 6 ≠ 1 := by
    intro h
    have hh : k ^ 6 = 1 := Subtype.ext (Units.ext h)
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [hk] at hd
    have := Nat.le_of_dvd (by decide : 0 < 6) hd
    omega
  have hkconj : J.conj (k.val : E) = (k.val : E)⁻¹ := k.property
  have h3 : J.conj ((k.val : E) ^ 3) ≠ (k.val : E) ^ 3 := by
    intro h
    apply h6
    rw [map_pow, hkconj, inv_pow] at h
    calc
      (k.val : E) ^ 6 = (k.val : E) ^ 3 * (k.val : E) ^ 3 := by ring
      _ = ((k.val : E) ^ 3)⁻¹ * (k.val : E) ^ 3 := by rw [h]
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ (Units.ne_zero _))
  have hn : (k.val : E) + 1 ≠ 0 := by
    intro h
    have he : (k.val : E) = -1 := eq_neg_of_add_eq_zero_left h
    exact h6 (by rw [he]; norm_num)
  let l : Eˣ := Units.mk0 ((k.val : E) + 1) hn
  refine ⟨k.val, l, hkconj, h3, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_inv_eq_inv_val]
  change ((k.val : E) + 1) * (J.conj ((k.val : E) + 1))⁻¹ = (k.val : E)
  rw [← div_eq_mul_inv, div_eq_iff ((map_ne_zero J.conj).mpr hn)]
  rw [map_add, map_one, hkconj]
  field_simp
  ring

private theorem exists_moved [Finite E] {p : ℕ} (hp : 1 < p)
    (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p) :
    ∃ a : E, J.conj a ≠ a := by
  by_contra! hall
  let e : {x : E // J.conj x = x} ≃ E :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, hall x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := hfixed.symm.trans ((Nat.card_congr e).trans hcard)
  nlinarith

private theorem exists_displacement_generator [Finite E]
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0]) {p : ℕ} (hp : p.Prime)
    (h2 : (2 : E) ≠ 0) (hcard : Nat.card E = p ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = p)
    (k : Eˣ) (hk : J.conj (k : E) = (k : E)⁻¹)
    (hk3 : J.conj ((k : E) ^ 3) ≠ (k : E) ^ 3) :
    ∃ z : hermitianUnipotentCoord J,
      ∀ H : Subgroup (hermitianUnipotentCoord J),
        displacement J z ∈ H →
        hermitianTorusAction J k (displacement J z) ∈ H → H = ⊤ := by
  obtain ⟨a, ha⟩ := exists_moved J hp.one_lt hcard hfixed
  obtain ⟨z, hz⟩ := coord_first_surjective J h2 a
  change z.val.1 = a at hz
  let d := displacement J z
  have hd : d.val.1 ≠ 0 := by
    rw [displacement_fst, hz]
    exact sub_ne_zero.mpr ha.symm
  have hnd : J.conj d.val.1 = -d.val.1 := by
    rw [displacement_fst, map_sub, J.conj_involutive]
    ring
  have hn : d * hermitianTorusAction J k d ≠ hermitianTorusAction J k d * d := by
    intro he
    have he' := congrArg (fun v : hermitianUnipotentCoord J => v.val.2) he
    change d.val.2 + (hermitianTorusAction J k d).val.2 -
      d.val.1 * J.conj (hermitianTorusAction J k d).val.1 =
      (hermitianTorusAction J k d).val.2 + d.val.2 -
      (hermitianTorusAction J k d).val.1 * J.conj d.val.1 at he'
    rw [EvenInner.normOne_action_first J k hk, map_mul, hnd] at he'
    apply hk3
    apply mul_right_cancel₀ hd
    apply mul_right_cancel₀ hd
    linear_combination he'
  have hcoord : Nat.card (hermitianUnipotentCoord J) = p ^ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective (root_injective J hJ)).toEquiv).trans
      (rootGroup_card J hJ p hcard hfixed)
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨z, fun H hd ht => ?_⟩
  exact HeisenbergPrime.subgroup_eq_top_of_noncommuting hcoord H ⟨_, hd⟩ ⟨_, ht⟩
    (fun he => hn (congrArg Subtype.val he))

variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

private theorem entrywise_root (z : hermitianUnipotentCoord J) :
    entrywiseProjectiveAut J hJ (root J hJ z) = root J hJ (coordConj J z) := by
  have hp (v : hermitianUnipotentCoord J) : root J hJ v =
      J.specialToProjective (hermitianUnipotentSU J hJ v) := by
    apply Subtype.ext
    rw [hermitianUnipotentPSU_val, specialToProjective_apply_val]
    rfl
  rw [hp, entrywiseProjectiveAut_specialToProjective, hp]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [entrywiseSpecialAut_apply_val]
  change (hermitianUnipotentMatrix J z).map J.conj =
    hermitianUnipotentMatrix J (coordConj J z)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianUnipotentMatrix, coordConj]

private theorem entrywise_torus (k : Eˣ) :
    entrywiseProjectiveAut J hJ (hermitianTorusPSU J hJ k) =
      hermitianTorusPSU J hJ (unitConj J k) := by
  have hp (v : Eˣ) : hermitianTorusPSU J hJ v =
      J.specialToProjective (hermitianTorusSU J hJ v) := by
    apply Subtype.ext
    rw [hermitianTorusPSU_val, specialToProjective_apply_val]
    rfl
  rw [hp, entrywiseProjectiveAut_specialToProjective, hp]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [entrywiseSpecialAut_apply_val]
  change (hermitianTorusMatrix J k).map J.conj =
    hermitianTorusMatrix J (unitConj J k)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, unitConj]

private theorem entrywise_weyl : entrywiseProjectiveAut J hJ (weyl J hJ) = weyl J hJ := by
  have hp : weyl J hJ = J.specialToProjective (hermitianWeylSU J hJ) := by
    apply Subtype.ext
    rw [hermitianWeylPSU_val, specialToProjective_apply_val]
    rfl
  rw [hp, entrywiseProjectiveAut_specialToProjective]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [entrywiseSpecialAut_apply_val]
  change (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) E).map J.conj =
    hermitianWeylMatrix
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianWeylMatrix]

private theorem entrywise_opposite (z : hermitianUnipotentCoord J) :
    entrywiseProjectiveAut J hJ (oppositeRoot J hJ z) =
      oppositeRoot J hJ (coordConj J z) := by
  simp only [oppositeRoot_apply, map_mul, map_inv, entrywise_weyl, entrywise_root]

private theorem torus_opposite (k : Eˣ) (hk : J.conj (k : E) = (k : E)⁻¹)
    (z : hermitianUnipotentCoord J) :
    hermitianTorusPSU J hJ k * oppositeRoot J hJ z *
      (hermitianTorusPSU J hJ k)⁻¹ =
        oppositeRoot J hJ (hermitianTorusAction J k z) := by
  have hw := hermitianTorusPSU_commute_weyl_of_conj_eq_inv J hJ k hk
  have hu := hermitianTorusPSU_mul_unipotent J hJ k z
  rw [oppositeRoot_apply, oppositeRoot_apply]
  calc
    _ = weyl J hJ * (hermitianTorusPSU J hJ k * root J hJ z *
        (hermitianTorusPSU J hJ k)⁻¹) * (weyl J hJ)⁻¹ := by
      calc
        _ = (hermitianTorusPSU J hJ k * weyl J hJ) * root J hJ z *
            ((weyl J hJ)⁻¹ * (hermitianTorusPSU J hJ k)⁻¹) := by group
        _ = _ := by
          rw [hw, (show Commute (hermitianTorusPSU J hJ k) (weyl J hJ) from hw).inv_inv.eq.symm]
          group
    _ = _ := by rw [hu, mul_inv_cancel_right]

private theorem displacement_mem {G : Type*} [Group G]
    (a : MulAut G) (H : Subgroup (MulAut G)) (ha : a ∈ H) (s : G)
    (hs : MulAut.conj s * a * (MulAut.conj s)⁻¹ ∈ H) :
    s * (a s)⁻¹ ∈ H.comap (MulAut.conj : G →* MulAut G) := by
  change MulAut.conj (s * (a s)⁻¹) ∈ H
  have he : MulAut.conj (s * (a s)⁻¹) =
      (MulAut.conj s * a * (MulAut.conj s)⁻¹) * a⁻¹ := by
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
  rw [he]
  exact H.mul_mem hs (H.inv_mem ha)

private theorem range_le_of_displacement {G : Type*} [Group G]
    (f : hermitianUnipotentCoord J →* G) (a : MulAut G) (t : G) (k : Eˣ)
    (hentry : ∀ z, a (f z) = f (coordConj J z))
    (htorus : ∀ z, t * f z * t⁻¹ = f (hermitianTorusAction J k z))
    {z : hermitianUnipotentCoord J}
    (hgen : ∀ H : Subgroup (hermitianUnipotentCoord J),
      displacement J z ∈ H → hermitianTorusAction J k (displacement J z) ∈ H → H = ⊤)
    (H : Subgroup (MulAut G)) (ha : a ∈ H) (ht : MulAut.conj t ∈ H)
    (hz : MulAut.conj (f z) * a * (MulAut.conj (f z))⁻¹ ∈ H) :
    f.range ≤ H.comap (MulAut.conj : G →* MulAut G) := by
  let K := H.comap (MulAut.conj : G →* MulAut G)
  have hd : f (displacement J z) ∈ K := by
    simpa only [displacement, map_mul, map_inv, hentry] using
      displacement_mem a H ha (f z) hz
  have htd : f (hermitianTorusAction J k (displacement J z)) ∈ K := by
    rw [← htorus]
    exact K.mul_mem (K.mul_mem ht hd) (K.inv_mem ht)
  have htop := hgen (K.comap f) hd htd
  rintro _ ⟨v, rfl⟩
  exact (show v ∈ K.comap f from htop ▸ mem_top v)

/-- Four inner conjugates of entrywise conjugation contain every inner
automorphism of the projective special unitary group, for every prime p > 5.
The conjugators belong to the actual projective special unitary group. -/
theorem entrywise_four_cover [Finite E]
    [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hcard : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p) :
    MulAut.HasInnerConjugateCover (entrywiseProjectiveAut J hJ) 4 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype E := Fintype.ofFinite E
  let : CharP E p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have h2 : (2 : E) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime E Nat.prime_two (by omega : p ≠ 2)
  have hfixed : Nat.card {x : E // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hc)
  obtain ⟨k, l, hk, hk3, hl⟩ := exists_torus_parameter J hp5 hcard hc
  obtain ⟨z, hz⟩ := exists_displacement_generator J hJ hp h2 hcard hfixed k hk hk3
  let a := entrywiseProjectiveAut J hJ
  let t := hermitianTorusPSU J hJ k
  let s : Fin 4 → ProjectiveSpecialUnitaryMatrixGroup J :=
    ![1, hermitianTorusPSU J hJ l, root J hJ z, oppositeRoot J hJ z]
  let H := closure (Set.range fun i => MulAut.conj (s i) * a * (MulAut.conj (s i))⁻¹)
  have hs (i : Fin 4) : MulAut.conj (s i) * a * (MulAut.conj (s i))⁻¹ ∈ H :=
    subset_closure ⟨i, rfl⟩
  have ha : a ∈ H := by simpa [s] using hs 0
  have ht : MulAut.conj t ∈ H := by
    have hh := displacement_mem a H ha (hermitianTorusPSU J hJ l)
      (by simpa [s] using hs 1)
    have he : hermitianTorusPSU J hJ l *
        (a (hermitianTorusPSU J hJ l))⁻¹ = t := by
      dsimp only [a, t]
      rw [entrywise_torus, ← map_inv, ← map_mul, hl]
    rwa [he] at hh
  let K := H.comap (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →*
    MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
  have hU : rootGroup J hJ ≤ K :=
    range_le_of_displacement J (root J hJ) a t k
      (entrywise_root J hJ)
      (fun v => by
        change hermitianTorusPSU J hJ k * root J hJ v * _ = _
        rw [hermitianTorusPSU_mul_unipotent, mul_inv_cancel_right])
      hz H ha ht (by simpa [s] using hs 2)
  have hV : oppositeRootGroup J hJ ≤ K :=
    range_le_of_displacement J (oppositeRoot J hJ) a t k
      (entrywise_opposite J hJ) (torus_opposite J hJ k hk)
      hz H ha ht (by simpa [s] using hs 3)
  have htop : K = ⊤ := by
    apply top_unique
    rw [← rootGroup_sup_oppositeRootGroup J hJ hp.one_lt hcard hfixed]
    exact sup_le hU hV
  refine ⟨s, ?_⟩
  rintro _ ⟨g, rfl⟩
  exact (show g ∈ K from htop ▸ mem_top g)

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Outer
