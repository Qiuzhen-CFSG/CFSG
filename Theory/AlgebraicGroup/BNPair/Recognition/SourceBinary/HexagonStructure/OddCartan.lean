module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CartanPinning
public import Theory.GroupAction.PrimeOrderConjugation

/-!
# The actual odd Cartan actor separating unequal linear roots

Cartan irreducibility makes a nonidentity fixed point fill a whole linear
root. Prime-order orbit counting therefore forces a Cartan element to
centralize every smaller root when its prime does not divide q_small-1.
Cauchy's theorem in the literal H intersect R_large constructs such an
actor. Its own root action is fixed-point-free; the two source reflections
fix or invert it, giving fixed-point-free action on both outer middle roots.
All conjugates use the original quotient and right-conjugation words.

The arithmetic selection is supplied by BinaryPrimitiveDivisor.Separation,
including its explicit exponent-six calculation. This is the actual
Cartan input to middle-root isolation, not the derived
identity or an assumed irreducible radical module.

Source: Fong--Seitz I (4G), (6E), printed pp.23--24,44.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates GTwoSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] [CharP F 2]

include split in
private theorem cartan_le_element_centralizer {t : X ⧸ Q.D}
    (ht : t ∈ Q.tits.B ⊓ Q.tits.N) :
    Q.tits.B ⊓ Q.tits.N ≤ centralizer ({t} : Set (X ⧸ Q.D)) := by
  let := split.abelian
  intro h hh
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mul_comm (⟨h,hh⟩ : ↥(Q.tits.B ⊓ Q.tits.N)) ⟨t,ht⟩))

/-- A Cartan element has either no nonidentity fixed point on a linear
root or centralizes that whole literal root. -/
theorem linear_cartan_root_fixed_dichotomy (i : Fin 2)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (w : Weyl Q)
    {t : X ⧸ Q.D} (ht : t ∈ Q.tits.B ⊓ Q.tits.N) :
    rootAt Q split i w ⊓ centralizer ({t} : Set (X ⧸ Q.D)) = ⊥ ∨
      t ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) := by
  by_cases hz : rootAt Q split i w ⊓ centralizer ({t} : Set (X ⧸ Q.D)) = ⊥
  · exact Or.inl hz
  · right
    have hH := (le_inf (rootAt_torus_normalizes Q split i w)
      ((cartan_le_element_centralizer Q split ht).trans
        (centralizer ({t} : Set (X ⧸ Q.D))).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
    have he := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split i μ hK w
      (rootAt Q split i w ⊓ centralizer ({t} : Set (X ⧸ Q.D))) inf_le_left hz hH
    intro x hx
    exact mem_centralizer_singleton_iff.mp ((he.symm ▸ hx).2)

/-- The source prime separation forces pointwise centralization on every
Weyl conjugate of the smaller root. -/
theorem prime_cartan_centralizes_linear_roots (i : Fin 2)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F))
    {t : X ⧸ Q.D} (ht : t ∈ Q.tits.B ⊓ Q.tits.N)
    {r : ℕ} (hr : r.Prime) (ho : orderOf t = r)
    (hsep : ¬ r ∣ Nat.card F - 1) (w : Weyl Q) :
    t ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) := by
  obtain ⟨x,hx,hxne,hxt⟩ := Theory.GroupAction.exists_commuting_nonidentity_of_prime_order
    (rootAt Q split i w) hr ho (rootAt_torus_normalizes Q split i w ht)
    (by simpa only [rootAt, card_rightConjugate, simpleRoot_card Q split i hK μ] using hsep)
  rcases linear_cartan_root_fixed_dichotomy Q split i hK μ w ht with hz | hc
  · have he : x = 1 := mem_bot.mp (hz ▸ ⟨hx,mem_centralizer_singleton_iff.mpr hxt.symm.eq⟩)
    exact (hxne he).elim
  · exact hc

/-- A nonidentity element of the actual rank-one Cartan fixes no nonidentity
point of its own root. -/
theorem rankOne_cartan_root_fixedFree (i : Fin 2)
    (hK : simpleRemainder Q split i ≤ localKernel Q i)
    (μ : localGroup Q split i ≃* PSL(2,F)) (s : RootReflection Q split i)
    {t : X ⧸ Q.D} (htH : t ∈ Q.tits.B ⊓ Q.tits.N)
    (htR : t ∈ rankOne Q split i) (htne : t ≠ 1) :
    simpleRoot Q split i ⊓ centralizer ({t} : Set (X ⧸ Q.D)) = ⊥ := by
  rcases linear_cartan_root_fixed_dichotomy Q split i hK μ 1 htH with hz | hc
  · simpa only [rootAt_one] using hz
  · rw [rootAt_one] at hc
    obtain ⟨a,rfl⟩ := exists_alignedTorus_of_mem Q split i hK μ s htH htR
    have hx : alignedSimpleParameter Q split i hK μ s (.ofAdd 1) ∈ simpleRoot Q split i := by
      rw [← alignedSimpleParameter_range Q split i hK μ s]
      exact ⟨_,rfl⟩
    have he := alignedTorus_root Q split i hK μ s a 1
    rw [← mem_centralizer_iff.mp hc _ hx, mul_assoc, mul_inv_cancel, mul_one] at he
    have haa : (a : F)^2 = 1 := by
      have hh := Multiplicative.ofAdd.injective
        (alignedSimpleParameter_injective Q split i hK μ s he)
      simpa only [mul_one] using hh.symm
    have ha : a = 1 := Units.ext (CharTwo.sq_injective (haa.trans (one_pow 2).symm))
    apply (htne _).elim
    change alignedTorusHom Q split i hK μ s a = 1
    rw [ha,map_one]

private theorem fixedFree_rightConjugate {Y : Type*} [Group Y]
    (A : Subgroup Y) {t n : Y}
    (hfree : A ⊓ centralizer ({t} : Set Y) = ⊥)
    (hn : n*t*n⁻¹ = t ∨ n*t*n⁻¹ = t⁻¹) :
    rightConjugate A n ⊓ centralizer ({t} : Set Y) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have hc : Commute (n*t*n⁻¹) (n*x*n⁻¹) :=
    (show Commute t x from (mem_centralizer_singleton_iff.mp hx.2).symm).map
      (MulAut.conj n).toMonoidHom
  have htc : Commute t (n*x*n⁻¹) := by
    rcases hn with he | he
    · rwa [he] at hc
    · rw [he] at hc
      simpa only [inv_inv] using hc.inv_left
  have hy : n*x*n⁻¹ = 1 := mem_bot.mp
    (hfree ▸ ⟨hx.1,mem_centralizer_singleton_iff.mpr htc.symm.eq⟩)
  apply (MulAut.conj n).injective
  exact hy.trans (map_one _).symm

/-- Construct the actual separating actor, including its two nontrivial
middle-root actions and its pointwise action on every smaller root. -/
theorem exists_prime_cartan_separation
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (i j : Fin 2)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μi : localGroup Q split i ≃* PSL(2,E))
    (μj : localGroup Q split j ≃* PSL(2,F))
    (si : RootReflection Q split i) (sj : RootReflection Q split j)
    {r : ℕ} (hr : r.Prime) (hrj : r ∣ Nat.card F - 1)
    (hri : ¬ r ∣ Nat.card E - 1) :
    ∃ t : X ⧸ Q.D, t ∈ (Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split j ∧
      orderOf t = r ∧
      (∀ w, t ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D))) ∧
      Commute t (si.val : X ⧸ Q.D) ∧
      (sj.val : X ⧸ Q.D)*t*(sj.val : X ⧸ Q.D)⁻¹ = t⁻¹ ∧
      rootAt Q split j (Q.simple i) ⊓ centralizer ({t} : Set (X ⧸ Q.D)) = ⊥ ∧
      rootAt Q split j (Q.simple i*Q.simple j) ⊓ centralizer ({t} : Set (X ⧸ Q.D)) = ⊥ := by
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥((Q.tits.B ⊓ Q.tits.N) ⊓ rankOne Q split j)) r
    (by rwa [rankOne_cartan_card Q split j hKj μj sj])
  let t : X ⧸ Q.D := z
  have ht : orderOf t = r := by
    simpa only [t, Subgroup.orderOf_coe] using hz
  have htne : t ≠ 1 := by
    intro he
    rw [he,orderOf_one] at ht
    exact hr.ne_one ht.symm
  have hfix (w : Weyl Q) := prime_cartan_centralizes_linear_roots Q split i hKi μi
    z.property.1 hr ht hri w
  have hR : rankOne Q split i ≤ centralizer ({t} : Set (X ⧸ Q.D)) := by
    apply sup_le
    · intro u hu
      exact mem_centralizer_singleton_iff.mpr (by
        have hc := hfix 1
        rw [rootAt_one] at hc
        exact mem_centralizer_iff.mp hc u hu)
    · intro u hu
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hfix (Q.simple i)) u hu)
  have hsi : Commute t (si.val : X ⧸ Q.D) :=
    (mem_centralizer_singleton_iff.mp (hR si.mem_rankOne)).symm
  have hsj : (sj.val : X ⧸ Q.D)*t*(sj.val : X ⧸ Q.D)⁻¹ = t⁻¹ := by
    obtain ⟨a,ha⟩ := exists_alignedTorus_of_mem Q split j hKj μj sj z.property.1 z.property.2
    change alignedTorus Q split j hKj μj sj a = t at ha
    rw [← ha, reflection_alignedTorus]
    exact (alignedTorusHom Q split j hKj μj sj).map_inv a
  have hfree := rankOne_cartan_root_fixedFree Q split j hKj μj sj z.property.1 z.property.2 htne
  have hn : (si.val : X ⧸ Q.D)*t*(si.val : X ⧸ Q.D)⁻¹ = t :=
    mul_inv_eq_iff_eq_mul.mpr hsi.symm.eq
  have hnn : ((si.val*sj.val : Q.tits.N) : X ⧸ Q.D)*t*
      (((si.val*sj.val : Q.tits.N) : X ⧸ Q.D))⁻¹ = t⁻¹ := by
    change ((si.val : X ⧸ Q.D)*sj.val)*t*((si.val : X ⧸ Q.D)*sj.val)⁻¹ = t⁻¹
    calc
      _ = (si.val : X ⧸ Q.D)*((sj.val : X ⧸ Q.D)*t*(sj.val : X ⧸ Q.D)⁻¹)*(si.val : X ⧸ Q.D)⁻¹ := by group
      _ = t⁻¹ := by rw [hsj]; simpa only [mul_inv_rev,inv_inv,mul_assoc] using congrArg Inv.inv hn
  refine ⟨t,z.property,ht,hfix,hsi,hsj,?_,?_⟩
  · rw [rootAt_eq Q split j (Q.simple i) si.val si.class_eq]
    exact fixedFree_rightConjugate _ hfree (Or.inl hn)
  · rw [rootAt_eq Q split j (Q.simple i*Q.simple j) (si.val*sj.val)
      (by rw [map_mul,si.class_eq,sj.class_eq])]
    exact fixedFree_rightConjugate _ hfree (Or.inr hnn)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
