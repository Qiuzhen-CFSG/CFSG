module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.LocalSplitting
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary.RankOne

/-!
# Lifting the ternary orthogonal local group through a double kernel

SL₂(3) is binary tetrahedral, so its homomorphisms lift uniquely through
central two-group kernels. Uniqueness makes the two lifted rank-one factors
commute and supplies the conjugation action of the involutory complement.
Ambient involution fusion supplies a square-one lift of that complement.
A second fusion identity kills the diagonal scalar defect, so the lift
descends to the actual local image.

Unlike the argument for primes greater than three, this uses no perfectness
of SL₂(3). Commutation is proved only for two-primary kernels; no splitting
of the genuine cubic cover is asserted. The actual octonion map and fusion
are supplied in `InvolutionLift.Geometry`.

Source: the two-primary calculation for Aschbacher–Smith I.1.4(2), printed
p.408 (PDF p.419), GLS3 §6.1; the binary tetrahedral relations are the
ABG II.3 Proposition 2 calculation reused by the ternary Sp₄ development.
-/

public section

namespace Atlas.G2.FiniteCover.MultiplierThree.InvolutionLift
open PerfectCentralCovering Subgroup
open MultiplierOrdinary.OddTwoPrimary
open GLS3.Chapter5.SchurPresentation

private theorem rankOne_lift_unique {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker)
    (s t : RankOne 3 →* E) (hst : f.comp s = f.comp t) : s = t := by
  have he :=
    Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary.binary_lift_unique
      f hc hk (s.comp binaryTetrahedralEquivSL.toMonoidHom)
      (t.comp binaryTetrahedralEquivSL.toMonoidHom)
      (by rw [← MonoidHom.comp_assoc, ← MonoidHom.comp_assoc, hst])
  apply MonoidHom.ext
  intro x
  obtain ⟨a,rfl⟩ := binaryTetrahedralEquivSL.surjective x
  exact DFunLike.congr_fun he a

private theorem exists_rankOne_lift {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker) (j : RankOne 3 →* G) :
    ∃ s : RankOne 3 →* E, f.comp s = j := by
  obtain ⟨s,hs⟩ :=
    Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.TernarySection.TwoPrimary.exists_binary_lift
      f hf hc hk (j.comp binaryTetrahedralEquivSL.toMonoidHom)
  refine ⟨s.comp binaryTetrahedralEquivSL.symm.toMonoidHom, ?_⟩
  ext x
  have h := DFunLike.congr_fun hs (binaryTetrahedralEquivSL.symm x)
  simpa using h

private theorem product_lift_unique {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker)
    (s t : RankOne 3 × RankOne 3 →* E) (hst : f.comp s = f.comp t) : s = t := by
  have hl := rankOne_lift_unique f hc hk (s.comp (MonoidHom.inl _ _))
    (t.comp (MonoidHom.inl _ _))
    (by rw [← MonoidHom.comp_assoc, ← MonoidHom.comp_assoc, hst])
  have hr := rankOne_lift_unique f hc hk (s.comp (MonoidHom.inr _ _))
    (t.comp (MonoidHom.inr _ _))
    (by rw [← MonoidHom.comp_assoc, ← MonoidHom.comp_assoc, hst])
  ext x
  calc
    s x = s (x.1,1) * s (1,x.2) := by rw [← map_mul]; simp
    _ = t (x.1,1) * t (1,x.2) := by
      rw [show s (x.1,1) = t (x.1,1) from DFunLike.congr_fun hl x.1,
        show s (1,x.2) = t (1,x.2) from DFunLike.congr_fun hr x.2]
    _ = t x := by rw [← map_mul]; simp

private theorem exists_product_lift {E G : Type*} [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker)
    (j : RankOne 3 × RankOne 3 →* G) :
    ∃ s : RankOne 3 × RankOne 3 →* E, f.comp s = j := by
  obtain ⟨s,hs⟩ := exists_rankOne_lift f hf hc hk (j.comp (MonoidHom.inl _ _))
  obtain ⟨t,ht⟩ := exists_rankOne_lift f hf hc hk (j.comp (MonoidHom.inr _ _))
  have hs' (x) : f (s x) = j (x,1) := DFunLike.congr_fun hs x
  have ht' (x) : f (t x) = j (1,x) := DFunLike.congr_fun ht x
  have hcomm (x y) : Commute (s x) (t y) := by
    have he : (MulAut.conj (t y)).toMonoidHom.comp s = s := by
      apply rankOne_lift_unique f hc hk
      ext z
      change f (t y * s z * (t y)⁻¹) = f (s z)
      rw [map_mul, map_mul, map_inv, hs', ht']
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      ext <;> simp
    have hh := DFunLike.congr_fun he x
    change t y * s x * (t y)⁻¹ = s x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  refine ⟨s.noncommCoprod t hcomm, ?_⟩
  ext z
  change f (s z.1 * t z.2) = j z
  rw [map_mul, hs', ht']
  simpa using (map_mul j (z.1,1) (1,z.2)).symm

private theorem exists_semidirect_lift {G E : Type*} [Group G] [Group E]
    (m : LocalModel 3 G)
    (f : E →* G) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : IsPGroup 2 f.ker)
    (houter : IsConj (m.inclusion m.scalar) (m.inclusion m.outer)) :
    ∃ t : m.Domain →* E, f.comp t = m.inclusion := by
  obtain ⟨s,hs⟩ := exists_product_lift f hf hc hk
    (m.inclusion.comp SemidirectProduct.inl)
  have hs' (x) : f (s x) = m.inclusion (SemidirectProduct.inl x) :=
    DFunLike.congr_fun hs x
  obtain ⟨g,hg⟩ := isConj_iff.mp houter
  obtain ⟨a,ha⟩ := hf g
  let y := a * s (-1,1) * a⁻¹
  have hy : y ^ 2 = 1 := by
    have hn : ((-1,1) : RankOne 3 × RankOne 3) ^ 2 = 1 := by ext <;> simp
    dsimp only [y]
    rw [conj_pow, ← map_pow, hn, map_one, mul_one, mul_inv_cancel]
  let c : C2 →* E := QuaternionGroup.cyclicPowerHom 2 y hy
  have hc1 : c (.ofAdd 1) = y := QuaternionGroup.cyclicPowerHom_one 2 y hy
  have hcy : f y = m.inclusion m.outer := by
    dsimp only [y]
    rw [map_mul, map_mul, map_inv, ha, hs']
    exact hg
  have hcf (b : C2) : f (c b) = m.inclusion (SemidirectProduct.inr b) := by
    have hb : b = 1 ∨ b = .ofAdd 1 :=
      (by decide : ∀ b : C2, b = 1 ∨ b = .ofAdd 1) b
    rcases hb with rfl | rfl
    · simp
    · rw [hc1, hcy]
      rfl
  have hcompat (b : C2) : s.comp (m.action b).toMonoidHom =
      (MulAut.conj (c b)).toMonoidHom.comp s := by
    apply product_lift_unique f hc hk
    ext x
    change f (s (m.action b x)) = f (c b * s x * (c b)⁻¹)
    rw [map_mul, map_mul, map_inv, hs', hs', hcf]
    rw [← map_inv, ← map_mul, ← map_mul, SemidirectProduct.inl_aut, map_inv]
  refine ⟨SemidirectProduct.lift s c hcompat, ?_⟩
  apply SemidirectProduct.hom_ext
  · simpa only [MonoidHom.comp_assoc, SemidirectProduct.lift_comp_inl] using hs
  · simpa only [MonoidHom.comp_assoc, SemidirectProduct.lift_comp_inr] using
      (show f.comp c = m.inclusion.comp SemidirectProduct.inr from MonoidHom.ext hcf)

/-- The marked ternary orthogonal local image splits in every central double
extension when its two displayed involutions fuse to the scalar involution. -/
theorem exists_section_of_double_kernel {G E : Type*} [Group G] [Group E]
    (m : LocalModel 3 G)
    (houter : IsConj (m.inclusion m.scalar) (m.inclusion m.outer))
    (hpair : IsConj (m.inclusion m.scalar) (m.inclusion m.paired))
    (f : E →* G) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2) :
    ∃ s : m.inclusion.range →* E, f.comp s = m.inclusion.range.subtype := by
  obtain ⟨t,ht⟩ := exists_semidirect_lift m f hf hc
    (IsPGroup.of_card (n := 1) (by simpa using hk)) houter
  have hd := m.diagonal_lift_eq_one f hf hc hk t ht hpair
  have hker : m.inclusion.ker ≤ t.ker := by
    intro x hx
    rcases (m.kernel x).mp hx with rfl | rfl
    · exact map_one t
    · exact hd
  let q := QuotientGroup.lift m.inclusion.ker t hker
  let e := QuotientGroup.quotientKerEquivRange m.inclusion
  refine ⟨q.comp e.symm.toMonoidHom, ?_⟩
  ext x
  obtain ⟨a,ha⟩ := x.property
  have hx : x = m.inclusion.rangeRestrict a := Subtype.ext ha.symm
  rw [hx]
  have he : e.symm (m.inclusion.rangeRestrict a) =
      QuotientGroup.mk' m.inclusion.ker a := e.symm_apply_eq.mpr rfl
  change f (q (e.symm (m.inclusion.rangeRestrict a))) = m.inclusion a
  rw [he]
  exact DFunLike.congr_fun ht a

end Atlas.G2.FiniteCover.MultiplierThree.InvolutionLift
