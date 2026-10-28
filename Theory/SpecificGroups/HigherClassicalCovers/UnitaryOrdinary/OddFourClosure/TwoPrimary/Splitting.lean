module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.BlockModel
public import Theory.GroupTheory.PerfectCentralInvolutionExtension
public import Theory.GroupTheory.PerfectCentralCoverSquareObstruction
public import Theory.GroupTheory.DihedralPresentation
public import Theory.SpecificGroups.SL2.CentralTwoExtensions

/-!
# Lifting the unitary block-pair subgroup through a double cover

Split the two SL₂ factors and the transverse SL₂ by the central two-group
extension theorem. Perfectness makes the first two lifts commute. Fusion
to a lifted plane sign makes every lift of either dihedral reflection
square to one, because the central kernel has exponent two. The transverse
lift supplies the rotation with its original exponent. A dihedral
presentation bound then gives a section of the complement; uniqueness of
lifts on the perfect base supplies all semidirect-product relations.

The actual matrix embedding and its odd index are separate inputs to the
consumer in `OddFourClosure.TwoPrimary`. No splitting statement is a
field of the geometric model. Source: the local calculation supporting
Aschbacher--Smith I.1.4(3), printed p.408, and GLS3 §6.1.
-/

open Subgroup PerfectCentralCovering BenderSuzuki.MatrixGroups

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary

private theorem dihedral_lift {E G : Type*} [Group E] [Group G]
    {n : ℕ} [NeZero n] (f : E →* G) (j : DihedralGroup n →* G)
    (hj : Function.Injective j) (a b : E)
    (ha : a ^ n = 1) (hb : b ^ 2 = 1) (hba : (b * a) ^ 2 = 1)
    (hfa : f a = j (.r 1)) (hfb : f b = j (.sr 0)) :
    ∃ s : DihedralGroup n →* E, f.comp s = j := by
  let H : Subgroup E := closure ({b, b * a} : Set E)
  have hbb : b * b = 1 := by simpa only [pow_two] using hb
  have hbba : (b * a) * b = a⁻¹ := by
    apply mul_right_cancel (b := a)
    simpa only [pow_two, mul_assoc, inv_mul_cancel] using hba
  obtain ⟨hfin, hcard⟩ := closure_pair_finite_card_le_of_involutions
    (NeZero.pos n) b (b * a) hb hba (by rw [hbba, inv_pow, ha, inv_one])
  let : Finite H := hfin
  have hbH : b ∈ H := subset_closure (by simp)
  have haH : a ∈ H := by
    have hbaH : b * a ∈ H := subset_closure (by simp)
    simpa only [← mul_assoc, hbb, one_mul] using H.mul_mem hbH hbaH
  have hle : H ≤ j.range.comap f := by
    apply (closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨.sr 0, hfb.symm⟩
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨.sr 1, by rw [map_mul, hfb, hfa, ← map_mul]; simp⟩
  let e := MonoidHom.ofInjective hj
  let k : H →* DihedralGroup n := e.symm.toMonoidHom.comp
    ((f.comp H.subtype).codRestrict j.range fun x => hle x.property)
  have hk (x : H) : j (k x) = f x :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have hka : k ⟨a, haH⟩ = .r 1 := hj ((hk _).trans hfa)
  have hkb : k ⟨b, hbH⟩ = .sr 0 := hj ((hk _).trans hfb)
  have hks : Function.Surjective k := by
    rintro (i | i)
    · refine ⟨(⟨a, haH⟩ : H) ^ i.val, ?_⟩
      rw [map_pow, hka, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    · refine ⟨⟨b, hbH⟩ * (⟨a, haH⟩ : H) ^ i.val, ?_⟩
      rw [map_mul, map_pow, hkb, hka, DihedralGroup.r_one_pow,
        ZMod.natCast_zmod_val, DihedralGroup.sr_mul_r, zero_add]
  let eH : H ≃* DihedralGroup n := MulEquiv.ofBijective k
    (hks.bijective_of_nat_card_le (by simpa only [DihedralGroup.nat_card] using hcard))
  refine ⟨H.subtype.comp eH.symm.toMonoidHom, ?_⟩
  ext x
  change f (eH.symm x) = j x
  rw [← hk]
  exact congrArg j (eH.apply_symm_apply x)

private theorem fusion_square {E G N : Type*} [Group E] [Group G] [Group N]
    (f : E →* G) (hf : Function.Surjective f) (hc : f.ker ≤ center E)
    (h2 : ∀ k ∈ f.ker, k ^ 2 = 1) (s : N →* E) (n : N) (hn : n ^ 2 = 1)
    (x : E) (hconj : IsConj (f (s n)) (f x)) : x ^ 2 = 1 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  obtain ⟨a, rfl⟩ := hf g
  have he : f (a * s n * a⁻¹) = f x := by
    simpa only [map_mul, map_inv] using hg
  rw [← square_eq_of_map_eq_of_kernel_exponent_two f hc h2 he]
  simp [conj_pow, ← map_pow, hn]

private theorem semidirect_lift {N Q E G : Type*} [Group N] [Group.IsPerfect N]
    [Group Q] [Group E] [Group G]
    (f : E →* G) (hc : f.ker ≤ center E) (φ : Q →* MulAut N)
    (j : N ⋊[φ] Q →* G) (s : N →* E) (t : Q →* E)
    (hs : f.comp s = j.comp SemidirectProduct.inl)
    (ht : f.comp t = j.comp SemidirectProduct.inr) :
    ∃ r : N ⋊[φ] Q →* E, f.comp r = j := by
  have hs' (x : N) : f (s x) = j (SemidirectProduct.inl x) := DFunLike.congr_fun hs x
  have ht' (x : Q) : f (t x) = j (SemidirectProduct.inr x) := DFunLike.congr_fun ht x
  have hcompat (b : Q) :
      s.comp (φ b).toMonoidHom = (MulAut.conj (t b)).toMonoidHom.comp s := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq f hc
    ext x
    change f (s (φ b x)) = f (t b * s x * (t b)⁻¹)
    rw [map_mul, map_mul, map_inv, hs', hs', ht']
    rw [← map_inv, ← map_mul, ← map_mul, SemidirectProduct.inl_aut, map_inv]
  refine ⟨SemidirectProduct.lift s t hcompat, ?_⟩
  apply SemidirectProduct.hom_ext
  · simpa only [MonoidHom.comp_assoc, SemidirectProduct.lift_comp_inl] using hs
  · simpa only [MonoidHom.comp_assoc, SemidirectProduct.lift_comp_inr] using ht

private theorem rankOne_perfect {q : ℕ} [Fact q.Prime] (hq : 3 < q) :
    Group.IsPerfect (RankOne q) := by
  have h2 : (2 : ZMod q) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < q)
      ((ZMod.natCast_eq_zero_iff 2 q).mp h)
  have hsq : (2 : ZMod q) ^ 2 ≠ 1 := by
    intro h
    have h3 : (3 : ZMod q) = 0 := by linear_combination h
    exact Nat.not_dvd_of_pos_of_lt (by decide) hq
      ((ZMod.natCast_eq_zero_iff 3 q).mp h3)
  exact ⟨Matrix.SL2.commutator_eq_top h2 hsq⟩

/-- The marked block geometry constructs a section over its literal range
in every finite central extension with kernel of order two. All rank-one
splitting and compatibility premises are discharged here. -/
public theorem exists_section_on_block_model
    {F : Type*} [Field F] (J : HermitianForm 4 F)
    {q : ℕ} [Fact q.Prime] (hq : 3 < q) (m : BlockModel J q)
    {E : Type*} [Group E] [Finite E]
    (f : E →* J.specialSubgroup) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hcard : Nat.card f.ker = 2) :
    ∃ s : m.inclusion.range →* E, f.comp s = m.inclusion.range.subtype := by
  let : Group.IsPerfect (RankOne q) := rankOne_perfect hq
  let : Group.IsPerfect (RankOne q × RankOne q) := ⟨by
    change ⁅(⊤ : Subgroup (RankOne q × RankOne q)), ⊤⁆ = ⊤
    rw [← top_prod_top, commutator_prod_prod]
    change (commutator (RankOne q)).prod (commutator (RankOne q)) =
      (⊤ : Subgroup (RankOne q)).prod ⊤
    simp⟩
  have hp : IsPGroup 2 f.ker := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have h2 : ∀ k ∈ f.ker, k ^ 2 = 1 := by
    intro k hk
    have h := pow_card_eq_one' (x := (⟨k, hk⟩ : f.ker))
    rw [hcard] at h
    exact congrArg Subtype.val h
  have hsplit : ∀ (D : Type _) [Group D] [Finite D] (g : D →* RankOne q),
      Function.Surjective g → g.ker ≤ center D → IsPGroup 2 g.ker →
      ∃ s : RankOne q →* D, g.comp s = MonoidHom.id _ := by
    intro D _ _ g hg hgc hgp
    exact Matrix.SpecialLinearGroup.exists_section_of_central_two_kernel hq g hg hgc hgp
  let j := m.inclusion.comp SemidirectProduct.inl
  have hj : Function.Injective j := m.injective.comp SemidirectProduct.inl_injective
  let jl := j.comp (MonoidHom.inl (RankOne q) (RankOne q))
  let jr := j.comp (MonoidHom.inr (RankOne q) (RankOne q))
  obtain ⟨sl, hsl⟩ := exists_lift_of_splits_central_pGroup hsplit f hf hc hp jl
    (hj.comp fun _ _ h => congrArg Prod.fst h)
  obtain ⟨sr, hsr⟩ := exists_lift_of_splits_central_pGroup hsplit f hf hc hp jr
    (hj.comp fun _ _ h => congrArg Prod.snd h)
  obtain ⟨s, hs⟩ := exists_product_lift_of_factor_lifts f hc j sl sr hsl hsr
  obtain ⟨st, hst⟩ := exists_lift_of_splits_central_pGroup hsplit f hf hc hp
    m.transverse m.transverse_injective
  let a := st m.torus
  have ha : a ^ (q + 1) = 1 := by
    rw [← map_pow, m.torus_pow, map_one]
  have hfa : f a = m.inclusion (SemidirectProduct.inr (.r 1)) :=
    (DFunLike.congr_fun hst m.torus).trans m.rotation_eq
  obtain ⟨b, hfb⟩ := hf (m.inclusion (SemidirectProduct.inr (.sr 0)))
  have hn : ((-1, 1) : RankOne q × RankOne q) ^ 2 = 1 := by ext <;> simp
  have hsn : f (s (-1, 1)) = m.inclusion (SemidirectProduct.inl (-1, 1)) :=
    DFunLike.congr_fun hs (-1, 1)
  have hb : b ^ 2 = 1 := by
    apply fusion_square f hf hc h2 s (-1, 1) hn b
    rw [hsn, hfb]
    exact m.reflection_zero_conjugate
  have hba : (b * a) ^ 2 = 1 := by
    apply fusion_square f hf hc h2 s (-1, 1) hn (b * a)
    rw [hsn, map_mul, hfb, hfa, ← map_mul, ← map_mul,
      DihedralGroup.sr_mul_r, zero_add]
    exact m.reflection_one_conjugate
  obtain ⟨t, ht⟩ := dihedral_lift f (m.inclusion.comp SemidirectProduct.inr)
    (m.injective.comp SemidirectProduct.inr_injective) a b ha hb hba hfa hfb
  obtain ⟨r, hr⟩ := semidirect_lift f hc m.action m.inclusion s t hs ht
  let e := MonoidHom.ofInjective m.injective
  refine ⟨r.comp e.symm.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro x
  change f (r (e.symm x)) = x.val
  exact (DFunLike.congr_fun hr (e.symm x)).trans
    (congrArg Subtype.val (e.apply_symm_apply x))

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary


