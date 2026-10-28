module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.ScalarFour
public import Theory.SpecificGroups.G2.ConwayRootFour.MarkedLift
public import Theory.AtlasPort.Janko2.Algebra.IcosianDivision
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A dimension bound for the literal scalar fixed space

Every nontrivial involution in the actual scalar A₅ has a lift whose square is
central negation. Indeed, an icosian scalar squaring to one is ±1 in the golden
quaternion division ring, so its projective image would be trivial.

For a lattice automorphism g with g² = −1, reduction modulo two satisfies
im(g − 1) = ker(g − 1). To prove the reverse inclusion, lift a fixed class x,
write gx − x = 2y, and cancel doubling to get gy + y = −x. Rank-nullity then
gives dimension twelve. Applying this to any nonidentity element of the
published scalar U proves dim C_(Λ/2Λ)(U) ≤ 12.

This supplies the upper dimension bound used in Aschbacher, *Sporadic Groups*
(1994), Lemma 49.5, p.283. It does not identify a Conway conjugacy class or
assert that the entire U-fixed space already has dimension twelve.
All icosian and Leech models used here are the existing attributed ATLAS ports.
-/
open Atlas.Conway Atlas.Lattices Atlas.Codes Atlas.Algebra
open Atlas.G2.ConwayRootFour
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
@[expose] public noncomputable section

def difference (g : LeechCentralQuotient) : LeechModTwo →ₗ[Bit] LeechModTwo :=
  (quotientModTwoRepresentation g).toLinearMap - LinearMap.id

private theorem neg_mod_two (v : LeechModTwo) : -v = v := by
  obtain ⟨x,rfl⟩ := leechReduction_surjective v
  apply neg_eq_iff_add_eq_zero.mpr
  rw [← map_add]
  exact (leechReduction_eq_zero _).mpr ⟨x, by simp [two_nsmul]⟩

private theorem sub_mod_two (v w : LeechModTwo) : v - w = v + w := by
  rw [sub_eq_add_neg, neg_mod_two]

private theorem twice_mod_two (v : LeechModTwo) : v + v = 0 := by
  calc
    v + v = -v + v := congrArg (fun w => w + v) (neg_mod_two v).symm
    _ = 0 := neg_add_cancel v

private theorem lift_apply_sq (g : LeechIsometryGroup) (h : g ^ 2 = negationIsometry)
    (x : leech) : g.val (g.val x) = -x := by
  have he := congrArg (fun k : LeechIsometryGroup => k.val x) h
  exact he

theorem difference_range_eq_ker (g : LeechIsometryGroup)
    (h : g ^ 2 = negationIsometry) :
    LinearMap.range (difference (leechCentralProjection g)) =
      LinearMap.ker (difference (leechCentralProjection g)) := by
  let T := quotientModTwoRepresentation (leechCentralProjection g)
  have hs (v : LeechModTwo) : T (T v) = v := by
    have he : (leechCentralProjection g)^2 = 1 := by
      rw [← map_pow, h, projection_negation]
    have hh := congrArg (fun k : LeechCentralQuotient => quotientModTwoRepresentation k v) he
    simpa only [pow_two, map_mul, map_one, LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq, T] using hh
  apply le_antisymm
  · rintro _ ⟨v,rfl⟩
    rw [LinearMap.mem_ker]
    change T (T v - v) - (T v - v) = 0
    rw [map_sub, hs, sub_mod_two, sub_mod_two, sub_mod_two]
    calc
      v + T v + (T v + v) = (v + v) + (T v + T v) := by abel
      _ = 0 := by rw [twice_mod_two, twice_mod_two, add_zero]
  · intro v hv
    obtain ⟨x,rfl⟩ := leechReduction_surjective v
    have hz : leechReduction (g.val x - x) = 0 := by
      rw [map_sub]
      exact hv
    obtain ⟨y,hy⟩ := (leechReduction_eq_zero _).mp hz
    have hgy := congrArg g.val hy
    rw [map_nsmul, map_sub, lift_apply_sq g h] at hgy
    have he : g.val y + y = -x := by
      simp only [two_nsmul] at hy hgy
      apply Subtype.ext
      funext i
      have ha := congrArg (fun z : leech => z.val i) hy
      have hb := congrArg (fun z : leech => z.val i) hgy
      change y.val i + y.val i = (g.val x).val i - x.val i at ha
      change (g.val y).val i + (g.val y).val i = -x.val i - (g.val x).val i at hb
      change (g.val y).val i + y.val i = -x.val i
      omega
    refine ⟨leechReduction y, ?_⟩
    have hh := congrArg leechReduction he
    rw [map_add, map_neg, neg_mod_two] at hh
    change T (leechReduction y) - leechReduction y = leechReduction x
    rw [sub_mod_two]
    exact hh

theorem difference_ker_finrank (g : LeechIsometryGroup)
    (h : g ^ 2 = negationIsometry) :
    Module.finrank Bit (LinearMap.ker (difference (leechCentralProjection g))) = 12 := by
  have hr := (difference (leechCentralProjection g)).finrank_range_add_finrank_ker
  rw [difference_range_eq_ker g h, leechModTwo_finrank] at hr
  omega


private theorem scalar_sq_one (u : icosianNormOneGroup) (h : u ^ 2 = 1) :
    u = 1 ∨ u = icosianNormOneMinusOne := by
  have hs : u.val.val ^ 2 = 1 := congrArg (fun x : icosianNormOneGroup => x.val.val) h
  rcases sq_eq_one_iff.mp hs with hs | hs
  · exact Or.inl (icosianNormOne_value_injective hs)
  · exact Or.inr (icosianNormOne_value_injective hs)

theorem scalarFive_involution_lift (s : alternatingGroup (Fin 5))
    (hs : s ^ 2 = 1) (hne : s ≠ 1) :
    ∃ g : LeechIsometryGroup, leechCentralProjection g = scalarFive s ∧
      g ^ 2 = negationIsometry := by
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective icosianNormOneReduction.ker
    (icosianScalarProjectiveAlternating.symm s)
  have he : leechCentralProjection (icosianScalarsToCo0 u) = scalarFive s := by
    change icosianScalarProjectiveToCo1 (QuotientGroup.mk' _ u) = _
    rw [hu]
    rfl
  refine ⟨icosianScalarsToCo0 u, he, ?_⟩
  have hp : leechCentralProjection ((icosianScalarsToCo0 u)^2) = 1 := by
    rw [map_pow, he, ← map_pow, hs, map_one]
  have hk := MonoidHom.mem_ker.mpr hp
  rw [leechCentralProjection_kernel, leechCentralSigns_mem] at hk
  rcases hk with h | h
  · have hu2 : u^2 = 1 := icosianScalarsToCo0_injective (by rw [map_pow, h, map_one])
    have hz : leechCentralProjection (icosianScalarsToCo0 u) = 1 := by
      rcases scalar_sq_one u hu2 with rfl | rfl
      · rw [map_one, map_one]
      · rw [icosianScalarsToCo0_minusOne, projection_negation]
    exact False.elim (hne (scalarFive_injective (by rw [← he, hz, map_one])))
  · exact h

theorem U_involution_lift (u : U) (hne : u.val ≠ 1) :
    ∃ g : LeechIsometryGroup, leechCentralProjection g = u.val ∧
      g^2 = negationIsometry := by
  obtain ⟨a,ha⟩ := U_le_I u.property
  let s := alternatingGroup.ofSubtype fourPoints a
  have he : scalarFive s = u.val := ha
  have hs : s ^ 2 = 1 := scalarFive_injective (by
    rw [map_pow, he, map_one, pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self u))
  have hn : s ≠ 1 := by
    intro h
    apply hne
    rw [← he, h, map_one]
  obtain ⟨g,hg,hg2⟩ := scalarFive_involution_lift s hs hn
  exact ⟨g,hg.trans he,hg2⟩


theorem U_involution_fixed_finrank (u : U) (hne : u.val ≠ 1) :
    Module.finrank Bit (LinearMap.ker (difference u.val)) = 12 := by
  obtain ⟨g,hg,hg2⟩ := U_involution_lift u hne
  rw [← hg]
  exact difference_ker_finrank g hg2

theorem fixedSpace_finrank_le_twelve : Module.finrank Bit fixedSpace ≤ 12 := by
  have hn : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by rw [U_card]; decide)
  obtain ⟨u,hu⟩ := exists_ne (1 : U)
  have hu' : u.val ≠ 1 := fun h => hu (Subtype.ext h)
  have hle : fixedSpace ≤ LinearMap.ker (difference u.val) := by
    intro v hv
    rw [LinearMap.mem_ker]
    change quotientModTwoRepresentation u.val v - v = 0
    rw [hv u.val u.property, sub_self]
  exact (Submodule.finrank_mono hle).trans_eq (U_involution_fixed_finrank u hu')

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
