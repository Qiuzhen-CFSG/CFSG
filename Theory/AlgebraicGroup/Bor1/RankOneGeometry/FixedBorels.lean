module

public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.Borels
public import Theory.AlgebraicGroup.Borel.SelfNormalizer.Source
/-!
# Fixed points on a rank-one Borel orbit

An orbit point with Borel stabilizer gives its conjugate Borel. Self-normalization
makes this assignment injective. A torus-fixed orbit point yields a Borel
containing that torus, so the intrinsic rank-one two-Borel bound rules out three
distinct fixed orbit points. This is the homogeneous-space step of Borel §13.13.
-/

public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Theory.AlgebraicGroup
namespace Theory.AlgebraicGroup.Bor1.RankOneGeometry
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {X : Type v} [MulAction (Variety.Point G) X]

private theorem smul_eq_of_borel_conjugate_eq (hG : Variety.IsConnected G)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) (x : X)
    (hstab : ∀ a : Variety.Point G, a • x = x ↔ a ∈ B.toSubgroup)
    (g h : Variety.Point G) (he : B.conjugate g = B.conjugate h) : g • x = h • x := by
  let a := h⁻¹*g
  have ha : B.conjugate a = B := by
    dsimp only [a]
    rw [←ClosedSubgroup.conjugate_conjugate,he,
      ClosedSubgroup.conjugate_conjugate,inv_mul_cancel,ClosedSubgroup.conjugate_one]
  have hn : a ∈ B.normalizer.toSubgroup := by
    apply Subgroup.mem_normalizer_iff.mpr
    intro z
    have hz := B.mem_conjugate_iff a (a*z*a⁻¹)
    rw [ha] at hz
    change (a*z*a⁻¹ ∈ B.toSubgroup ↔ a⁻¹*(a*z*a⁻¹)*a ∈ B.toSubgroup) at hz
    simpa only [inv_mul_cancel_left,mul_assoc,inv_mul_cancel,mul_one] using hz.symm
  rw [BorelSelfNormalizer.normalizer_eq hG B hB] at hn
  have hx := (hstab a).mpr hn
  have hh := congrArg (fun y : X => h • y) hx
  simpa only [a,smul_smul,mul_inv_cancel_left] using hh

theorem rank_one_orbit_fixedPoints_no_three (hG : Variety.IsConnected G)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdim : Variety.dimension T.carrierVariety=1)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) (x : X)
    (hstab : ∀ a : Variety.Point G, a • x = x ↔ a ∈ B.toSubgroup)
    (g h j : Variety.Point G)
    (hg : ∀ t∈T.toSubgroup,t • (g • x) = g • x)
    (hh : ∀ t∈T.toSubgroup,t • (h • x) = h • x)
    (hj : ∀ t∈T.toSubgroup,t • (j • x) = j • x) :
    g • x = h • x ∨ g • x = j • x ∨ h • x = j • x := by
  classical
  have hTC (a : Variety.Point G) (ha : ∀ t∈T.toSubgroup,t • (a • x) = a • x) :
      T ≤ B.conjugate a := by
    intro t ht
    apply (B.mem_conjugate_iff a t).mpr
    apply (hstab _).mp
    simp only [mul_smul,ha t ht,inv_smul_smul]
  by_cases hgh : B.conjugate g = B.conjugate h
  · exact Or.inl (smul_eq_of_borel_conjugate_eq hG B hB x hstab g h hgh)
  by_cases hgj : B.conjugate g = B.conjugate j
  · exact Or.inr (Or.inl (smul_eq_of_borel_conjugate_eq hG B hB x hstab g j hgj))
  have he := rank_one_other_borel_unique hG T hT hdim
    (B.conjugate g) (B.conjugate h) (B.conjugate j)
    (hB.conjugate g) (hB.conjugate h) (hB.conjugate j)
    (hTC g hg) (hTC h hh) (hTC j hj) (Ne.symm hgh) (Ne.symm hgj)
  exact Or.inr (Or.inr (smul_eq_of_borel_conjugate_eq hG B hB x hstab h j he))
end Theory.AlgebraicGroup.Bor1.RankOneGeometry
