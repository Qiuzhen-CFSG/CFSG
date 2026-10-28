module

public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.TorusNormalizer
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.TorusRigidity.FiniteBorels
/-!
# At most two Borels through a rank-one maximal torus

Borels containing the same maximal torus are conjugate by its normalizer.
The actual dimension-one torus action is identity or inversion. An identity
actor lies in the torus centralizer, which is contained in the original
Borel. Two inversion actors differ by such a centralizer element. Consequently
all other Borels coincide, and the literal containing-Borel family has at
most two elements.

This proves the upper bound used in Borel §§13.11(1),13.13, from intrinsic
algebraic-group geometry. It does not assume a root system or a PGL₂ model.
-/

public section
namespace Theory.AlgebraicGroup.Bor1.RankOneGeometry
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
open Theory.AlgebraicGroup
open SemisimpleCenterContainment.RadicalGeometry.BorelRestriction

omit [IsAlgClosed k] in
private theorem inverse_conjugators_difference_centralizes
    (T : ClosedSubgroup G) (n m : Variety.Point G)
    (hn : ∀ x ∈ T.toSubgroup, n*x*n⁻¹=x⁻¹)
    (hm : ∀ x ∈ T.toSubgroup, m*x*m⁻¹=x⁻¹) :
    n⁻¹*m ∈ T.centralizer.toSubgroup := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  have hh : n⁻¹*x⁻¹*n=x := by
    rw [←hn x hx]
    group
  have he : (n⁻¹*m)*x*(n⁻¹*m)⁻¹=x := by
    calc
      (n⁻¹*m)*x*(n⁻¹*m)⁻¹ = n⁻¹*(m*x*m⁻¹)*n := by group
      _ = x := by rw [hm x hx,hh]
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Any two torus-containing Borels different from a specified Borel coincide
when the actual maximal torus has dimension one. -/
theorem rank_one_other_borel_unique
    (hG : Variety.IsConnected G) (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdim : Variety.dimension T.carrierVariety=1)
    (B C D : ClosedSubgroup G) (hB : IsBorelSubgroup B) (hC : IsBorelSubgroup C)
    (hD : IsBorelSubgroup D) (hTB : T≤B) (hTC : T≤C) (hTD : T≤D)
    (hCB : C≠B) (hDB : D≠B) : C=D := by
  have hCTB : T.centralizer ≤ B := centralizer_le_borel_of_solvable hG hT.1 hB hTB
    (SemisimpleCenterContainment.CartanGeometry.maximalTorus_centralizer_connected_solvable hG hT).2
  have hconj (E : ClosedSubgroup G) (hE : IsBorelSubgroup E) (hTE : T≤E) (hEB : E≠B) :
      ∃ n : Variety.Point G, E=B.conjugate n ∧ ∀ x∈T.toSubgroup,n*x*n⁻¹=x⁻¹ := by
    obtain ⟨n,hn,he⟩ := BorelIntersectionGeometry.normalizer_conjugate_of_borel_conjugate
      hB hT hTB hTE (BorelGeometricConjugacy.conjugacy hB hE)
    rcases normalizer_dim_one_torus_identity_or_inverse T hT.1 hdim n hn with hc | hi
    · exfalso
      apply hEB
      rw [he]
      apply ClosedSubgroup.conjugate_eq_self_of_mem_normalizer
      apply Subgroup.le_normalizer
      apply hCTB
      apply Subgroup.mem_centralizer_iff.mpr
      intro x hx
      exact (mul_inv_eq_iff_eq_mul.mp (hc x hx)).symm
    · exact ⟨n,he,hi⟩
  obtain ⟨n,hCn,hn⟩ := hconj C hC hTC hCB
  obtain ⟨m,hDm,hm⟩ := hconj D hD hTD hDB
  have hc : n⁻¹*m ∈ B.toSubgroup := hCTB (inverse_conjugators_difference_centralizes T n m hn hm)
  have hm' : m=n*(n⁻¹*m) := by group
  rw [hCn,hDm,hm',←ClosedSubgroup.conjugate_conjugate,
    ClosedSubgroup.conjugate_eq_self_of_mem_normalizer _ (Subgroup.le_normalizer hc)]

/-- The intrinsic rank-one torus lies in at most two Borels. -/
theorem rank_one_borels_card_le_two
    (hG : Variety.IsConnected G) (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdim : Variety.dimension T.carrierVariety=1) : Nat.card (BorelContainingIndex T)≤2 := by
  classical
  by_cases hex : Nonempty (BorelContainingIndex T)
  swap
  · let : IsEmpty (BorelContainingIndex T) := not_nonempty_iff.mp hex
    simp
  let B := Classical.choice hex
  let f : BorelContainingIndex T → Bool := fun C => decide (C.1=B.1)
  have hi : Function.Injective f := by
    intro C D he
    have he' : (C.1=B.1) ↔ (D.1=B.1) := by simpa [f] using congrArg (fun b => b=true) he
    apply Subtype.ext
    by_cases hc : C.1=B.1
    · exact hc.trans ((he'.mp hc).symm)
    · exact rank_one_other_borel_unique hG T hT hdim B.1 C.1 D.1 B.2.1 C.2.1 D.2.1
        B.2.2 C.2.2 D.2.2 hc (fun hd => hc (he'.mpr hd))
  simpa using Nat.card_le_card_of_injective f hi
end Theory.AlgebraicGroup.Bor1.RankOneGeometry
