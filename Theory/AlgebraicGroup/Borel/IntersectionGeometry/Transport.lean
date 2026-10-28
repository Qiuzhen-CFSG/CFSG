module

public import Theory.AlgebraicGroup.Borel.Existence
public import Theory.AlgebraicGroup.Tori.Maximal.theorem_1_4_3_b

/-!
Conjugation reductions for Borel intersections, following Borel, *Linear
Algebraic Groups*, §14.13, and GLS3, Theorem 1.11.4.

If a second Borel has the form `b n B n⁻¹ b⁻¹`, with `b ∈ B` and `n`
normalizing a maximal torus `T ≤ B`, then `b T b⁻¹` is a common maximal
torus. The intersection is conjugate to `B ∩ n B n⁻¹`, so connectedness
reduces to intersections of Borels containing a fixed torus. These are
algebraic reductions; the geometric existence of the normal form is separate.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry

variable {k : Type u} [Field k] {G : Variety k} [AlgebraicGroup G]

public theorem conjugate_le {H K : ClosedSubgroup G} (h : H ≤ K)
    (g : Variety.Point G) : H.conjugate g ≤ K.conjugate g := by
  intro x hx
  exact (K.mem_conjugate_iff g x).mpr (h ((H.mem_conjugate_iff g x).mp hx))

public theorem conjugate_inter (H K : ClosedSubgroup G) (g : Variety.Point G) :
    (H.inter K).conjugate g = (H.conjugate g).inter (K.conjugate g) := by
  apply SetLike.coe_injective
  ext x
  simp only [SetLike.mem_coe, ClosedSubgroup.mem_conjugate_iff,
    ClosedSubgroup.mem_inter_iff]
  rfl

public theorem conjugate_isSubtorus {T : ClosedSubgroup G}
    (hT : IsSubtorus T) (g : Variety.Point G) :
    IsSubtorus (T.conjugate g) := by
  obtain ⟨n, ⟨e⟩⟩ := hT
  exact ⟨n, ⟨(T.conjugateIso g).comp e⟩⟩

public theorem conjugate_isMaximalTorus {T : ClosedSubgroup G}
    (hT : IsMaximalTorus T) (g : Variety.Point G) :
    IsMaximalTorus (T.conjugate g) := by
  refine ⟨conjugate_isSubtorus hT.1 g, ?_⟩
  intro S hS hTS
  have hback := conjugate_le hTS g⁻¹
  rw [ClosedSubgroup.conjugate_conjugate, inv_mul_cancel,
    ClosedSubgroup.conjugate_one] at hback
  have heq := hT.2 _ (conjugate_isSubtorus hS g⁻¹) hback
  have hforward := congrArg (fun H : ClosedSubgroup G => H.conjugate g) heq
  simpa only [ClosedSubgroup.conjugate_conjugate, mul_inv_cancel,
    ClosedSubgroup.conjugate_one] using hforward

public theorem conjugate_isConnected {H : ClosedSubgroup G}
    (hH : _root_.IsConnected (H : Set (Variety.Point G)))
    (g : Variety.Point G) :
    _root_.IsConnected (H.conjugate g : Set (Variety.Point G)) := by
  have himage :
      (AlgebraicGroup.conjugationByMorphism G g).toFun '' (H : Set (Variety.Point G)) =
        (H.conjugate g : Set (Variety.Point G)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, H.mem_conjugate_iff,
        AlgebraicGroup.conjugationByMorphism_apply]
      convert hy using 1
      group
      rfl
    · intro hx
      refine ⟨g⁻¹ * x * g, (H.mem_conjugate_iff g x).mp hx, ?_⟩
      rw [AlgebraicGroup.conjugationByMorphism_apply]
      group
  rw [← himage]
  exact hH.image _ (AlgebraicGroup.conjugationByMorphism G g).continuous.continuousOn

/-- Existence of an initial Borel and ambient maximal torus requires no
conjugacy or root geometry. -/
public theorem exists_borel_maximalTorus_pair [IsAlgClosed k] :
    ∃ (B T : ClosedSubgroup G), IsBorelSubgroup B ∧ IsMaximalTorus T ∧ T ≤ B := by
  obtain ⟨T, hT⟩ := exists_maximalTorus G
  have hconn : _root_.IsConnected (T : Set (Variety.Point G)) := by
    let : ConnectedSpace (Variety.Point T.carrierVariety) :=
      connectedSpace_iff_univ.mpr hT.1.isConnected
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [← T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  have hcomm := hT.1.isMulCommutative
  rw [isMulCommutative_iff] at hcomm
  obtain ⟨B, hB, hTB⟩ := exists_borelSubgroup_containing_connected_solvable
    T hconn (Group.isSolvable_of_comm hcomm)
  exact ⟨B, T, hB, hT, hTB⟩

private theorem conjugate_eq_of_mem (B : ClosedSubgroup G)
    {b : Variety.Point G} (hb : b ∈ B.toSubgroup) : B.conjugate b = B :=
  ClosedSubgroup.conjugate_eq_self_of_mem_normalizer b
    (Subgroup.le_normalizer hb)

/-- The common torus furnished by a Bruhat representative is `b T b⁻¹`. -/
public theorem common_maximalTorus_of_normal_form
    (B T : ClosedSubgroup G) (hT : IsMaximalTorus T) (hTB : T ≤ B)
    (b n : Variety.Point G) (hb : b ∈ B.toSubgroup)
    (hn : n ∈ T.normalizer.toSubgroup) :
    IsMaximalTorus (T.conjugate b) ∧
      T.conjugate b ≤ B ∧ T.conjugate b ≤ B.conjugate (b * n) := by
  have hTn : T.conjugate n = T :=
    ClosedSubgroup.conjugate_eq_self_of_mem_normalizer n hn
  have hTnB : T ≤ B.conjugate n := by
    simpa only [hTn] using conjugate_le hTB n
  refine ⟨conjugate_isMaximalTorus hT b, ?_, ?_⟩
  · simpa only [conjugate_eq_of_mem B hb] using conjugate_le hTB b
  · simpa only [ClosedSubgroup.conjugate_conjugate] using conjugate_le hTnB b

/-- Remove the first Borel factor from an intersection in Bruhat position. -/
public theorem inter_normal_form (B : ClosedSubgroup G)
    (b n : Variety.Point G) (hb : b ∈ B.toSubgroup) :
    B.inter (B.conjugate (b * n)) = (B.inter (B.conjugate n)).conjugate b := by
  rw [conjugate_inter, conjugate_eq_of_mem B hb,
    ClosedSubgroup.conjugate_conjugate]

/-- Connectedness in Bruhat position reduces to the normalizer representative. -/
public theorem inter_connected_of_normal_form (B : ClosedSubgroup G)
    (b n : Variety.Point G) (hb : b ∈ B.toSubgroup)
    (hconn : _root_.IsConnected
      (B.inter (B.conjugate n) : Set (Variety.Point G))) :
    _root_.IsConnected (B.inter (B.conjugate (b * n)) : Set (Variety.Point G)) := by
  rw [inter_normal_form B b n hb]
  exact conjugate_isConnected hconn b

/-- The final right Borel factor in a double coset fixes the conjugated Borel. -/
public theorem conjugate_of_double_coset (B : ClosedSubgroup G)
    (b n c : Variety.Point G) (hc : c ∈ B.toSubgroup) :
    B.conjugate (b * n * c) = B.conjugate (b * n) := by
  rw [← ClosedSubgroup.conjugate_conjugate, conjugate_eq_of_mem B hc]

end Theory.AlgebraicGroup.BorelIntersectionGeometry
