module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Requirements

/-!
# Intersection and generation of the full marked spans

Transitivity on nonzero dual vectors proves irreducibility for the actual
marked quotient by Z_alpha. Two noncommuting abelian spans therefore meet
in exactly Z_alpha. Their indices multiply to 64, so the source starred
index makes their join the whole starred subgroup.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12), pp.911--912.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
namespace RankOne.SpanQuotient
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  {common : CommonFacts R source geometry}
  {c rho : Vertex R} (q : SpanQuotient source common c)

include q

omit [Finite M] in
/-- Invariance under the actual stabilizer leaves no proper intermediate
subgroup between the kernel and a marked dual span. -/
theorem invariant_between (H : Subgroup (FreeAmalgam R))
    (hZH : Z R (alpha R) ≤ H) (hHS : H ≤ orbitSpan c)
    (hn : stabilizer R (alpha R) ≤ normalizer (H : Set (FreeAmalgam R))) :
    H = Z R (alpha R) ∨ H = orbitSpan c := by
  by_cases hHZ : H ≤ Z R (alpha R)
  · exact Or.inl (le_antisymm hHZ hZH)
  right
  apply le_antisymm hHS
  obtain ⟨x, hxH, hxZ⟩ := SetLike.not_le_iff_exists.mp hHZ
  let xS : orbitSpan c := ⟨x, hHS hxH⟩
  have hx : (q.quotient xS).toAdd ≠ 0 := by
    intro h
    apply hxZ
    have hk : xS ∈ q.quotient.ker := congrArg Multiplicative.ofAdd h
    rwa [q.kernel] at hk
  intro y hyS
  let yS : orbitSpan c := ⟨y, hyS⟩
  by_cases hy : (q.quotient yS).toAdd = 0
  · apply hZH
    have hk : yS ∈ q.quotient.ker := congrArg Multiplicative.ofAdd hy
    rwa [q.kernel] at hk
  obtain ⟨g, hg⟩ := Linear.dual_orbit hx hy
  obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
  have hmg : common.natural.marking (source.projection m) = g := by simp [hm]
  have hmS : embedM R m ∈ stabilizer R (alpha R) := by
    rw [alpha, stabilizer_m_base]
    exact ⟨m, rfl⟩
  let z : orbitSpan c := ⟨embedM R m * x * (embedM R m)⁻¹,
    (mem_normalizer_iff.mp (orbitSpan_normalized c hmS) _).mp xS.property⟩
  have hzH : (z : FreeAmalgam R) ∈ H := (mem_normalizer_iff.mp (hn hmS) _).mp hxH
  have he : q.quotient z = q.quotient yS := by
    apply congrArg Multiplicative.ofAdd
    exact (q.action m xS z rfl).trans (by rw [hmg]; exact hg)
  have hk : yS * z⁻¹ ∈ q.quotient.ker := by
    change q.quotient (yS * z⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [q.kernel] at hk
  have hh := H.mul_mem (hZH hk) hzH
  change (y * (z : FreeAmalgam R)⁻¹) * z ∈ H at hh
  simpa only [inv_mul_cancel_right] using hh

/-- Noncommutation forces the literal intersection to be the common kernel. -/
theorem intersect (hc : (cosetGraph R).dist (alpha R) c = 2)
    (hrho : (cosetGraph R).dist (alpha R) rho = 2)
    (hab : IsMulCommutative (orbitSpan rho))
    (hne : ⁅Z R rho, orbitSpan c⁆ ≠ ⊥) :
    orbitSpan c ⊓ orbitSpan rho = Z R (alpha R) := by
  have hn : stabilizer R (alpha R) ≤
      normalizer (orbitSpan c ⊓ orbitSpan rho : Set (FreeAmalgam R)) :=
    (le_inf (orbitSpan_normalized c) (orbitSpan_normalized rho)).trans
      inf_normalizer_le_normalizer_inf
  rcases q.invariant_between _
    (le_inf (Z_le_orbitSpan_of_distance_two c hc)
      (Z_le_orbitSpan_of_distance_two rho hrho)) inf_le_left hn with h | h
  · exact h
  · exfalso
    apply hne
    have hle : orbitSpan c ≤ orbitSpan rho := h ▸ inf_le_right
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (Z_le_orbitSpan rho).trans
      ((le_centralizer_iff_isMulCommutative.mpr hab).trans (centralizer_le hle))

omit q in
private theorem relIndex_join {G : Type*} [Group G] (A B : Subgroup G)
    (hn : B ≤ normalizer (A : Set G)) : A.relIndex (A ⊔ B) = A.relIndex B := by
  let T := A ⊔ B
  let : (A.subgroupOf T).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have h := relIndex_sup_left (B.subgroupOf T) (A.subgroupOf T)
  rw [← subgroupOf_sup le_sup_left le_sup_right, relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at h
  exact h

/-- The two actual indices eight exhaust the starred quotient of order 64. -/
theorem star_generation (radius : RadiusFacts R geometry)
    (r : SpanQuotient source common rho)
    (hc : nu R geometry (alpha R) c) (hrho : nu R geometry (alpha R) rho)
    (hab : IsMulCommutative (orbitSpan rho)) (hne : ⁅Z R rho, orbitSpan c⁆ ≠ ⊥)
    (hindex : (Z R (alpha R)).relIndex (VStar R geometry (alpha R) (beta R)) = 64) :
    VStar R geometry (alpha R) (beta R) = orbitSpan c ⊔ orbitSpan rho := by
  let T := orbitSpan c ⊔ orbitSpan rho
  have hTV : T ≤ VStar R geometry (alpha R) (beta R) := sup_le
    (orbitSpan_le_star geometry radius.toEarlyFacts _ _ (base_adjacent R) hc)
    (orbitSpan_le_star geometry radius.toEarlyFacts _ _ (base_adjacent R) hrho)
  have hlocal : orbitSpan rho ≤ stabilizer R (alpha R) :=
    (orbitSpan_le_radius rho hrho.1.le).trans
      (geometry.V_local (alpha R) rfl common.large_distance)
  have hjoin : (orbitSpan c).relIndex T = 8 := by
    change (orbitSpan c).relIndex (orbitSpan c ⊔ orbitSpan rho) = 8
    rw [relIndex_join _ _ (hlocal.trans (orbitSpan_normalized c)),
      ← inf_relIndex_right, q.intersect ((cosetGraph R).dist_comm.trans hc.1)
        ((cosetGraph R).dist_comm.trans hrho.1) hab hne]
    exact r.quotient_index
  have hZ := Z_le_orbitSpan_of_distance_two c ((cosetGraph R).dist_comm.trans hc.1)
  have hZT : (Z R (alpha R)).relIndex T = 64 := by
    have h := relIndex_mul_relIndex (Z R (alpha R)) (orbitSpan c) T hZ le_sup_left
    rw [q.quotient_index, hjoin] at h
    exact h.symm
  have h := relIndex_mul_relIndex (Z R (alpha R)) T
    (VStar R geometry (alpha R) (beta R)) (hZ.trans le_sup_left) hTV
  rw [hZT, hindex] at h
  have hi : T.relIndex (VStar R geometry (alpha R) (beta R)) = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp hi) hTV

end RankOne.SpanQuotient
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
