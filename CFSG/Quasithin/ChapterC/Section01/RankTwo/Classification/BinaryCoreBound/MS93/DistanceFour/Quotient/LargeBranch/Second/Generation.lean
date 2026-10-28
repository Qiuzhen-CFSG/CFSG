module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.FirstFactor

/-!
# Two-span generation from the actual starred index

Each recognized factor has order 64 and intersects Z_alpha in U_alpha.
Its full conjugate span therefore has index eight over Z_alpha. The same
irreducibility argument shows that a stabilizer-invariant subgroup of the
span above Z_alpha is either Z_alpha or the whole span. For two spans
selected by noncommutation, the latter intersection alternative contradicts
the second span's commutativity. Their intersection is consequently exactly
Z_alpha, and their join has index 64. The starred index from (4.6.12)(5)
then proves equality with the actual starred subgroup.

All normalization is relative to the actual base stabilizer; no normality
in the infinite free amalgam is assumed. The two marked factors and starred
index are explicit inputs here. Reapplying the first-stage construction to
obtain the second factor remains a separate source obligation.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(5) and its final
paragraph, printed pp.911--912.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
private theorem relIndex_join {G : Type*} [Group G] (A B : Subgroup G)
    (hn : B ≤ normalizer (A : Set G)) : A.relIndex (A ⊔ B) = A.relIndex B := by
  let T := A ⊔ B
  let : (A.subgroupOf T).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have h := relIndex_sup_left (B.subgroupOf T) (A.subgroupOf T)
  rw [← subgroupOf_sup le_sup_left le_sup_right, relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at h
  exact h

variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  {common : CommonFacts R source geometry}
namespace FirstFactor
variable {c rho : Vertex R} (f : FirstFactor source common c)
include f

private theorem layer_in_span : Z R (alpha R) ≤ orbitSpan c := by
  rw [f.span_decomposition]
  exact le_sup_left

private theorem factor_local [Finite M] :
    f.factor.map (core R (alpha R)).subtype ≤ stabilizer R (alpha R) :=
  (map_subtype_le _).trans ((core_le_Q source).trans (fun _ hx => hx.1))

private theorem invariant_factor_intersection (H : Subgroup (FreeAmalgam R))
    (hZH : Z R (alpha R) ≤ H)
    (hn : stabilizer R (alpha R) ≤ normalizer (H : Set (FreeAmalgam R))) :
    f.factor ⊓ H.subgroupOf (core R (alpha R)) =
      (U R (alpha R)).subgroupOf (core R (alpha R)) ∨
    f.factor ⊓ H.subgroupOf (core R (alpha R)) = f.factor := by
  apply f.data.invariant_between
  · exact le_inf f.data.contains (fun x hx => hZH (DistanceEight.U_le_Z R _ hx))
  · exact inf_le_left
  · intro m x hx
    refine ⟨f.data.normalized m x hx.1, ?_⟩
    have hm : embedM R m ∈ stabilizer R (alpha R) := by
      rw [alpha, stabilizer_m_base]
      exact ⟨m, rfl⟩
    exact (mem_normalizer_iff.mp (hn hm) _).mp hx.2

private theorem factor_intersect_layer :
    f.factor ⊓ (Z R (alpha R)).subgroupOf (core R (alpha R)) =
      (U R (alpha R)).subgroupOf (core R (alpha R)) := by
  rcases f.invariant_factor_intersection _ le_rfl (Z_normalized R _) with h | h
  · exact h
  · exfalso
    apply f.span_not_le_Z
    rw [f.span_decomposition]
    refine sup_le le_rfl ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ f.factor ⊓ (Z R (alpha R)).subgroupOf (core R (alpha R)) := h.symm ▸ hx
    exact hx'.2

/-- Each recognized conjugate span has the literal index eight above Z_alpha. -/
theorem span_relIndex [Finite M] : (Z R (alpha R)).relIndex (orbitSpan c) = 8 := by
  rw [f.span_decomposition, relIndex_join _ _ (f.factor_local.trans (Z_normalized R _)),
    ← relIndex_comap]
  change ((Z R (alpha R)).subgroupOf (core R (alpha R))).relIndex f.factor = 8
  rw [← inf_relIndex_right, inf_comm, f.factor_intersect_layer]
  have h := relIndex_mul_relIndex (⊥ : Subgroup (core R (alpha R)))
    ((U R (alpha R)).subgroupOf (core R (alpha R))) f.factor bot_le f.data.contains
  rw [relIndex_bot_left, relIndex_bot_left, f.data.card,
    Nat.card_congr (subgroupOfEquivOfLe (U_le_core source geometry common)).toEquiv,
    U_card source geometry common] at h
  omega

/-- There is no intermediate stabilizer-invariant subgroup above Z_alpha. -/
theorem span_invariant_between [Finite M] (H : Subgroup (FreeAmalgam R))
    (hZH : Z R (alpha R) ≤ H) (hHS : H ≤ orbitSpan c)
    (hn : stabilizer R (alpha R) ≤ normalizer (H : Set (FreeAmalgam R))) :
    H = Z R (alpha R) ∨ H = orbitSpan c := by
  rcases f.invariant_factor_intersection H hZH hn with h | h
  · left
    apply le_antisymm _ hZH
    intro x hx
    have hxS := hHS hx
    rw [f.span_decomposition] at hxS
    have hxprod : x ∈ (Z R (alpha R) : Set (FreeAmalgam R)) *
        (f.factor.map (core R (alpha R)).subtype : Set (FreeAmalgam R)) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        (f.factor_local.trans (Z_normalized R _))]
      exact hxS
    obtain ⟨z, hz, a, ha, rfl⟩ := hxprod
    obtain ⟨a, ha, rfl⟩ := ha
    have haH : (a : FreeAmalgam R) ∈ H := by
      simpa only [inv_mul_cancel_left, subtype_apply] using H.mul_mem (H.inv_mem (hZH hz)) hx
    have haU : a ∈ (U R (alpha R)).subgroupOf (core R (alpha R)) := h ▸ ⟨ha, haH⟩
    exact (Z R (alpha R)).mul_mem hz (DistanceEight.U_le_Z R _ haU)
  · right
    apply le_antisymm hHS
    rw [f.span_decomposition]
    refine sup_le hZH ?_
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ∈ f.factor ⊓ H.subgroupOf (core R (alpha R)) := h.symm ▸ ha
    exact ha'.2

/-- Noncommutation forces the two full spans to intersect precisely in Z_alpha. -/
theorem span_intersect [Finite M] (g : FirstFactor source common rho)
    (hne : ⁅Z R rho, orbitSpan c⁆ ≠ ⊥) :
    orbitSpan c ⊓ orbitSpan rho = Z R (alpha R) := by
  have hn : stabilizer R (alpha R) ≤
      normalizer (orbitSpan c ⊓ orbitSpan rho : Set (FreeAmalgam R)) :=
    (le_inf (orbitSpan_normalized c) (orbitSpan_normalized rho)).trans
      inf_normalizer_le_normalizer_inf
  rcases f.span_invariant_between _ (le_inf f.layer_in_span g.layer_in_span) inf_le_left hn with h | h
  · exact h
  · exfalso
    apply hne
    have hle : orbitSpan c ≤ orbitSpan rho := h ▸ inf_le_right
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (Z_le_orbitSpan rho).trans
      ((le_centralizer_iff_isMulCommutative.mpr g.span_commutative).trans (centralizer_le hle))

/-- The index 64 in (4.6.12)(5) makes the two recognized noncommuting spans
exhaust the actual starred subgroup. -/
theorem star_generation [Finite M] (radius : RadiusFacts R geometry)
    (g : FirstFactor source common rho) (hne : ⁅Z R rho, orbitSpan c⁆ ≠ ⊥)
    (hindex : (Z R (alpha R)).relIndex (VStar R geometry (alpha R) (beta R)) = 64) :
    VStar R geometry (alpha R) (beta R) = orbitSpan c ⊔ orbitSpan rho := by
  let T := orbitSpan c ⊔ orbitSpan rho
  have hTV : T ≤ VStar R geometry (alpha R) (beta R) := sup_le
    (orbitSpan_le_star geometry radius.toEarlyFacts _ _ (base_adjacent R) f.vertex_nu)
    (orbitSpan_le_star geometry radius.toEarlyFacts _ _ (base_adjacent R) g.vertex_nu)
  have hlocal : orbitSpan rho ≤ stabilizer R (alpha R) :=
    (orbitSpan_le_radius rho g.vertex_nu.1.le).trans
      (geometry.V_local (alpha R) rfl common.large_distance)
  have hjoin : (orbitSpan c).relIndex T = 8 := by
    change (orbitSpan c).relIndex (orbitSpan c ⊔ orbitSpan rho) = 8
    rw [relIndex_join _ _ (hlocal.trans (orbitSpan_normalized c)),
      ← inf_relIndex_right, f.span_intersect g hne]
    exact g.span_relIndex
  have hZT : (Z R (alpha R)).relIndex T = 64 := by
    have h := relIndex_mul_relIndex (Z R (alpha R)) (orbitSpan c) T
      f.layer_in_span le_sup_left
    rw [f.span_relIndex, hjoin] at h
    exact h.symm
  have h := relIndex_mul_relIndex (Z R (alpha R)) T
    (VStar R geometry (alpha R) (beta R)) (f.layer_in_span.trans le_sup_left) hTV
  rw [hZT, hindex] at h
  have hi : T.relIndex (VStar R geometry (alpha R) (beta R)) = 1 := by omega
  exact le_antisymm (relIndex_eq_one.mp hi) hTV

end FirstFactor
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
