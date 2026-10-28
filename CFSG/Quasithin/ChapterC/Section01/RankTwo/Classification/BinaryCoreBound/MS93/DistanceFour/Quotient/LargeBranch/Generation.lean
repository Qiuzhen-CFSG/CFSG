module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.FirstFactor

/-!
# Removing Z_alpha from the two-span generation identity

Suppose the two recognized spans generate V_alpha^*. The radius/center/star
decomposition first places [V_alpha,Ltilde_alpha] in that star, since the
radius-center factor contributes commutators only in Z_alpha. Each span is
Z_alpha times its core factor. Their factors are normalized by the original
stabilizer and contain U_alpha = [Z_alpha,Ltilde_alpha]. Residual commutator
idempotence therefore removes Z_alpha and proves that the factors generate
the actual core. The previously proved intersection lemma finishes the
`OrbitFactors` contract.

This is the final passage in original MS93 (1993), (4.6.12), p.912, conditional
on the two recognized spans and their printed generation identity. No core
order bound or center equality is an input.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch

private theorem commutator_sup_le {G : Type*} [Group G] (A B C N : Subgroup G)
    (hn : A ⊔ B ≤ normalizer (N : Set G))
    (hA : ⁅A, C⁆ ≤ N) (hB : ⁅B, C⁆ ≤ N) : ⁅A ⊔ B, C⁆ ≤ N := by
  have hp : A ⊔ B ≤ commutatorPreimage (A ⊔ B) C N :=
    sup_le (le_commutatorPreimage le_sup_left hA) (le_commutatorPreimage le_sup_right hB)
  exact (commutator_mono hp le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hn)

variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  {common : CommonFacts R source geometry}

theorem factor_map_normalized {A : Subgroup (core R (alpha R))}
    (d : DualFactor source common A) :
    stabilizer R (alpha R) ≤ normalizer (A.map (core R (alpha R)).subtype : Set (FreeAmalgam R)) := by
  apply le_normalizer_iff.mpr
  intro m hm x hx
  rw [alpha, stabilizer_m_base] at hm
  obtain ⟨m, rfl⟩ := hm
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨coreAction (R := R) m a, d.normalized m a ha, rfl⟩

namespace FirstFactor
variable {c rho : Vertex R} (f : FirstFactor source common c)
    (g : FirstFactor source common rho)

include f g

/-- The literal star generation on p.912 generates the actual core factors:
first place the moving core in the star, then use residual commutator
idempotence to remove the extra Z_alpha factor. -/
theorem generate_of_star_generation [Finite M] (radius : RadiusFacts R geometry)
    (hstar : VStar R geometry (alpha R) (beta R) = orbitSpan c ⊔ orbitSpan rho) :
    f.factor ⊔ g.factor = ⊤ := by
  let T := f.factor.map (core R (alpha R)).subtype ⊔
    g.factor.map (core R (alpha R)).subtype
  have hTn : stabilizer R (alpha R) ≤ normalizer (T : Set (FreeAmalgam R)) :=
    (le_inf (factor_map_normalized f.data) (factor_map_normalized g.data)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hVL : V R (alpha R) ≤ stabilizer R (alpha R) :=
    geometry.V_local (alpha R) rfl common.large_distance
  have hZstar : Z R (alpha R) ≤ VStar R geometry (alpha R) (beta R) :=
    Flags.Z_le_star geometry radius.toEarlyFacts common.large_distance _ _ rfl (base_adjacent R)
  have hstarL : VStar R geometry (alpha R) (beta R) ≤ stabilizer R (alpha R) :=
    (Flags.star_le_radius geometry _ _).trans hVL
  have hstarN := Flags.star_normalized geometry (alpha R) (beta R)
  have hcoreStar : core R (alpha R) ≤ VStar R geometry (alpha R) (beta R) := by
    have hv := Flags.radius_eq_B_sup_star geometry radius.toEarlyFacts common.large_distance
      (alpha R) (beta R) rfl (base_adjacent R)
    rw [radius.core_eq_moving (alpha R) rfl, Vcirc, hv]
    apply commutator_sup_le
    · rw [← hv]
      exact hVL.trans hstarN
    · exact (Flags.B_commutator_le_Z geometry _ hVL).trans hZstar
    · exact le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans hstarN)
  have hstarZT : VStar R geometry (alpha R) (beta R) = Z R (alpha R) ⊔ T := by
    rw [hstar, f.span_decomposition, g.span_decomposition]
    simp only [T, sup_assoc, sup_left_comm, sup_left_idem]
  have hUT : U R (alpha R) ≤ T := by
    intro x hx
    exact mem_sup_left ⟨⟨x, U_le_core source geometry common hx⟩, f.data.contains hx, rfl⟩
  have hmove : ⁅VStar R geometry (alpha R) (beta R), Ltilde R (alpha R)⁆ ≤ T := by
    rw [hstarZT]
    apply commutator_sup_le
    · rw [← hstarZT]
      exact hstarL.trans hTn
    · exact hUT
    · exact le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans hTn)
  have hcoreT : core R (alpha R) ≤ T := by
    rw [← Flags.core_idempotent source (alpha R) rfl]
    exact (commutator_mono hcoreStar le_rfl).trans hmove
  apply top_unique
  intro x _
  have hx : (x : FreeAmalgam R) ∈ (f.factor ⊔ g.factor).map (core R (alpha R)).subtype := by
    rw [Subgroup.map_sup]
    exact hcoreT x.property
  obtain ⟨y, hy, he⟩ := hx
  exact (Subtype.ext he : y = x) ▸ hy

/-- The source star identity and the selected noncommutation complete the
actual two-factor contract, without any assumed order or center bound. -/
theorem orbitFactors_of_star_generation [Finite M] (radius : RadiusFacts R geometry)
    (hne : ⁅Z R rho, orbitSpan c⁆ ≠ ⊥)
    (hstar : VStar R geometry (alpha R) (beta R) = orbitSpan c ⊔ orbitSpan rho) :
    Nonempty (OrbitFactors source common c) := by
  exact ⟨⟨rho, (cosetGraph R).dist_comm.trans g.vertex_nu.1,
    f.factor, g.factor, f.factor_le, g.factor_le, f.data, g.data,
    f.generate_of_star_generation g radius hstar,
    f.data.intersect_of_ne g.data (f.factor_ne_of_noncommuting g hne)⟩⟩

end FirstFactor
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
