module

public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.ChevalleyAction
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.OrbitEscape

/-!
# An escaping torus fixed Borel coset

The diagonal orbit of the base point in the complete model of G/B and the
actual projective Chevalley model of a proper parabolic P is closed, complete
and connected. Projective fixed-point escape gives a torus fixed point of
that diagonal orbit whose second coordinate differs from the base point.
Its common representative g satisfies g outside P and T inside gBg⁻¹.
This proves the geometric step of Borel 13.7 directly from the source
hypotheses, including both the second fixed point and its fixed lift.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Theory.AlgebraicGroup.Bor1.TorusBorelGeneration
open Variety.Geometric
open SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- The fixed coset outside a proper parabolic in the proof of Borel 13.7.
Both its escape and the torus containment are derived from actual complete
projective geometry, with no fixed-coset certificate. -/
theorem exists_fixed_borel_coset_outside_parabolic
    (hG : Variety.IsConnected G) (T P B : ClosedSubgroup G)
    (hT : IsSubtorus T) (hB : IsBorelSubgroup B) (hBP : B ≤ P)
    (hP : P.toSubgroup ≠ ⊤) :
    ∃ g : Variety.Point G, g ∉ P.toSubgroup ∧ T ≤ B.conjugate g := by
  obtain ⟨E, hEadd, hEmod, hEfin, ρ, b, A, x, hρ, he, hstab⟩ :=
    exists_projective_action_stabilizer P
  obtain ⟨M⟩ := nonempty_completeModel B hB
  let x₀ := modelBasePoint M
  let D := M.action.generationDiagonal A
  let p := prodPoint x₀ x
  have hcomplete : Variety.Geometric.IsComplete (Variety.Geometric.prod M.variety (projectiveSpace k E)) := by
    letI : UniversallyClosed M.variety.structureMap := M.complete
    letI : UniversallyClosed (projectiveSpace k E).structureMap := projectiveSpace_isComplete k E
    change UniversallyClosed (pullback.fst M.variety.structureMap
      (projectiveSpace k E).structureMap ≫ M.variety.structureMap)
    infer_instance
  have hfix : ∀ g ∈ B.toSubgroup, D.toMulAction.smul g p = p := by
    intro g hg
    rw [M.action.generationDiagonal_smul]
    exact congrArg₂ prodPoint ((modelBasePoint_stabilizer M g).mpr hg)
      ((hstab g).mpr (hBP hg))
  obtain ⟨z, hz⟩ : ∃ z : Variety.Point G, z ∉ P.toSubgroup := by
    by_contra! h
    exact hP (top_unique (fun z _ => h z))
  have hproj : ∀ (g : Variety.Point G)
      (q : Point (Variety.Geometric.prod M.variety (projectiveSpace k E))),
      projectiveSpacePointEquivOf b
        (snd M.variety (projectiveSpace k E) (D.toMulAction.smul g q)) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b (snd M.variety (projectiveSpace k E) q)) := by
    intro g q
    rw [M.action.generationDiagonal_snd]
    exact he g _
  obtain ⟨g, hgfix, hgoutside⟩ := D.exists_torus_fixedPoint_on_complete_borel_orbit
    hcomplete hG B hB ρ hρ T hT b (snd M.variety (projectiveSpace k E)) hproj p hfix z
    (by
      rw [M.action.generationDiagonal_smul, snd_prodPoint, snd_prodPoint]
      exact fun hzfix => hz ((hstab z).mp hzfix))
  refine ⟨g, ?_, ?_⟩
  · intro hg
    apply hgoutside
    rw [M.action.generationDiagonal_smul, snd_prodPoint, snd_prodPoint]
    exact (hstab g).mpr hg
  · intro t ht
    have htrange : t ∈ Set.range T.inclusion.onPoints := by
      rw [T.range_inclusion]
      exact ht
    obtain ⟨s, rfl⟩ := htrange
    apply (B.mem_conjugate_iff g _).mpr
    apply (modelBasePoint_stabilizer M _).mp
    have hhprod := hgfix s
    rw [M.action.generationDiagonal_smul, M.action.generationDiagonal_smul] at hhprod
    have hpair :
        (M.action.toMulAction.smul (T.includePoint s) (M.action.toMulAction.smul g x₀),
          A.toMulAction.smul (T.includePoint s) (A.toMulAction.smul g x)) =
        (M.action.toMulAction.smul g x₀, A.toMulAction.smul g x) :=
      (prodPointEquiv M.variety (projectiveSpace k E)).symm.injective hhprod
    have hh := congrArg Prod.fst hpair
    letI := M.action.toMulAction
    change (g⁻¹ * T.inclusion.onPoints s * g) • x₀ = x₀
    change T.inclusion.onPoints s • (g • x₀) = g • x₀ at hh
    simp only [mul_smul, hh, inv_smul_smul]

end Theory.AlgebraicGroup.Bor1.TorusBorelGeneration
