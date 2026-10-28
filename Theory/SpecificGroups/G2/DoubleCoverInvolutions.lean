module

public import Theory.GroupTheory.DoubleCoverInvolutionLifting
public import Theory.AtlasPort.LinearGroups.G2.LongRootPlaneLiftInterface
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.RootElements
public import Theory.AtlasPort.LinearGroups.G2.TorusNormalization

/-!
# Two-central involutions in actual double covers of G₂(4)

The two root groups A and B form an elementary plane of order sixteen. Its
nonidentity elements and all two-central involutions are conjugate to A(1):
the root shear handles the plane, the Sylow-center calculation handles
central involutions, and the split torus scales the nonzero parameter.
The double-cover involution theorem supplies one involutory lift in this
plane; lifting conjugators supplies every two-central involution. Thus the
full inverse image of the plane is elementary of order thirty-two.

Source: Aschbacher–Smith I.2.2(5a), printed pp.409–411, and 16.3.9, p.1181
(combined 1 March 2004 manuscript). The earlier multiplier input |Z(K)|=2
is explicit; no involution-lifting premise remains. Neither quasisimplicity
nor finite-group universality is needed once that input is supplied.
The imported octonion root formulas retain the attribution and license in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. These new proofs use those
established formulas without porting new ATLAS source.
-/

public section

namespace Atlas.G2.DoubleCoverInvolutions
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverInvolutionLifting
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
theorem rootA_isConj_one {a : F} (ha : a ≠ 0) :
    IsConj (rootA (1 : F)) (rootA a) := by
  apply isConj_iff.mpr
  refine ⟨torus (Units.mk0 a ha) 1, ?_⟩
  simpa only [Units.val_mk0, Units.val_one, mul_one] using
    torus_rootA (Units.mk0 a ha) 1 (1 : F)

omit [CharP F 2] [Finite F] in
theorem isConj_one_of_long {x : Model F}
    (hx : ShortRootProducts.IsLongRootElement x) : IsConj (rootA (1 : F)) x := by
  obtain ⟨a, ha, g, rfl⟩ := hx
  exact (rootA_isConj_one ha).trans (isConj_iff.mpr ⟨g, rfl⟩)

theorem isConj_one_of_twoCentral {x : Model F}
    (hx : IsSylowCentralInvolution x) : IsConj (rootA (1 : F)) x := by
  obtain ⟨ho, S, hm, hc⟩ := hx
  have hne : x ≠ 1 := by intro he; simp [he] at ho
  obtain ⟨g, a, ha, rfl⟩ := EvenInvolutionGeometry.central_involution_isLongRoot
    S hm (ho ▸ pow_orderOf_eq_one x)
    (fun y hy => (mem_centralizer_singleton_iff.mp (hc hy)).symm) hne
  exact (rootA_isConj_one ha).trans (isConj_iff.mpr ⟨g, rfl⟩)

theorem central_involution_lifting
    {K : Type*} [Group K] [Finite K]
    (e : (K ⧸ center K) ≃* Model F) (hF : Nat.card F = 4)
    (hZ : Nat.card (center K) = 2) :
    LongRootPlaneLift.CentralInvolutionLifting K := by
  let f : K →* Model F := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center K := by
    ext x
    change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let : IsElementaryAbelian 2 (longRootLocal (F := F)) := LongRootPlaneLift.elementary
  obtain ⟨y, hy2, hyE, hyn⟩ := exists_involution_above_elementary_subgroup f hf
    (hk ▸ hZ) longRootLocal (by rw [LongRootPlaneLift.card_eq_sixteen hF]; decide)
  have hroot := isConj_one_of_long (ShortRootProducts.longRootLocal_isLong hyE hyn)
  apply (LongRootPlaneLift.centralInvolutionLifting_iff K).mpr
  intro x hx
  obtain ⟨z, hz, hz2⟩ := involution_lift_of_isConj f hf hy2
    (hroot.symm.trans (isConj_one_of_twoCentral (hx.map e)))
  exact ⟨z, e.injective hz, hz2⟩

theorem double_cover_rank_ge_five
    {K : Type*} [Group K] [Finite K]
    (e : (K ⧸ center K) ≃* Model F) (hF : Nat.card F = 4)
    (hZ : Nat.card (center K) = 2) : 5 ≤ primeRank 2 K :=
  LongRootPlaneLift.rank_ge_five e hF hZ (central_involution_lifting e hF hZ)

end Atlas.G2.DoubleCoverInvolutions
