module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.PerpendicularKernel
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Actor

/-!
# The original natural involution lies in the partner actor

The selected cubic moves the point perpendicular. A natural vector in its
conjugate perpendicular therefore lies in X and outside Q_H. Since the
original natural actor has order two, this common nonidentity actor proves
V* ≤ X* on the literal quotient H/O₂(H).
Source: Aschbacher–Smith 15.3.53 and 15.3.56(4–6), pp.1146–1148.
-/
@[expose] public noncomputable section
open Matrix Subgroup ClassicalOrthogonal.FourPlusMatrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open CFSG.Quasithin.ChapterG.Section02.Setup
namespace MatrixOrbit
private theorem cubic_moves_perp (X : M) (hX : X ≠ 0) (hs : X.det=0) :
    ∃ v : M, determinantForm.polarBilin v X ≠ 0 ∧
      determinantForm.polarBilin (matrixAction leftCubic v) X=0 := by
  simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,determinantForm_apply]
  exact (show ∀ X : M, X≠0 → X.det=0 → ∃ v : M,
    (v+X).det-v.det-X.det≠0 ∧
      (matrixAction leftCubic v+X).det-(matrixAction leftCubic v).det-X.det=0
    by decide +kernel) X hX hs
end MatrixOrbit
variable {G : Type*} [Group G] [Finite G] {D : CFSG.Quasithin.ChapterG.Section02.Setup G}
  {g : G} (d : Hypothesis D g)

private theorem lift_mem_perp_iff (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (v : MatrixOrbit.M) : matrixLift d (Multiplicative.ofAdd v) ∈ D.V ↔
      determinantForm.polarBilin v (d.pointVector z)=0 := by
  change (d.coordinates.symm (Multiplicative.ofAdd v) : G) ∈ D.V ↔ _
  rw [d.perpendicular]
  simp only [d.coordinates.apply_symm_apply]
  change (∀ w : D.V₁, determinantForm.polarBilin v (d.pointVector w)=0) ↔ _
  constructor
  · exact fun h => h z
  · intro h w
    rcases d.pointVector_zero_or_eq z hz w with hw | hw
    · rw [hw,map_zero]
    · rw [hw]
      exact h

/-- An actual element common to V and X survives the original hyperplane. -/
theorem exists_natural_partner_outside_perp (Z ZS : Subgroup G)
    (hZ : D.V₁=Z) (hU : D.U=closureU Z ZS)
    (y : D.I g) (hyc : matrixSection d y=MatrixOrbit.leftCubic) :
    ∃ v ∈ D.VL ⊓ partnerX Z ZS (y:G), v ∉ D.V := by
  let := d.VL_elementary
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  obtain ⟨v,hvn,hvw⟩ := MatrixOrbit.cubic_moves_perp (d.pointVector z) hz (d.pointVector_det z)
  let vG := matrixLift d (Multiplicative.ofAdd v)
  let w := matrixLift d (Multiplicative.ofAdd (matrixAction MatrixOrbit.leftCubic v))
  have hvVL : vG ∈ D.VL := (d.coordinates.symm (Multiplicative.ofAdd v)).property
  have hwV : w ∈ D.V := (lift_mem_perp_iff d z hz _).mpr hvw
  have heq : w=(y:G)*vG*(y:G)⁻¹ := by
    have hh := matrixLift_equivariant d y (Multiplicative.ofAdd v)
    change matrixLift d (Multiplicative.ofAdd (matrixAction (matrixSection d y) v)) = _ at hh
    rw [hyc] at hh
    exact hh
  have hZVL : Z ≤ D.VL := hZ ▸ point_le_VL D
  have hZyVL : rightConjugate Z (y:G) ≤ D.VL := by
    rintro _ ⟨a,ha,rfl⟩
    exact (mem_normalizer_iff.mp (d.I_normalizes_VL ((D.I g).inv_mem y.property)) a).mp
      (hZVL ha)
  have hwF : w ∈ intersectionF Z ZS (y:G) := by
    refine ⟨hU ▸ (d.VL_inf_U.ge hwV).2, ?_⟩
    rw [rightConjugate_centralizer]
    exact ((D.VL.le_centralizer).trans (centralizer_le hZyVL)) (d.V_le_VL hwV)
  refine ⟨vG,⟨hvVL,⟨w,hwF,?_⟩⟩,?_⟩
  · change (y:G)⁻¹*w*((y:G)⁻¹)⁻¹=vG
    rw [heq]
    group
  · exact fun hv => hvn ((lift_mem_perp_iff d z hz v).mp hv)

open Recognition
omit [Finite G] in
/-- A shared nonidentity element exhausts the original order-two actor. -/
theorem actor_le_of_order_two_and_common_outside (Z V X : Subgroup G)
    (hVH : V ≤ centralizerH Z) (hcard : Nat.card (actorImage Z V)=2)
    (hcommon : ∃ v ∈ V ⊓ X, v ∉ coreQ Z) : actorImage Z V ≤ actorImage Z X := by
  obtain ⟨v,hv,hn⟩ := hcommon
  let vH : centralizerH Z := ⟨v,hVH hv.1⟩
  let a : ActorQuotient Z := QuotientGroup.mk' _ vH
  have haV : a ∈ actorImage Z V := ⟨vH,hv.1,rfl⟩
  have haX : a ∈ actorImage Z X := ⟨vH,hv.2,rfl⟩
  have hna : a ≠ 1 := by
    intro he
    exact hn (mem_map_of_mem (centralizerH Z).subtype ((QuotientGroup.eq_one_iff _).mp he))
  obtain ⟨b,_,hall⟩ := (Nat.card_eq_two_iff' (1 : actorImage Z V)).mp hcard
  intro c hc
  by_cases hc1 : c=1
  · exact hc1 ▸ (actorImage Z X).one_mem
  have hca : c=a := congrArg Subtype.val
    ((hall ⟨c,hc⟩ (fun h => hc1 (congrArg Subtype.val h))).trans
      (hall ⟨a,haV⟩ (fun h => hna (congrArg Subtype.val h))).symm)
  exact hca ▸ haX

/-- The exact V*≤X* field of the source-56 recognition inputs. -/
theorem natural_actor_le_partner (Z ZS : Subgroup G)
    (hZ : D.V₁=Z) (hU : D.U=closureU Z ZS)
    (y : D.I g) (hyc : matrixSection d y=MatrixOrbit.leftCubic)
    (hVQ : D.VL ⊓ coreQ Z=D.V) (hcard : Nat.card (actorImage Z D.VL)=2) :
    actorImage Z D.VL ≤ actorImage Z (partnerX Z ZS (y:G)) := by
  let := d.VL_elementary
  have hVH : D.VL ≤ centralizerH Z :=
    D.VL.le_centralizer.trans (centralizer_le (hZ ▸ point_le_VL D))
  apply actor_le_of_order_two_and_common_outside Z _ _ hVH hcard
  obtain ⟨v,hv,hn⟩ := exists_natural_partner_outside_perp d Z ZS hZ hU y hyc
  refine ⟨v,hv,fun hq => hn ?_⟩
  exact hVQ ▸ (show v ∈ D.VL ⊓ coreQ Z from ⟨hv.1,hq⟩)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
