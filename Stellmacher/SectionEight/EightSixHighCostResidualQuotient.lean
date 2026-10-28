module
public import Stellmacher.SectionEight.EightSixHighCostModuleData
/-!
# The actual high-cost residual quotient is elementary cubic

For the selected high-cost graph configuration, with elementary D from the
common structure, the native quotient E_next/O₂(E_next) is elementary
abelian of exponent three. No actor rank, action kernel, or model is
assumed beyond the original local high-cost hypotheses.

The actual module-data theorem constructs the next-stabilizer action on
Vnext/Znext with exact two-core kernel and elementary residual image.
Restricting that same action to E_next gives a quotient witness. The normal
residual-core intersection identity identifies its kernel exactly with
O₂(E_next), so its elementary image proves the native quotient assertion.

This is the elementary-group assertion of Stellmacher (8.6)(21), printed
p.45, transferred from the literal action image to the public case-C
quotient. The four independent order-three factors and resulting order81
remain separate conclusions.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_six_high_cost_residual_quotient_is_elementary
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (ha : actor ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a)
    (hout : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hlarge : 4 * Nat.card
      ((VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) ⊓ D : Subgroup G) ≤
      Nat.card (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G))
    (hmin : ∀ other : G, other ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      other ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        eightSixCommutatorCost ctx.Γ ctx.criticalPath actor ≤
          eightSixCommutatorCost ctx.Γ ctx.criticalPath other)
    (hQ : Q = twoCoreIn L)
    (hhigh : ∀ mover : G, mover ∈ VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a →
      mover ∉ QAt ctx.Γ ctx.criticalPath.firstStep →
        8 ≤ eightSixCommutatorCost ctx.Γ ctx.criticalPath mover)
    (helementary : IsElementaryAbelianSubgroup 2 D)
 :
    QuotientIsElementaryAbelian
      (EAt ctx.Γ ctx.criticalPath.firstStep)
      (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) 3 := by
  obtain ⟨hN,hW,action,_hformula,hkernel,hF⟩ := eight_six_high_cost_residual_module_data
    ctx hcenter hquot hlength hcard previous D L Q hprev data E A0 actor geom
    hcore hedge hD hL ha hout hlarge hmin hQ hhigh helementary
  let _ := hN
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let W := V ⧸ Z.subgroupOf V
  let R := EAt Γ cp.firstStep
  have hR : R = twoResidualIn P := Γ.twoResidualAt_def _
  have hRP : R ≤ P := hR ▸ SevenSix.twoResidualIn_le P
  let f : R →* MulAut W := action.comp (Subgroup.inclusion hRP)
  have hrange : f.range = ((twoResidualIn P).subgroupOf P).map action := by
    rw [MonoidHom.range_comp,Subgroup.inclusion_range,hR]
  have hF' : IsElementaryAbelian 3 f.range := hrange.symm ▸ hF
  have hcore : twoCoreIn R = R ⊓ QAt Γ cp.firstStep := by
    rw [hR,SevenSix.residual_core_eq_inter_core]
    rw [show QAt Γ cp.firstStep = twoCoreIn P from Γ.twoCoreAt_def _]
  have hnative : (QAt Γ cp.firstStep).subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt cp.firstStep).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hker : f.rangeRestrict.ker = (twoCoreIn R).subgroupOf R := by
    rw [MonoidHom.ker_rangeRestrict,←MonoidHom.comap_ker,hkernel,←hnative,hcore]
    ext r
    change (r:G) ∈ QAt Γ cp.firstStep ↔ (r:G) ∈ R ⊓ QAt Γ cp.firstStep
    exact ⟨fun hr => ⟨r.property,hr⟩, fun hr => hr.2⟩
  exact ⟨{ X := f.range
           projection := f.rangeRestrict
           surjective := f.rangeRestrict_surjective
           kernel_eq := hker }, hF'⟩
end Stellmacher.SectionEight
