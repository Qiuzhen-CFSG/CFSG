module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting.Intervals
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting.SymmetricQuotient.SelfDual
public import Theory.SpecificGroups.Alternating.FiveCentralChiefFactors
public import Theory.GroupTheory.NoncentralChiefRefinement.CentralPQuotient

/-!
# The S₅ quotient and natural dual factor in H-chief accounting

Every binary S₅-chief factor is central, including its top C₂ factor. The
original surjection `d.qH`, with kernel the actual two-core of H, therefore
makes every chief refinement above that core contribute zero noncentral
binary factors.

Full S₅-equivariant self-duality pulls back through the same `d.qH`. Applying
its inverse to the existing literal Q_K/C_H(U) dual coordinates identifies
that chief factor with one copy of the original natural action. The original
dual coordinates and their functional-kernel formula are retained.

Source: Aschbacher–Smith, 14.7.71(1), printed p.1075 (PDF p.1092), using the
duality of 14.5.21(1), printed pp.1019–1020. The construction of the dual
witness and the other intervals' contributions remain with HAccounting.
-/

public section
noncomputable section
open Subgroup Representation NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The genuine quotient by the original H → S₅ kernel has central binary chief factors. -/
theorem coreQuotient_hasCentralTwoChiefFactors :
    HasCentralPChiefFactors 2 (F.H ⧸ (coreNode d).val) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective d.qH d.qH_surjective
  exact alternatingGroup.symmetric_five_hasCentralTwoChiefFactors.of_surjective
    e.symm.toMonoidHom e.symm.surjective

/-- Every actual binary chief interval above the original kernel is central. -/
theorem isCentral_above_core {A B : NormalNode F.H} (hAB : A ⋖ B)
    (hcore : coreNode d ≤ A) (hp : IsPGroup 2 (Section A B)) : IsCentral A B :=
  isCentral_of_quotient_hasCentralTwoChiefFactors (coreNode d)
    (coreQuotient_hasCentralTwoChiefFactors d) hAB hcore hp

include d in
/-- The source two-core formulation, using precisely `Data.qH_ker`. -/
theorem isCentral_above_twoCore {A B : NormalNode F.H} (hAB : A ⋖ B)
    (hcore : (F.H.pCoreIn 2).subgroupOf F.H ≤ A.val)
    (hp : IsPGroup 2 (Section A B)) : IsCentral A B := by
  apply isCentral_above_core d hAB _ hp
  change d.qH.ker ≤ A.val
  rw [d.qH_ker]
  exact hcore

/-- Any terminal chief refinement above O₂(H) contributes zero noncentral factors. -/
theorem terminal_noncentralTwoCount (s : ChiefSeries F.H)
    (hs : coreNode d ≤ s.head) : s.noncentralTwoCount = 0 :=
  s.noncentralTwoCount_eq_zero_of_centralTwo_quotient (coreNode d) hs
    (coreQuotient_hasCentralTwoChiefFactors d)

/-- Self-duality for the original H action, pulled back through its marked quotient map. -/
def naturalSelfDual : (naturalAction d).Equiv (naturalAction d).dual where
  __ := d.naturalQuotient.selfDual.toLinearEquiv
  isIntertwining' h := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    have he := congrArg (fun f : Module.Dual (ZMod 2) SL2FourNatural.V => f w)
      (d.naturalQuotient.selfDual_equivariant (d.qH h) v)
    change d.naturalQuotient.selfDual.toLinearEquiv (d.naturalQuotient.action (d.qH h) v) w =
      d.naturalQuotient.selfDual.toLinearEquiv v (d.naturalQuotient.action (d.qH h⁻¹) w)
    change d.naturalQuotient.selfDual.toLinearEquiv (d.naturalQuotient.action (d.qH h) v) w =
      d.naturalQuotient.selfDual.toLinearEquiv v (d.naturalQuotient.action (d.qH h)⁻¹ w) at he
    simpa only [map_inv] using he

private def dualCopies : Multiplicative (Fin 1 → Module.Dual (ZMod 2) SL2FourNatural.V) ≃*
    Multiplicative (Fin 1 → SL2FourNatural.V) where
  toFun v := Multiplicative.ofAdd (fun i => (naturalSelfDual d).symm.toLinearEquiv (v.toAdd i))
  invFun v := Multiplicative.ofAdd (fun i => (naturalSelfDual d).toLinearEquiv (v.toAdd i))
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    exact (naturalSelfDual d).toLinearEquiv.apply_symm_apply _
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    exact (naturalSelfDual d).toLinearEquiv.symm_apply_apply _
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext i
    exact (naturalSelfDual d).symm.toLinearEquiv.map_add _ _

/-- The literal dual chief interval is one copy of the original natural H module. -/
def naturalDualChiefCoordinates (b : QKDualCoordinates d) :
    SectionCoordinates (cNode d) (qKNode d b) (naturalAction d) 1 where
  equiv := (dualChiefCoordinates d b).equiv.trans (dualCopies d)
  equivariant h x i := by
    change (naturalSelfDual d).symm.toLinearEquiv
      (((dualChiefCoordinates d b).equiv (sectionAction _ _ h x)).toAdd i) = _
    rw [(dualChiefCoordinates d b).equivariant]
    exact LinearMap.congr_fun ((naturalSelfDual d).symm.isIntertwining' h) _

/-- On representatives, only the dual vector is transported; the quotient map is unchanged. -/
theorem naturalDualChiefCoordinates_mk (b : QKDualCoordinates d)
    (a : (qKNode d b).val) (i : Fin 1) :
    ((naturalDualChiefCoordinates d b).equiv
      (QuotientGroup.mk' ((cNode d).val.subgroupOf (qKNode d b).val) a)).toAdd i =
    (naturalSelfDual d).symm.toLinearEquiv
      ((b.qSection.coordinates ((subgroupOfEquivOfLe b.qSection.section_le) a)).toAdd) := by
  change (naturalSelfDual d).symm.toLinearEquiv
    (((dualChiefCoordinates d b).equiv (QuotientGroup.mk' _ a)).toAdd i) = _
  rw [dualChiefCoordinates_mk]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting
