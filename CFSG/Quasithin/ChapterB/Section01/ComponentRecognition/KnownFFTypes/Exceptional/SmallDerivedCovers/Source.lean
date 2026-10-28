module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.SmallDerivedCovers
public import Theory.SpecificGroups.SU3.TernaryPerfectCover
public import Theory.SpecificGroups.Tits.CentralCoverLifting.CompatibleGenerators.Source

/-!
# The source covering identifications for G₂(2)′ and Tits

For a finite perfect group with trivial two-core, the given central quotient
isomorphism to the actual binary octonion commutator defines a central cover.
Its kernel is a two-group by the ternary unitary comparison and transfer.
Being normal, that kernel lies in the original two-core and is therefore
trivial. This argument needs no calculation of the two-primary multiplier.

For the Parrott Tits carrier, the compatible lifts satisfy all 37 source
relations in the canonical universal cover. Their section and perfectness
give trivial universal kernel, hence trivial kernel for the given cover.
Both resulting isomorphisms are the original marked central projections.
In particular these group-only conclusions require no representation estimate.

Sources: Aschbacher–Smith K.3, printed p.457, the covering step in B.1.13,
printed pp.73–74, and I.1.1–I.1.3, printed p.407; GLS III §§2.2, 6.1;
Parrott (1972), §5, p.683. The natural-module and Tits-exclusion arguments
citing Guralnick–Malle remain separate representation results.
-/

public section

open Subgroup PerfectCentralCovering

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional

variable {L : Type*} [Group L] [Group.IsPerfect L]

/-- The kernel of the original G₂(2)′ covering projection vanishes in the
finite source group with trivial two-core. -/
theorem g2Derived_centralQuotientCover_ker_eq_bot [Finite L]
    (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    (centralQuotientCover e).toMonoidHom.ker = ⊥ := by
  apply bot_unique
  rw [← hcore]
  exact le_sSup ⟨inferInstance,
    BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup
      (centralQuotientCover e)⟩

/-- The same calculation removes the entire center of the supplied group. -/
theorem g2Derived_center_eq_bot [Finite L]
    (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) : center L = ⊥ := by
  simpa only [centralQuotientCover_ker] using
    g2Derived_centralQuotientCover_ker_eq_bot hcore e

/-- The original marked quotient map is an isomorphism to the literal
derived G₂(2) carrier; full G₂(2) is not substituted. -/
noncomputable def g2DerivedEquivOfTwoCoreEqBot [Finite L]
    (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    L ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  MulEquiv.ofBijective (centralQuotientCover e).toMonoidHom
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (g2Derived_centralQuotientCover_ker_eq_bot hcore e),
      (centralQuotientCover e).surjective⟩

@[simp] theorem g2DerivedEquivOfTwoCoreEqBot_apply [Finite L]
    (hcore : pCore 2 L = ⊥)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) (x : L) :
    g2DerivedEquivOfTwoCoreEqBot hcore e x = e (QuotientGroup.mk x) := by
  unfold g2DerivedEquivOfTwoCoreEqBot
  rfl

/-- Source recognition from the actual binary-derived central quotient,
with the covering-kernel premise discharged. -/
theorem g2Derived_recognition_of_twoCore_eq_bot [Finite L]
    (hcore : pCore 2 L = ⊥)
    (hmodel : Nonempty (L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨e⟩ := hmodel
  exact ⟨g2DerivedEquivOfTwoCoreEqBot hcore e⟩

/-- The Parrott lifting calculation removes the center of any perfect group
with the specified Tits central quotient. -/
theorem tits_center_eq_bot (e : L ⧸ center L ≃* Tits.ParrottGroup) : center L = ⊥ :=
  center_eq_bot_of_centralQuotientEquiv
    Tits.CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot e

/-- The Tits identification is the supplied central quotient projection,
with no remaining multiplier or relation-lifting hypothesis. -/
noncomputable def titsEquiv (e : L ⧸ center L ≃* Tits.ParrottGroup) :
    L ≃* Tits.ParrottGroup :=
  centralQuotientEquivOfUniversalKernelEqBot
    Tits.CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot e

@[simp] theorem titsEquiv_apply (e : L ⧸ center L ≃* Tits.ParrottGroup) (x : L) :
    titsEquiv e x = e (QuotientGroup.mk x) := by
  unfold titsEquiv
  exact centralQuotientEquivOfUniversalKernelEqBot_apply _ e x

/-- Source recognition from the literal Parrott central quotient. -/
theorem tits_recognition
    (hmodel : Nonempty (L ⧸ center L ≃* Tits.ParrottGroup)) :
    Nonempty (L ≃* Tits.ParrottGroup) :=
  tits_recognition_of_universalKernel
    Tits.CentralCoverLifting.CompatibleGenerators.universalProjection_ker_eq_bot hmodel

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional
