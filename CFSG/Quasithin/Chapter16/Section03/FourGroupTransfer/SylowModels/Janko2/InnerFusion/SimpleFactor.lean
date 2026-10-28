module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner.NoncentralChecks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.Orbit

/-!
# Fusion of the marked A₅ factor in the noncentral J₂ centralizer

Every involution among the sixty checked simple-factor words is one of the
315 already certified conjugates of `FirstFusion.t`. The small index table
below supplies the matching rows; the Lean kernel checks each equality on
all one hundred points. No new centralizer table or unverified group oracle
is used. The companion assembly uses perfectness to place actual component
elements in precisely this embedded factor.

Source: Aschbacher–Smith, proof of 16.3.4, printed p.1178 / PDF p.1195,
using 16.1.5(8), p.1172; retained ATLAS J2G1-p100B0 permutation words.
The adjacent `source/generate.py` reproduces the index witnesses.
-/

open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open J2Inner.NoncentralData
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels.J2InnerFusion

private def fusionIndex : Fin 60 → Fin 315 :=
  ![0, 304, 0, 0, 308, 314, 307, 0, 0, 24, 0, 0, 0, 0, 0, 0, 191, 313, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 309, 0, 0, 207, 0, 0, 0, 312, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 196, 0, 0, 0, 0, 283, 284, 0, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
private theorem fusion_check : ∀ i : Fin 60,
    simpleMul i i = 0 → i ≠ 0 → ∀ p : Fin 100,
      FirstFusion.OrbitData.value (fusionIndex i) p = conjugatorTable (simpleIndex i) p := by
  apply FirstFusion.allFin
  decide +kernel

/-- Each involution in the marked simple factor lies in the central J₂ class. -/
public theorem simple_involution_fusion (i : Fin 60) (hi : orderOf (simpleEquiv i) = 2) :
    IsConj FirstFusion.t (conjugator (simpleIndex i)) := by
  have hs : simpleMul i i = 0 := by
    apply simpleEquiv.injective
    change simpleEnum (simpleMul i i) = simpleEnum 0
    rw [simpleEnum_mul, simpleEnum_zero, ← pow_two]
    exact hi ▸ pow_orderOf_eq_one (simpleEquiv i)
  have hn : i ≠ 0 := by
    rintro rfl
    change orderOf (simpleEnum 0) = 2 at hi
    rw [simpleEnum_zero, orderOf_one] at hi
    contradiction
  apply isConj_iff.mpr
  refine ⟨(FirstFusion.rep (fusionIndex i))⁻¹, ?_⟩
  rw [inv_inv]
  apply inclusion_injective
  apply Equiv.ext
  intro p
  rw [FirstFusion.row_spec, conjugator_inclusion]
  exact fusion_check i hs hn p

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels.J2InnerFusion
