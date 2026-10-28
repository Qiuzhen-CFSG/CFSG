module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.ChiefBounds.Transfer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.ChiefBounds.HSNative.Model
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# The HS chief-factor bound in the original sporadic source case

The concrete HS carrier is centerless. A two-central inner automorphism
therefore comes from an actual two-central involution. Genuine involution
fusion identifies its fixed subgroup with the marked centralizer, and the
same group isomorphism identifies their two-residuals. The native model
bound then applies to every complete chief series.

The supplied marking of `J/O₂(J)` and the central-cover transfer carry this
bound to the original `K` of 14.7.68(2). No order assumption on the center
of an upstairs cover is used. The separate lower bound on K's chief count
belongs to the source assembly.

Source: Aschbacher–Smith 14.7.68(2), printed p.1071 / PDF p.1088,
and 1.1.5(3)(f), printed pp.502–503; GLS3 Table 5.3m.
-/

public section
noncomputable section
open Subgroup NoncentralChiefRefinement
open scoped commutatorElement
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SporadicSieve.HSNative

open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner

private theorem fixed_equiv_local (β : MulAut Carrier) (hβ : TwoCentralInner β) :
    Nonempty (β.fixedSubgroup ≃* localGroup 0) := by
  obtain ⟨P, hP⟩ := hβ.2.2
  obtain ⟨x, hx, hx2, he⟩ := MulAut.inner_involution_fixing_sylow_center
    Sporadic.LeechRelated.HS.BlockNormalizer.center_carrier_eq_bot P β hβ.2.1
    (by obtain ⟨g, hg⟩ := hβ.1; exact ⟨g, hg.symm⟩) (fun y hy => hP ⟨y,hy⟩)
  have hxc : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral (x : Carrier) :=
    ⟨P, x.property, hx⟩
  obtain ⟨e⟩ := fixed_equiv_centralizer_of_isConj ((twoCentral_iff_isConj_e0 _ hx2).mp hxc)
  rw [he]
  exact ⟨e.trans (MulEquiv.subgroupCongr localGroup_zero_eq_centralizer.symm)⟩

private theorem fixedResidual_equiv_modelResidual (β : MulAut Carrier) (hβ : TwoCentralInner β) :
    Nonempty (pResidual 2 β.fixedSubgroup ≃* modelResidual) := by
  obtain ⟨e⟩ := fixed_equiv_local β hβ
  exact ⟨((pResidual 2 β.fixedSubgroup).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr ((map_pResidual 2 e).trans model_pResidual_eq))⟩

/-- The native HS bound for every genuine two-central inner automorphism.
The fixed subgroup is transported by involution fusion, then its literal
two-residual is identified with the alternating preimage. -/
theorem noncentralTwoCount_le (β : MulAut CFSG.Quasithin.ClassificationModels.SporadicName.hs.Carrier)
    (hβ : TwoCentralInner β) (s : ChiefSeries (pResidual 2 β.fixedSubgroup))
    (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) : s.noncentralTwoCount ≤ 1 := by
  obtain ⟨e⟩ := fixedResidual_equiv_modelResidual β hβ
  obtain ⟨ht0, ht1⟩ := s.mapActor_complete e hs0 hs1
  calc
    s.noncentralTwoCount = (s.mapActor e).noncentralTwoCount :=
      (s.mapActor_noncentralTwoCount e).symm
    _ ≤ 1 := modelResidual_noncentralTwoCount_le (s.mapActor e) ht0 ht1

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SporadicSieve.HSNative

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open Chapter12.Section08 Chapter15.Section03.Candidates.ComponentStructure
open ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
/-- In the genuine HS branch of 14.7.68(2), the original K has at most
one noncentral two-chief factor, using the supplied marking of J/O₂(J). -/
theorem fixedHS_noncentralTwoCount_le
    (d : Data T L V F W) (u : F.U) {Lu : Subgroup G}
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u)))
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* SporadicName.hs.Carrier)
    (h : SporadicSieve.Case d u Lu α .hs)
    (s : ChiefSeries (K F)) (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 :=
  d.fixedSporadic_noncentralTwoCount_le_of_native u α e h 1
    SporadicSieve.HSNative.noncentralTwoCount_le s hs0 hs1
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
