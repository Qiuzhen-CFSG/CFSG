module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Recognition.Sporadic.ChiefBounds.Transfer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.NativeChiefBound

/-!
# The native J₂ chief bound and its marked source application

The two native inner-involution centralizers have respectively at most one
and zero noncentral binary chief factors in their two-residuals. Apply this
intrinsic calculation to the action induced by the supplied, literal
`Lᵤ/O₂(Lᵤ) ≃ J₂` map. The central-cover transfer then bounds every complete
chief series of the original subgroup K.

This discharges the J₂ branch of the sporadic count comparison in the proof
of Aschbacher–Smith 14.7.68(2), printed p.1071 / PDF p.1088, with the
2-central inner action supplied by 1.1.5(3)(f), printed pp.502–503.
The independent count-greater-than-one witness and combined J₂/HS exclusion
remain with the parent source assembly.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter15.Section03.Candidates.ComponentStructure
open ClassificationModels

/-- Native bound on the actual catalogue carrier, for every complete chief series. -/
theorem SporadicSieve.j2_native_noncentralTwoCount_le_one
    (β : MulAut SporadicName.j2.Carrier) (hβ : TwoCentralInner β)
    (s : ChiefSeries (pResidual 2 β.fixedSubgroup))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : s.noncentralTwoCount ≤ 1 := by
  apply Sporadic.LeechRelated.J2.NativeChiefBound.inner_fixed_residual_count β hβ.2.1 ?_ s h0 h1
  obtain ⟨x, hx⟩ := hβ.1
  exact ⟨x, hx.symm⟩

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The J₂ native theorem bounds the literal original K through the marked
quotient map. No covering recognition or extra chief-count premise is used. -/
theorem Data.fixedJ2_noncentralTwoCount_le_one
    (d : Data T L V F W) (u : F.U) {Lu : Subgroup G}
    (α : MulAut (Lu.subgroupOf (d.fixedCentralizer u)))
    (h : SporadicSieve.Case d u Lu α .j2)
    (e : ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
      pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* SporadicName.j2.Carrier)
    (s : ChiefSeries (K F)) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 1 :=
  d.fixedSporadic_noncentralTwoCount_le_of_native u α e h 1
    SporadicSieve.j2_native_noncentralTwoCount_le_one s h0 h1

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
