module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.EndpointSections
public import Theory.Representation.BinaryOffender.SylowGeneratedKernel
public import Theory.Representation.BinaryConjugationSection.Projection

/-!
# Faithful Sylow action on the actual endpoint quotient

Construct the full Z action and its literal projection to Z/Ω₁(Z(L)).
The projection kernel is central. Sylow fixed-space generation makes its
faithful image two-reduced, so the central quotient has no additional
kernel. The critical centralizer theorem then detects every Sylow image
in the original L/Q. This proves Sylow faithfulness without assuming an
SL₂ model, natural coordinates or a distance bound.

Source: DGS, *Groups and Graphs* (1985), (7.1), printed pp.126–127,
using (3.8), (6.2), and the corrected generation hypothesis of (5.12).
`EndpointSource` applies the construction to the reduced F1.11 graph.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

/-- Every Sylow image acts faithfully on the literal central endpoint quotient. -/
theorem graph_critical_endpoint_section_sylow_kernel
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (E : Subgroup G) (c : LocalRankOneData (stabilizer (family P) v) E)
    (hodd : ¬ 2 ∣ c.Pstar.relIndex (stabilizer (family P) v))
    [((Q (family P) v).subgroupOf c.Pstar).Normal]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (c.Pstar ⧸ (Q (family P) v).subgroupOf c.Pstar) W)
    (s : BinaryConjugationSection c.Pstar (Z (family P) v)
      (Stellmacher.omegaOneCenterAmbient c.Pstar)
      (σ.comp (QuotientGroup.mk' ((Q (family P) v).subgroupOf c.Pstar))))
    (T : Sylow 2 c.Pstar) :
    Disjoint σ.ker ((T : Subgroup c.Pstar).map
      (QuotientGroup.mk' ((Q (family P) v).subgroupOf c.Pstar))) := by
  let := finite_endpoints h
  let := graph_Z_elementary h v
  let : Finite c.Pstar := Finite.of_injective (inclusion c.Pstar_le) (inclusion_injective _)
  let π := QuotientGroup.mk' ((Q (family P) v).subgroupOf c.Pstar)
  let S := T.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  obtain ⟨ρ,r,_⟩ := graph_endpoint_full_action_exists h v E c hodd
  have hgen : GeneratedByFixedSpace ρ S :=
    sylow_span_fixedSpace_generated c.Pstar _ _ ρ π r T (local_center_span _ _ c hodd)
  obtain ⟨f,_,_,hf⟩ := exists_projection c.Pstar c.Pstar (Z (family P) v) ⊥
    (Stellmacher.omegaOneCenterAmbient c.Pstar) le_rfl bot_le π π
    (QuotientGroup.mk'_surjective _) (MonoidHom.id _) (fun _ => rfl) ρ σ r s
  have hcentral : ⁅c.Pstar,Stellmacher.omegaOneCenterAmbient c.Pstar⁆ = ⊥ := by
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hz l hl
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz |>.2.2 l hl
  have hk : f.toLinearMap.ker ≤ fixedSpace ρ ⊤ := by
    rw [hf]
    intro z hz a
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective ((Q (family P) v).subgroupOf c.Pstar) a.val
    change ρ a.val z = z
    rw [←hl]
    exact r.fixed_on_imageSpace_of_commutator_le c.Pstar _ hcentral.le l l.property z hz
  have hker : σ.ker ≤ ρ.ker := kernel_le_of_central_quotient_sylow_fixed_generation ρ σ S
    hgen f.toLinearMap hk (fun g z => f.isIntertwining' g |> (fun he => LinearMap.congr_fun he z))
  exact (graph_critical_full_action_sylow_kernel h hB hS hc c.Pstar_le ρ r T).mono_left hker

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
