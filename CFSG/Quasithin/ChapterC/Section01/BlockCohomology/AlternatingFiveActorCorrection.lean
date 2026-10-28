module
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFivePairSplit

/-!
# Correcting actors fixing an A₅ block module

An automorphism fixing the natural block layer displaces the group into its
centralizer, which is the two-core. The genuine C.1.13 cocycle correction
therefore adjusts a normalizing actor by a block-module element to centralize
the whole block. The application retains that actor's quotient image.
Source: Aschbacher–Smith C.1.13(c) and E.2.3, used in10.2.1,p.743.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G]
/-- A block-module adjustment lifts a module centralizer to the full block centralizer. -/
theorem IsAlternatingBlock.exists_centralizing_correction
    {L : Subgroup G} (h : IsAlternatingBlock L 5)
    (g : G) (hg : g ∈ normalizer (L : Set G))
    (hfix : g ∈ centralizer ((blockU L).map L.subtype : Set G)) :
    ∃ u : blockU L, ((u : L) : G) * g ∈ centralizer (L : Set G) := by
  let α := L.normalizerMonoidHom ⟨g,hg⟩
  have hf (u : L) (hu : u ∈ blockU L) : α u = u := by
    apply Subtype.ext
    change g * (u : G) * g⁻¹ = (u : G)
    rw [←hfix u (mem_map_of_mem L.subtype hu),mul_inv_cancel_right]
  have hd (x : L) : α x * x⁻¹ ∈ pCore 2 L := by
    rw [←h.2.1.centralizer_blockU]
    intro v hv
    have hconj : x⁻¹ * v * x ∈ blockU L :=
      by simpa only [inv_inv] using (inferInstance : (blockU L).Normal).conj_mem v hv x⁻¹
    have hh := hf (x⁻¹*v*x) hconj
    simp only [map_mul,map_inv,hf v hv] at hh
    have hh' := congrArg (fun z : L => α x * z * x⁻¹) hh
    group at hh'
    simpa only [mul_assoc,zpow_neg_one] using hh'
  obtain ⟨u,hu⟩ := h.automorphism_inner_of_core_displacement α hd hf
  refine ⟨u,?_⟩
  intro x hx
  have hh := congrArg L.subtype (hu ⟨x,hx⟩)
  change g*x*g⁻¹ = ((u : L) : G)⁻¹*x*u at hh
  calc
    x * (((u : L) : G)*g) = u * (((u : L) : G)⁻¹*x*u) * g := by group
    _ = u * (g*x*g⁻¹) * g := by rw [←hh]
    _ = (((u : L) : G)*g)*x := by group
end CFSG.Quasithin.ChapterC
