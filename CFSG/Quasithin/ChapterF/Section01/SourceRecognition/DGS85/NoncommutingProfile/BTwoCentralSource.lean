module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCentralD
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoNoncentralSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearEnlargement

/-!
# The central D calculation on the original marked source

A common full-vertex Sylow places Omega(Z(L_alpha)) in Z_beta.
Centrality of Z_beta therefore makes this subgroup normal in both local
actors, and faithful edge generation kills it. The marked natural center
action now constructs the opposite geometry and proves D elementary.

The original F1.11 application preserves D as the intersection of the
original beta-core with the image of its chosen conjugate. Its normalizer
is the actual enlarged alpha endpoint, with the full Borel retained.
The center-family application also discharges centrality using the proved
characteristic-two noncentral exclusion. Earlier 6.5 and Chapter 7 actions
remain inputs of the existing source producers.
Source: DGS, *Groups and Graphs* (1985), 10.2, 10.4, and the opening of
10.7, printed pp.154--159. The exhaustive 10.9/10.10 alternatives remain
separate obligations of the Chapter 10 assembly.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- A center central in its intrinsic local actor lies in every adjacent
center span, through the same common full-vertex Sylow. -/
theorem center_le_of_central_neighbor (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v m : Vertex (family P)} (hm : (graph (family P)).Adj v m)
    (hc : Z (family P) m ≤ centerIn (graphLocalGroup (family P) m)) :
    Z (family P) m ≤ Z (family P) v := by
  let := finite_endpoints h
  obtain ⟨T,R,hTR⟩ := source_common_edge_sylow h hB hSyl hm
  apply le_trans _ (le_iSup (fun A : Sylow 2 (stabilizer (family P) v) =>
    omegaCenterIn ((A : Subgroup (stabilizer (family P) v)).map
      (stabilizer (family P) v).subtype)) T)
  rw [hTR]
  intro x hx
  obtain ⟨hxQ,_,hp⟩ := (mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h m).1 hx)
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨pCoreIn_le_sylow _ R hxQ,
      centralizer_le (sylow_le_sylowGenerated _ R) (hc hx).2,hp⟩

/-- The source central neighbor kills the earlier natural action's central
kernel. No trivial-center conclusion is assumed. -/
theorem BTwoCenterActionData.omega_eq_bot_of_central_neighbor
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v m w : Vertex (family P)} (c : BTwoCenterActionData (family P) v m w k W)
    (hactor : c.actor = graphLocalGroup (family P) v)
    (hcentral : Z (family P) m ≤ centerIn (graphLocalGroup (family P) m)) :
    omegaCenterIn c.actor = ⊥ := by
  let := finite_endpoints h
  let F := family P
  let O := omegaCenterIn c.actor
  let M := graphLocalGroup F m
  let E := stabilizer F v ⊓ stabilizer F m
  obtain ⟨T,R,hTR⟩ := source_common_edge_sylow h hB hSyl c.middle
  have hZQ : Z F v ≤ Q F v := fun x hx =>
    ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hx)).1
  have hOS : O ≤ (T : Subgroup (stabilizer F v)).map (stabilizer F v).subtype :=
    c.coordinates.kernel_le.trans (hZQ.trans (pCoreIn_le_sylow _ T))
  have hSL : (T : Subgroup (stabilizer F v)).map (stabilizer F v).subtype ≤ c.actor := by
    rw [hactor]
    exact sylow_le_sylowGenerated _ _
  have hOZ : O ≤ Z F m := by
    apply le_trans _ (le_iSup (fun A : Sylow 2 (stabilizer F m) =>
      omegaCenterIn ((A : Subgroup (stabilizer F m)).map (stabilizer F m).subtype)) R)
    intro x hx
    obtain ⟨_,hc,hp⟩ := (mem_omegaCenterIn_iff _ _).mp hx
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨hTR ▸ hOS hx,centralizer_le (hTR ▸ hSL) hc,hp⟩
  have hOE : O ≤ E := le_inf (hOS.trans (map_subtype_le _))
    (hOZ.trans (Z_le_stabilizer F m))
  apply graph_local_common_normal_eq_bot h c.middle c.actor M O c.factor
  · intro a ha
    have he : M ⊔ E = stabilizer F m := by
      simpa only [M,E,inf_comm] using graphLocalGroup_sup_edge h hB hSyl c.middle.symm
    have hx : a ∈ (M : Set G) * (E : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left M E
        (inf_le_right.trans (sylowGenerated_normalized _)),he]
      exact ha
    obtain ⟨l,hl,b,hb,hab⟩ := hx
    exact ⟨l,hl,b,hb,hab.symm⟩
  · exact hOE
  · apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    intro x hx
    exact ((mem_omegaCenterIn_iff _ _).mp hx).2.1
  · apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
    exact fun x hx => (hcentral (hOZ hx)).2

namespace Reduction
open DGS85.Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- The central branch gives a literal elementary D in the original
completion, normal in its actual enlarged local actor. -/
theorem original_bTwo_central_D_structure (h : HypothesisF11 L S)
    (hb : b F = 2) {u t : Vertex F}
    (c : BTwoCenterActionData F α β u k W)
    (hactor : c.actor = graphLocalGroup F α)
    (hcentral : Z F β ≤ centerIn (graphLocalGroup F β))
    (ht : (graph F).Adj α t) (hne : t ≠ β) :
    ∃ g : c.actor, (g : G₀ L S) • β = t ∧
      let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map (G₀ L S).subtype
      let R₀ := (centralResidual F β t u ((g : G₀ L S) • u)).map (G₀ L S).subtype
      D₀ ≤ (parabolic L S 0).pCoreIn 2 ∧
      enlargedEndpoint L S 0 ≤ normalizer (D₀ : Set G) ∧
      IsElementaryAbelian 2 D₀ ∧
      D₀ = (Z F α).map (G₀ L S).subtype ⊔ R₀ ∧
      Disjoint R₀ ((Z F α).map (G₀ L S).subtype) := by
  have hω := c.omega_eq_bot_of_central_neighbor (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hactor hcentral
  obtain ⟨g,hg,hD,hn,he,hspan,hdis,_⟩ := c.central_D_structure
    (reduced_triple h) (reduced_kernel_sylow h) hb hω ht hne
  change D F β t ≤ Q F α at hD
  change c.actor ≤ normalizer (D F β t : Set (G₀ L S)) at hn
  change IsElementaryAbelian 2 (D F β t) at he
  change D F β t = Z F α ⊔ centralResidual F β t u ((g : G₀ L S) • u) at hspan
  have hDm : (D F β t).map (G₀ L S).subtype =
      (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map (G₀ L S).subtype := by
    change ((Q F β ⊓ Q F t).map _) = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hAm : c.actor.map (G₀ L S).subtype = enlargedEndpoint L S 0 := by
    rw [hactor,reduced_graphLocalGroup_image h false]
    rfl
  refine ⟨g,hg,?_,?_,?_,?_,?_⟩
  · have hh := map_mono (f := (G₀ L S).subtype) hD
    rwa [hDm,reduced_base_Q_map h false] at hh
  · rw [←hAm,←hDm]
    exact (map_mono hn).trans (le_normalizer_map (G₀ L S).subtype)
  · rw [←hDm]
    let := he
    exact IsElementaryAbelian.map _
  · have hh := congrArg (map (G₀ L S).subtype) hspan
    rwa [hDm,Subgroup.map_sup] at hh
  · exact Subgroup.disjoint_map (G₀ L S).subtype_injective hdis

variable {k₁ W₁ : Type*} [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The original center-family application discharges the central-branch
premise by the characteristic-two exclusion. The literal D is elementary
and relatively normal, without assuming any conclusion of 10.4 or 10.7. -/
theorem original_bTwo_D_elementary_of_center_family
    (h : HypothesisF11 L S) (hb : b F = 2) {u t : Vertex F}
    (c : BTwoCenterActionData F α β u k W)
    (hactor : c.actor = graphLocalGroup F α)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hnot : ∀ y, (graph F).Adj y α →
      ¬ stabilizer F α ≤ normalizer ((Q F y ⊓ Q F α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hcenters : ∀ y, (graph F).Adj y α → IsCriticalPair F β y →
      ⁅Z F β,Z F y⁆ ≠ ⊥ → Nonempty (BTwoCenterActionData F β α y k₁ W₁))
    (ht : (graph F).Adj α t) (htne : t ≠ β) :
    let D₀ := (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map (G₀ L S).subtype
    D₀ ≤ (parabolic L S 0).pCoreIn 2 ∧
      enlargedEndpoint L S 0 ≤ normalizer (D₀ : Set G) ∧
      IsElementaryAbelian 2 D₀ ∧ (Z F α).map (G₀ L S).subtype ≤ D₀ := by
  have hcentral := original_bTwo_center_central_of_center_family h hb c E E₁ hc hne hnot hcenters
  obtain ⟨g,_,hD,hn,he,hspan,_⟩ := original_bTwo_central_D_structure h hb c hactor hcentral ht htne
  exact ⟨hD,hn,he,hspan ▸ le_sup_left⟩

end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
