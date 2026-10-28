module
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover.NormalizerGeneration
public import Stellmacher.ElementaryAbelianMaxPair.PlaneChoice
/-! # An escaping root-plane normalizer on the actual linear Sylow
The two parabolics generate PSL₃. Aligning the supplied component Sylow with
the standard unipotent subgroup therefore selects an intrinsic maximum plane
whose component normalizer escapes M. All full plane lifts are the literal
preimages of the supplied cover. Source: Aschbacher--Smith 2.5.7, p.556.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3Even.ThompsonCentralCover
open UnipotentGeometry PSL3.LinearThree PSL3.RootPlaneGeometry
variable {G F:Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
omit [Finite F] [CharP F 2] in
private theorem rootPlane_as_projective (b:Bool) :
    rootPlane F b=(if b then V₁ F else V₂ F).map (projective F) := by
  rw [rootPlane,rootPlaneSL,Subgroup.map_map]
  rfl
omit [Finite F] in
private theorem elementary_rootPlane_cover (A:Subgroup PSL(3,F)) [IsElementaryAbelian 2 A]
    (hAU:A≤unipotent F) : A≤rootPlane F true ∨ A≤rootPlane F false := by
  let B:Subgroup (U F):=(A.subgroupOf (unipotent F)).map (unipotentEquiv F).symm.toMonoidHom
  let : IsElementaryAbelian 2 (A.subgroupOf (unipotent F)):=IsElementaryAbelian.subgroupOf hAU
  let : IsElementaryAbelian 2 B:=IsElementaryAbelian.map _
  have hle (V:Subgroup (U F)) (hB:B≤V) : A≤V.map (projective F):=by
    intro a ha
    let u:unipotent F:=⟨a,hAU ha⟩
    refine ⟨(unipotentEquiv F).symm u,hB (mem_map_of_mem _ (show u∈A.subgroupOf (unipotent F) from ha)),?_⟩
    change ((unipotentEquiv F) ((unipotentEquiv F).symm u):PSL(3,F))=a
    rw [MulEquiv.apply_symm_apply]
  simpa only [rootPlane_as_projective, Bool.true_eq_false, Bool.false_eq_true, if_true, if_false] using
    (elementary_le_plane F B).imp (hle (V₁ F)) (hle (V₂ F))

theorem exists_maximum_escaping_normalizer_of_sylow
    (K M:Subgroup G) (hKM:¬K≤M) (q:K→*PSL(3,F)) (hq:Function.Surjective q)
    (hk:IsPGroup 2 q.ker) (P:Sylow 2 K)
    {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap q)) :
    ∃V∈Stellmacher.elementaryAbelianMaxSubgroups ((P:Subgroup K).map K.subtype),
      ¬K⊓normalizer (V:Set G)≤M := by
  have hplane (b:Bool):IsElementaryAbelian 2 (rootPlane F b):=by
    rw [rootPlane_as_projective]
    cases b
    · exact IsElementaryAbelian.map (projective F) (A:=V₂ F)
    · exact IsElementaryAbelian.map (projective F) (A:=V₁ F)
  let :=hplane true
  let :=hplane false
  have hc (b:Bool):Nat.card (rootPlane F b)=Nat.card F^2:=by
    rw [rootPlane_as_projective,card_map_of_injective (projective_injective F)]
    cases b
    · exact card_V₂ F
    · exact card_V₁ F
  apply Stellmacher.exists_maximum_escaping_normalizer_of_sylow_planes K M hKM q hq hk P
    (unipotentSylow F hn hF) (rootPlane F true) (rootPlane F false)
    (map_mono (rootPlaneSL_le_unipotent F true)) (map_mono (rootPlaneSL_le_unipotent F false))
    hlift ((hc true).trans (hc false).symm)
  · intro A hA hAU
    let :=hA
    exact elementary_rootPlane_cover A hAU
  · rw [normalizer_rootPlane,normalizer_rootPlane]
    exact parabolics_sup_eq_top F
end Matrix.PSL3Even.ThompsonCentralCover
