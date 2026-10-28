module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalKernelCentralizer
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticKernelComparison

/-!
# Normalization of the original selected hyperplane kernel

The original truncated radius action gives an exact hyperplane-centralizer
identity for every escaping neighboring join that remains in the truncated
kernel. Its endpoint generator normalizes the selected centralizer joined
with the starting seed. The original escaping-neighbor alternative retains
this normalization together with the order-four root commutator and the
literal backward path.

The centralizer-index refinement is in GenerationTwoSymplecticSelectedKernel.
The remaining source generator and the large-distance and distance-four
exclusions still require their proofs. These results do not complete
SymplecticPlaneRecognition.
Source: MS93 (5.7), printed p.919; Aschbacher--Smith 9.3.10, p.734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- Exact centralizer saturation and endpoint normalization on the original
neighboring root branch. -/
theorem original_neighbor_hyperplane_centralizer
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ((Z R d ⊔ Z R a) ⊓ centralizer
        ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _) =
          Z R a ⊔ ((Z R d ⊔ Z R a) ⊓ Q R z)) ∧
      Z R z ≤ normalizer (((Z R d ⊓ centralizer
        ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) ⊔ Z R a :
          Subgroup (FreeAmalgam R)) : Set _) := by
  intro R geometry hb a z d t path hat hdt hcontained hbad
  let Y := Z R d ⊔ Z R a
  let Y₀ := V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))
  have hZa₀ : Z R a ≤ Y₀ := by
    apply le_inf (Z_le_VBall R a 2)
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a path.start_color)
    rw [geometry.distance_constant a path.start_color,path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hYV : Y ≤ V R a := ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt
  have hY₀ : Y ≤ Y₀ := le_inf hYV (sup_le hcontained (hZa₀.trans inf_le_right))
  have hYZ := hY₀.trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hn : ¬ ⁅Y₀,Z R z⁆ ≤ Z R a := by
    intro h
    apply hbad
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono hY₀ le_rfl).trans h).trans le_sup_right
  obtain h | ⟨ha4,hz4,_,_⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact (hn h).elim
  obtain ⟨F,hF,f,hf,hr,π,hπ⟩ := c.original_truncated_radius_root_action eK geometry path ha4 hz4
  let fY := f.comp (inclusion hY₀)
  have hfY : fY.ker = (Q R z).subgroupOf Y := by
    ext y
    change f (inclusion hY₀ y) = 1 ↔ y.val ∈ Q R z
    change inclusion hY₀ y ∈ f.ker ↔ _
    rw [hf]
    rfl
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hCa : C R a = Q R a := C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith a path.start_color
  have hcent := critical_root_hyperplane_centralizer path (by omega) hCa
    (c.original_Z_eq_U z path.end_color) Y le_sup_right hYZ fY hfY
    (fun y hy => hr (inclusion hY₀ y) hy) π (fun y u => hπ (inclusion hY₀ y) u)
    (by rw [F.card_eq,hF]; exact ha4)
  exact ⟨hcent,endpoint_normalizes_neighbor_centralizer path (by omega) hat hdt hcent⟩

/-- The escaping original neighbor supplies either the required overlapping
path or an exact root kernel already normalized by the endpoint generator. -/
theorem original_backward_path_or_normalized_neighbor_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a t z : Vertex R} (path : CriticalPath R geometry a z), Adjacent R a t →
      ∃ d t', Adjacent R a t' ∧ Adjacent R d t' ∧
        ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) ∧
        ((∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
        (Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) ∧
          ⁅Z R d,Z R z ⊓ Q R a⁆ = ⁅Z R a,Z R z⁆ ∧
          Nat.card (⁅Z R d,Z R z ⊓ Q R a⁆ : Subgroup (FreeAmalgam R))=4 ∧
          Z R z ≤ normalizer (((Z R d ⊓ centralizer
            ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) ⊔ Z R a :
              Subgroup (FreeAmalgam R)) : Set _))) := by
  intro R geometry hb a t z path hat
  obtain ⟨d,t',hat',hdt',hbad,hback | ⟨hkernel,hroot,hcard⟩⟩ :=
    c.original_backward_path_or_neighbor_root_commutator eK geometry hb path hat
  · exact ⟨d,t',hat',hdt',hbad,Or.inl hback⟩
  · exact ⟨d,t',hat',hdt',hbad,Or.inr ⟨hkernel,hroot,hcard,
      (c.original_neighbor_hyperplane_centralizer eK geometry hb path hat' hdt' hkernel hbad).2⟩⟩
end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
