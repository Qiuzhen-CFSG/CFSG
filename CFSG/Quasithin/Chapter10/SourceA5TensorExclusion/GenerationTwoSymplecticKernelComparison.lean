module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalKernelDisplacement
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRootRadius

/-!
# Original neighboring seeds and their critical-root commutator

At critical distance greater than four, take an original neighboring seed
whose join with Z_a is not normalized by the critical endpoint Z_z. If
that seed lies in the kernel two steps before z, the previously constructed
truncated radius action has both critical indices four. Its bijective
natural marking identifies Z_z ∩ Q_a with the critical hyperplane. The
quadratic hyperplane comparison gives the entire root commutator, and
abelian radius geometry removes the redundant starting-seed factor.
Thus [Z_d, Z_z ∩ Q_a] = [Z_a, Z_z] has order four, on the original geometry.

The actual escaping-neighbor construction now yields either an overlapping
backward critical path or this exact root equality. No displacement,
secondary action, or source-generator callback is assumed. The source
selected-pair kernel-index and normalization steps, the large-distance
exclusion and distance four remain to be proved; these results do not
complete SymplecticPlaneRecognition.

Source: MS93 (3.3)(ii), pp.866--867, and (5.7), p.919;
Aschbacher--Smith 9.3.10, p.734.
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

/-- Original source (3.3)(ii) for a neighboring seed that survives in the
truncated kernel: its commutator with the critical hyperplane is exactly
the original critical commutator, of order four. -/
theorem original_neighbor_kernel_commutator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ⁅Z R d,Z R z ⊓ Q R a⁆ = ⁅Z R a,Z R z⁆ ∧
        Nat.card (⁅Z R d,Z R z ⊓ Q R a⁆ : Subgroup (FreeAmalgam R)) = 4 := by
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
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
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
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  have hAn : Z R z ⊓ Q R a ≤ normalizer (Y : Set (FreeAmalgam R)) :=
    (inf_le_right.trans (Q_le_adjacent_h R ht hat)).trans
      (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hdt)
  have hh := critical_root_kernel_commutator path hb hCa (c.original_Z_eq_U z path.end_color)
    Y hYQ le_sup_right hYZ hYV fY hfY (fun y hy => hr (inclusion hY₀ y) hy)
    π (fun y u => hπ (inclusion hY₀ y) u) hAn hbad
  rw [F.card_eq,hF] at hh
  let A := Z R z ⊓ Q R a
  have hAnD : A ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    ((inf_le_right.trans (Q_le_adjacent_h R ht hat)).trans
      (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt))).trans
        (Z_normalized R d)
  have hcommV : ⁅Z R d,A⁆ ≤ V R a :=
    (le_normalizer_iff_commutator_le_left.mp hAnD).trans (le_sup_left.trans hYV)
  have hnorm : V R a ≤ normalizer ((⁅Z R d,A⁆ : Subgroup (FreeAmalgam R)) : Set _) :=
    ((le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt R path.start_color hb)).trans
      (centralizer_le hcommV)).trans (Subgroup.centralizer_le_normalizer _)
  have hZaA : ⁅Z R a,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_rfl inf_le_right).trans (geometry.centralizes a path.start_color).le)
  have hjoin : ⁅Y,A⁆ = ⁅Z R d,A⁆ := le_antisymm
    (commutator_sup_le_of_relative_normal (V R a) (Z R d) (Z R a) A ⁅Z R d,A⁆
      hnorm (le_sup_left.trans hYV) (Z_le_VBall R a 2) le_rfl (hZaA ▸ bot_le))
    (commutator_mono le_sup_left le_rfl)
  have hseed : ⁅Z R d,A⁆ = ⁅Z R a,Z R z⁆ := hjoin.symm.trans hh.1
  refine ⟨hseed,?_⟩
  rw [hseed]
  exact hh.2

/-- On the original geometry an escaping neighboring join either supplies the
backward critical path or has its actual endpoint-hyperplane commutator equal
to the critical root of order four. No source generator or displacement callback is assumed. -/
theorem original_backward_path_or_neighbor_root_commutator
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
          Nat.card (⁅Z R d,Z R z ⊓ Q R a⁆ : Subgroup (FreeAmalgam R))=4)) := by
  intro R geometry hb a t z path hat
  obtain ⟨d,hdt,_,g,hg,hbad⟩ := c.original_critical_neighbor_join_escape eK geometry path hat
  have hga : act R g a = a := hg
  have hatg : Adjacent R a (act R g t) := by
    rw [←hga]
    exact (adjacent_act_iff R g _ _).mpr hat
  have hdtg : Adjacent R (act R g d) (act R g t) := (adjacent_act_iff R g _ _).mpr hdt
  rw [Subgroup.map_sup,←Z_act R g d,←Z_act R g a,hga] at hbad
  refine ⟨act R g d,act R g t,hatg,hdtg,hbad,?_⟩
  by_cases h : Z R (act R g d) ≤ Q R (path.walk.getVert (path.walk.length-2))
  · exact Or.inr ⟨h,c.original_neighbor_kernel_commutator eK geometry hb path hatg hdtg h hbad⟩
  · exact Or.inl (ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
      geometry (by omega) path hatg hdtg h)
end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
