module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticSelectedKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallMovers

/-!
# The canonical original small movers normalize the selected kernel

At distance greater than four, the original hyperplane-centralizer index is
at most four. The actual maximum-small-mover join J_d(T_t) therefore normalizes
C_(Z_d)(Z_z intersect Q_a), including its full central kernel. It also
normalizes Z_a, so the selected kernel join is normalized by this precise
source subgroup and by the already proved endpoint generator.

The backward-path consumer now requires only the source generation and strict
moving index, with no normalization callback. Those two claims, the remaining
paired selection, and the large-distance and distance-four exclusions remain
open; this does not complete SymplecticPlaneRecognition.

Source: MS93 (5.5)--(5.9), pp.915--922; Aschbacher--Smith9.3.10, p.734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- The canonical small-mover join at the neighboring vertex normalizes
the selected centralizer joined with the original starting seed. -/
theorem original_neighbor_small_movers_normalize_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      LocalPackage.J R d t ≤ normalizer (((Z R d ⊓ centralizer
        ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) ⊔ Z R a :
          Subgroup (FreeAmalgam R)) : Set _) := by
  intro R geometry hb a z d t path hat hdt hcontained hbad
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases he : color R d <;> simp_all
  let A := Z R z ⊓ Q R a
  have hfixed : U R d ⊓ centralizer (Ltilde R d : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R d := ⟨
      ((U_le_Z d).trans (geometry.omega_bound d hd
        (by
          rw [geometry.distance_constant d hd]
          change 0 < geometry.b R
          omega)) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot d hd] at hcore
  have hsmall : (centralizer (A : Set (FreeAmalgam R))).relIndex (U R d) ≤ 4 := by
    rw [←c.original_Z_eq_U d hd]
    exact c.original_neighbor_kernel_centralizer_index eK geometry hb path hat hdt hcontained hbad
  have hQt : IsPGroup 2 (Q R t) := by
    obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le hd hdt
    rw [←hiT]
    exact hodd.isPGroup.map i
  have hJ := original_small_mover_join_normalizes_kernel R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq hd hfixed (Q R t) A hQt
    (fun _ hx => hx.2 d (adjacent_symm R hdt))
    (Q_le_adjacent_h R ht hdt) (inf_le_right.trans (Q_le_adjacent_h R ht hat)) hsmall
  change LocalPackage.J R d t ≤ normalizer
    ((U R d ⊓ centralizer (A : Set _) : Subgroup (FreeAmalgam R)) : Set _) at hJ
  rw [←c.original_Z_eq_U d hd] at hJ
  have hZa : LocalPackage.J R d t ≤ normalizer (Z R a : Set (FreeAmalgam R)) :=
    (LocalPackage.J_le_radical R d t).trans
      ((show Q R t ≤ stabilizer R a from fun _ hx => hx.2 a (adjacent_symm R hat)).trans
        (Z_normalized R a))
  exact (le_inf hJ hZa).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The actual small-mover generator supplies the selected normalization;
only its source generation and the strict moving index remain. -/
theorem original_small_movers_backward_path
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      Ltilde R a ≤ LocalPackage.J R d t ⊔ Z R z →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1=t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
      ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry hb a z d t path hat hdt hbad hgen hmove
  exact c.original_selected_generator_backward_path eK geometry hb path hat hdt hbad
    (LocalPackage.J R d t) hgen
    (fun hkernel => c.original_neighbor_small_movers_normalize_kernel eK geometry hb path
      hat hdt hkernel hbad) hmove
end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
