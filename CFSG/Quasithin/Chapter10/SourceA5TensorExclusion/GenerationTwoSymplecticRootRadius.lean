module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRadiusDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalCoreActor

/-!
# The original radius kernel in the critical-root branch

The kernel at the vertex two steps before a critical endpoint lies in the
endpoint stabilizer and in the starting two-core. Its action on the endpoint
natural module is therefore inner in the order-four critical branch. Original
center-freeness makes the natural marking bijective. The action kernel is
exactly the intersection with the endpoint two-core, not a replacement core.

For critical distance greater than four, the actor is elementary abelian;
its image has at most 64 elements and its kernel has at least 16 elements.
An endpoint image of order at most four supplies the radius displacement and
an actual overlapping backward critical path. A surviving displacement failure
therefore has an image strictly larger than four, retains both order-four
critical images and both X = Z identities, and has the stated double-kernel
bound. The source (5.7) selection for that branch and the large-distance and
distance-four exclusions remain open.
Source: MS93 (3.3), p.867, and (5.2), (5.7), pp.914,919;
Aschbacher--Smith 9.3.10, p.734.
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

/-- The literal truncated radius kernel, with its entire natural action and
its exact second kernel. Both critical images refer to the original path. -/
theorem original_truncated_radius_root_action
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) = 4 → (Q R a).relIndex (Z R z) = 4 →
      let Y := V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))
      ∃ F : BinaryField, F.degree = 2 ∧
        ∃ f : Y →* Sp F.Carrier,
          f.ker = (Q R z).subgroupOf Y ∧
          (∀ u : Y, (u : FreeAmalgam R) ∈ Z R a →
            Module.finrank F.Carrier (InvolutionTypes.movedSpace (f u)) ≤ 1) ∧
          ∃ π : U R z ≃* Multiplicative (Vector F.Carrier),
            ∀ (y : Y) (u : U R z),
              π ⟨y.val*u.val*y.val⁻¹,
                (mem_normalizer_iff.mp (U_normalized z
                  (truncated_radius_le_endpoint_stabilizer path
                    (le_trans (by decide : 2 ≤ 4) (c.original_geometry_four_le eK geometry))
                    y.property)) u.val).mp u.property⟩ =
                  Multiplicative.ofAdd (f y • (π u).toAdd) := by
  intro R geometry a z path ha4 hz4 Y
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
  have hpos : 0 < geometry.b R := lt_of_lt_of_le (by decide : 0 < 4)
    (c.original_geometry_four_le eK geometry)
  have hYQ : Y ≤ Q R a := inf_le_left.trans
    (geometry.V_le_Q (lt_of_lt_of_le (by decide : 2 < 4)
      (c.original_geometry_four_le eK geometry)) a path.start_color)
  have hYZ : Y ≤ stabilizer R z := truncated_radius_le_endpoint_stabilizer path
    (le_trans (by decide : 2 ≤ 4) (c.original_geometry_four_le eK geometry))
  obtain ⟨F,hF,f,hf,hroot,π,hπ,hπker,hact⟩ := original_core_actor_root_action R hms
    hodd.isPGroup hne hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hcard hBC hsq path hpos ha4 hz4 Y hYQ hYZ
  have hinj : Function.Injective π := by
    apply (MonoidHom.ker_eq_bot_iff π).mp
    apply le_bot_iff.mp
    intro u hu
    have hfixed : u.val ∈ fixedCore R z := ⟨
      ((U_le_Z z).trans (geometry.omega_bound z path.end_color
        (by rwa [geometry.distance_constant z path.end_color])) |>.trans (omegaCenter_le _)) u.property,
      (hπker u).mp hu⟩
    rw [c.original_fixedCore_eq_bot z path.end_color] at hfixed
    exact Subtype.ext (mem_bot.mp hfixed)
  exact ⟨F,hF,f,hf,hroot,MulEquiv.ofBijective π ⟨hinj,hπ⟩,hact⟩

/-- In the root branch, the original truncated kernel has at most 64
images at the critical endpoint. -/
theorem original_truncated_radius_endpoint_index_le_64
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
        (Q R z).relIndex (Z R a) = 4 → (Q R a).relIndex (Z R z) = 4 →
        (Q R z).relIndex (V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))) ≤ 64 := by
  intro R geometry hb a z path ha4 hz4
  obtain ⟨F,hF,f,hf,_,_,_⟩ := c.original_truncated_radius_root_action eK geometry path ha4 hz4
  let := V_elementary_of_four_lt R path.start_color hb
  let : IsElementaryAbelian 2 (V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) :
      Subgroup (FreeAmalgam R)) := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective f.rangeRestrict
    f.rangeRestrict_surjective
  have hFc : Nat.card F.Carrier = 2^2 := by rw [F.card_eq,hF]
  have hr := EvenTwoRank.rank hFc (by decide : 0 < 2)
  have hc := (primeRank_le_iff_elementary_card_le (Sp F.Carrier)).mp hr.le f.range inferInstance
  change ((Q R z).subgroupOf _).index ≤ 64
  rw [←hf,index_ker]
  exact hc

/-- Both literal kernels still have a nontrivial intersection of order at least
16; central extensions have not been discarded in the root action. -/
theorem original_truncated_radius_double_kernel_card_ge_16
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
        (Q R z).relIndex (Z R a) = 4 → (Q R a).relIndex (Z R z) = 4 →
        16 ≤ Nat.card ((V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))) ⊓ Q R z :
          Subgroup (FreeAmalgam R)) := by
  intro R geometry hb a z path ha4 hz4
  let Y := V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))
  have hi := c.original_truncated_radius_endpoint_index_le_64 eK geometry hb path ha4 hz4
  have hc := c.original_truncated_radius_kernel_card_ge_1024 eK geometry hb path
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) (Y ⊓ Q R z) Y
    bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at hm
  change (Q R z).relIndex Y ≤ 64 at hi
  change 1024 ≤ Nat.card Y at hc
  change 16 ≤ Nat.card (Y ⊓ Q R z : Subgroup (FreeAmalgam R))
  nlinarith

/-- A four-image bound at the critical endpoint supplies the original
radius displacement. The large critical-index branch was already discharged. -/
theorem original_radius_displacement_of_endpoint_index_le_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))) ≤ 4 →
      ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a := by
  intro R geometry a z path hsmall
  rcases c.original_radius_displacement_or_root eK geometry path with h | ⟨ha4,hz4,_,_⟩
  · exact h
  obtain ⟨F,_,f,hf,_,_,_⟩ := c.original_truncated_radius_root_action eK geometry path ha4 hz4
  let Y := V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have hYQ : Y ≤ Q R a := inf_le_left.trans (geometry.V_le_Q hb a path.start_color)
  have hZY : Z R a ≤ Y := by
    apply le_inf (Z_le_VBall R a 2)
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a path.start_color)
    rw [geometry.distance_constant a path.start_color,path.dist_start (Nat.sub_le _ _),
      path.length_eq_b]
    change geometry.b R - 2 < geometry.b R
    omega
  exact critical_displacement_of_root_image_bound path Y hYQ hZY f hf ha4 hsmall

/-- The original backward critical path now needs only a bound on the
literal endpoint image of the truncated radius kernel. -/
theorem original_backward_path_of_endpoint_index_le_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a t z : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t →
      (Q R z).relIndex (V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))) ≤ 4 →
      ∃ d t', Adjacent R a t' ∧ Adjacent R d t' ∧
        (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry a t z path hat hsmall
  exact c.original_backward_path_of_radius_displacement eK geometry path hat
    (c.original_radius_displacement_of_endpoint_index_le_four eK geometry path hsmall)

/-- Any surviving failure has a larger-than-root but at-most-64 endpoint
image, and retains at least sixteen elements in both original kernels. -/
theorem original_radius_displacement_or_root_kernel_obstruction
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      let Y := V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))
      ⁅Y,Z R z⁆ ≤ Z R a ∨
        ((Q R z).relIndex (Z R a) = 4 ∧ (Q R a).relIndex (Z R z) = 4 ∧
          X R a = Z R a ∧ X R z = Z R z ∧
          4 < (Q R z).relIndex Y ∧ (Q R z).relIndex Y ≤ 64 ∧
          16 ≤ Nat.card (Y ⊓ Q R z : Subgroup (FreeAmalgam R))) := by
  intro R geometry hb a z path Y
  by_cases hdisp : ⁅Y,Z R z⁆ ≤ Z R a
  · exact Or.inl hdisp
  obtain h | ⟨ha,hz,hXa,hXz⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact (hdisp h).elim
  refine Or.inr ⟨ha,hz,hXa,hXz,?_,
    c.original_truncated_radius_endpoint_index_le_64 eK geometry hb path ha hz,
    c.original_truncated_radius_double_kernel_card_ge_16 eK geometry hb path ha hz⟩
  exact Nat.lt_of_not_ge (fun h => hdisp
    (c.original_radius_displacement_of_endpoint_index_le_four eK geometry path h))

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
