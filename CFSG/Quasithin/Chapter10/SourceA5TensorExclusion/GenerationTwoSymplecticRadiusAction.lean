module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRadius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.RadiusAction
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank

/-!
# The marked radius action and its original kernel

The original center-free setup removes the full central kernel from the
natural cover, yielding a bijective natural-module marking compatible with
the actual radius action. For critical distance greater than four the radius
is elementary abelian, so its symplectic image has order at most 64. The proved
radius order of at least 65536 then forces its kernel to have order at least
1024, including at the literal vertex two steps before a critical endpoint.

These are original-geometry inputs to MS93 (5.2), p.914. Neither the radius
displacement nor the final distance reduction is assumed or concluded here.
Source application: Aschbacher--Smith 9.3.10, p.734.
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

/-- A bijective natural marking with the literal restricted conjugation action. -/
theorem original_radius_natural_action
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (ha : color R a = false) (_hz : color R z = false)
      (hd : (cosetGraph R).dist a z + 2 ≤ geometry.b R),
    ∃ F : BinaryField, F.degree = 2 ∧
      ∃ f : V R a →* Sp F.Carrier,
        f.ker = (Q R z).subgroupOf (V R a) ∧
      ∃ π : U R z ≃* Multiplicative (Vector F.Carrier),
        ∀ (v : V R a) (u : U R z),
          π ⟨v.val*u.val*v.val⁻¹,
            (mem_normalizer_iff.mp (U_normalized z
              (radius_le_stabilizer_of_distance R geometry ha hd v.property)) u.val).mp u.property⟩ =
            Multiplicative.ofAdd (f v • (π u).toAdd) := by
  intro R geometry a z ha hz hd
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
  obtain ⟨F,hF,f,hf,π,hπ,hπker,hact⟩ := original_radius_inner_action R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq geometry hpos ha hz hd
  have hinj : Function.Injective π := by
    apply (MonoidHom.ker_eq_bot_iff π).mp
    apply le_bot_iff.mp
    intro u hu
    have hfixed : u.val ∈ fixedCore R z := ⟨
      ((U_le_Z z).trans (geometry.omega_bound z hz
        (by rwa [geometry.distance_constant z hz])) |>.trans (omegaCenter_le _)) u.property,
      (hπker u).mp hu⟩
    rw [c.original_fixedCore_eq_bot z hz] at hfixed
    exact Subtype.ext (mem_bot.mp hfixed)
  exact ⟨F,hF,f,hf,MulEquiv.ofBijective π ⟨hinj,hπ⟩,hact⟩

/-- The elementary original radius has symplectic image order at most 64. -/
theorem original_radius_image_index_le_64
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R}, color R a = false → color R z = false →
        (cosetGraph R).dist a z + 2 ≤ geometry.b R →
          (Q R z).relIndex (V R a) ≤ 64 := by
  intro R geometry hb a z ha hz hd
  obtain ⟨F,hF,f,hf,_,_⟩ := c.original_radius_natural_action eK geometry ha hz hd
  let := V_elementary_of_four_lt R ha hb
  let : IsElementaryAbelian 2 f.range := IsElementaryAbelian.of_surjective f.rangeRestrict
    f.rangeRestrict_surjective
  have hFc : Nat.card F.Carrier = 2^2 := by rw [F.card_eq,hF]
  have hr := EvenTwoRank.rank hFc (by decide : 0 < 2)
  have hc := (primeRank_le_iff_elementary_card_le (Sp F.Carrier)).mp hr.le f.range inferInstance
  change ((Q R z).subgroupOf (V R a)).index ≤ 64
  rw [←hf,index_ker]
  exact hc

/-- The kernel inside the original radius has at least 1024 elements. -/
theorem original_radius_kernel_card_ge_1024
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R}, color R a = false → color R z = false →
        (cosetGraph R).dist a z + 2 ≤ geometry.b R →
          1024 ≤ Nat.card (V R a ⊓ Q R z : Subgroup (FreeAmalgam R)) := by
  intro R geometry hb a z ha hz hd
  have hi := c.original_radius_image_index_le_64 eK geometry hb ha hz hd
  have hc := c.original_radius_card_ge_65536 eK geometry a ha
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (V R a ⊓ Q R z) (V R a) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at hm
  change (Q R z).relIndex (V R a) ≤ 64 at hi
  change 65536 ≤ Nat.card (V R a) at hc
  nlinarith

/-- Apply the kernel bound at the literal truncated critical endpoint. -/
theorem original_truncated_radius_kernel_card_ge_1024
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
        1024 ≤ Nat.card (V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) :
          Subgroup (FreeAmalgam R)) := by
  intro R geometry hb a z path
  have hb' : 4 < path.walk.length := by rw [path.length_eq_b]; exact hb
  have he : Even path.walk.length := by
    rw [path.shortest,path.critical.1]
    exact geometry.even a path.start_color
  have hz : color R (path.walk.getVert (path.walk.length-2)) = false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at he ⊢
    omega
  apply c.original_radius_kernel_card_ge_1024 eK geometry hb path.start_color hz
  rw [path.dist_start (Nat.sub_le _ _),Nat.sub_add_cancel (by omega : 2 ≤ path.walk.length)]
  exact path.length_eq_b.le
/-- The truncated kernel cannot be absorbed by the original natural seed. -/
theorem original_truncated_radius_kernel_not_le_Z
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
        ¬ V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) ≤ Z R a := by
  intro R geometry hb a z path hle
  let := finite_Z R a
  have hcard := c.original_truncated_radius_kernel_card_ge_1024 eK geometry hb path
  have hbound := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  have hZ := c.original_Z_card eK a path.start_color
  change Nat.card (Z R a) = 256 at hZ
  rw [hZ] at hbound
  change 1024 ≤ Nat.card (V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) :
    Subgroup (FreeAmalgam R)) at hcard
  omega

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
