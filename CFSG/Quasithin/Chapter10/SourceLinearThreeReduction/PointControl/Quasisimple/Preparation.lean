module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Contracts
public import CFSG.Quasithin.Chapter10.SourceA5PointAllLocalData
public import CFSG.Quasithin.Chapter10.SourceA5PointMovedImage

/-!
# The literal central quotient in the non-A₅ quasisimple point branch

Restrict the prescribed full point Sylow to the containing component and
then map it through I/Z(I). The original local component remains proper
and is not quasisimple; its moved subgroup remains nonzero, elementary,
and fully moved. Both the local component and the restricted Sylow
normalize that same image. The moved normalizer also controls the
original component normalizer inside I.

These data prepare the actual A.3.12 embedding inspection. They do not
assume an irreducible moved quotient or discard any Theorem C carrier.
Source: Aschbacher--Smith, 10.2.9, printed pp.750--751.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02 ChapterA.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The opposite moved factor acts on the literal containing component. -/
theorem partner_normalizes :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ normalizer (I : Set G) := by
  let := source_original_full_moved_elementary D
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  apply le_trans (show U ≤ centralizer ({v} : Set G) from ?_) c.normalizes
  intro u hu y hy
  have he : y = v := Set.mem_singleton_iff.mp hy
  rw [he]
  exact U.le_centralizer hu v c.v_mem

/-- The source's extra normalizer restriction is available on the original
subgroups inside I, without an A₅ quotient or irreducibility hypothesis. -/
theorem moved_normalizer_le_component_normalizer :
    normalizer ((⁅D.fullModule,L⁆).subgroupOf I : Set I) ≤
      normalizer (L.subgroupOf I : Set I) := by
  rw [←subgroupOf_normalizer_eq ((source_full_moved_le_component D).trans c.strict.le),
    ←subgroupOf_normalizer_eq c.strict.le]
  apply comap_mono
  exact (le_inf c.moved_normalizer le_rfl).trans
    (source_original_moved_stabilizer_le_component_normalizer D
      c.t_mem c.t_not_normalizes c.crossed)

/-- A central quotient cannot turn the original component into a quasisimple
one: its nonzero fully moved elementary subgroup precludes that. -/
theorem center_image_not_quasisimple :
    ¬ IsQuasisimple ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) := by
  let A := L.subgroupOf I
  let q := QuotientGroup.mk' (center I)
  let k : L ≃* A := (subgroupOfEquivOfLe c.strict.le).symm
  let f := (q.subgroupMap A).comp k.toMonoidHom
  apply source_central_image_not_quasisimple D f
    ((q.subgroupMap_surjective A).comp k.surjective)
  intro l hl
  have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
  change q (inclusion c.strict.le l) = 1 at hh
  have hc := (QuotientGroup.eq_one_iff (inclusion c.strict.le l)).mp hh
  apply mem_center_iff.mpr
  intro m
  exact Subtype.ext (congrArg I.subtype (mem_center_iff.mp hc (inclusion c.strict.le m)))

/-- The moved subgroup does not disappear on passage through Z(I). -/
theorem center_moved_ne_bot :
    ((⁅D.fullModule,L⁆).subgroupOf I).map (QuotientGroup.mk' (center I)) ≠ ⊥ := by
  intro he
  have hk := (map_eq_bot_iff ((⁅D.fullModule,L⁆).subgroupOf I)).mp he
  rw [QuotientGroup.ker_mk'] at hk
  have hc : ⁅D.fullModule,L⁆ ≤ centralizer (L : Set G) := by
    intro w hw l hl
    let wI : I := ⟨w,(source_full_moved_le_component D).trans c.strict.le hw⟩
    let lI : I := ⟨l,c.strict.le hl⟩
    have hz : wI ∈ center I := hk hw
    exact congrArg I.subtype (mem_center_iff.mp hz lI)
  have hz := commutator_eq_bot_iff_le_centralizer.mpr hc
  rw [source_full_moved_eq_commutator D] at hz
  exact source_full_moved_ne_bot D hz

/-- The actual full point Sylow and both literal central-quotient images,
with every model-free hypothesis needed for the embedding inspection. -/
theorem center_quotient_data [Group.IsPerfect I] :
    let q := QuotientGroup.mk' (center I)
    let B := (L.subgroupOf I).map q
    let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
    ∃ S : Sylow 2 I,
      (S : Subgroup I).map I.subtype =
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ⊓ I ∧
      B ∈ localCComponents (S.mapSurjective (QuotientGroup.mk'_surjective (center I))) ∧
      (S.mapSurjective (QuotientGroup.mk'_surjective (center I)) : Subgroup (I ⧸ center I)) ≤
        normalizer (B : Set (I ⧸ center I)) ∧
      (S.mapSurjective (QuotientGroup.mk'_surjective (center I)) : Subgroup (I ⧸ center I)) ≤
        normalizer (E : Set (I ⧸ center I)) ∧
      B ≠ ⊤ ∧ ¬ IsQuasisimple B ∧ IsElementaryAbelian 2 E ∧
      E ≤ B ∧ E ≠ ⊥ ∧ ⁅E,B⁆ = E := by
  obtain ⟨S,hSm,hSN,hlocal⟩ := source_point_containing_component_local_sylow_of_normalizes
    D c.sylow_normalizes c.sylow c.strict.le c.le_centralizer c.component
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map q
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    exact Group.isSolvable_of_comm fun x y => mul_comm x y
  let := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 ((⁅D.fullModule,L⁆).subgroupOf I) :=
    IsElementaryAbelian.subgroupOf ((source_full_moved_le_component D).trans c.strict.le)
  refine ⟨S,hSm,Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal q,
    (map_mono hSN).trans (le_normalizer_map q),
    source_a5_point_center_moved_normalized_of_normalizes D c.sylow_normalizes
      c.strict.le S hSm,?_,center_image_not_quasisimple D c,
    IsElementaryAbelian.map q,map_mono (comap_mono (source_full_moved_le_component D)),
    center_moved_ne_bot D c,source_a5_containing_center_moved_commutator D c.strict.le⟩
  intro he
  have hh : (⊤ : Subgroup I) ≤ L.subgroupOf I :=
    perfect_le_of_map_le_of_central_kernel q (by rw [QuotientGroup.ker_mk'])
      ⊤ (L.subgroupOf I) (by rw [he]; exact le_top)
  exact c.strict.ne (le_antisymm c.strict.le (subgroupOf_eq_top.mp (top_unique hh)))

/-- Keep the full checked carrier catalogue until a source row has actually
been excluded using the original embedding and module. -/
theorem center_quotient_model [IsQuasisimple I] :
    ChapterA.Section02.IsTheoremCModel (I ⧸ center I) :=
  source_a5_point_center_quotient_theoremC_model D t c.v_mem c.v_ne c.le_centralizer

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
