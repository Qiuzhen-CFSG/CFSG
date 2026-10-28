module
public import CFSG.Quasithin.Chapter13.Section09.LocalGeometry.Core
public import Theory.SpecificGroups.SymmetricFourWreath.Core.Geometry
public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.Solvability

/-!
# The marked 13.9.6 data in the original centralizer quotient

The Sylow coordinate embedding induces an injective map into the literal
quotient C_G(z)/⟨z⟩. It carries the native maximum elementary subgroup and its
hyperplane-fixer geometry to the original marked Q. This constructs every
field of CoreData and discharges the coordinate premises of 13.9.8 normality
and solvability. The earlier PairData, its four-group closure facts, and
condition (E) remain the genuine preceding source inputs.

Source: Aschbacher–Smith 13.9.6–8, printed pp.971–972 (PDF pp.988–989).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath CentralizerStructure
variable {G : Type*} [Group G] [Finite G] {d : Configuration G} (m : Marking d)
variable (p : PairData d) (hz : p.z=m.z)

private def sourceSylowHom : P→*p.C := m.sylowModelEmbedding.codRestrict p.C (by
  intro x
  change m.sylowModelEmbedding x∈centralizer ({p.z}:Set G)
  rw [hz]
  apply m.z_central_sylow
  rw [←m.range_sylowModelEmbedding]
  exact ⟨x,rfl⟩)

private def sourceProjection : P→*p.Tilde :=
  (QuotientGroup.mk' (p.Z.subgroupOf p.C)).comp (m.sourceSylowHom p hz)

private theorem sourceProjection_ker : (m.sourceProjection p hz).ker=centralLine := by
  ext x
  change ((m.sourceSylowHom p hz x : p.C) : p.Tilde)=1 ↔ x∈centralLine
  rw [QuotientGroup.eq_one_iff]
  change m.sylowModelEmbedding x∈zpowers p.z ↔ x∈zpowers centralInP
  rw [hz,←m.sylowModelEmbedding_center,←MonoidHom.map_zpowers]
  exact mem_map_iff_mem m.sylowModelEmbedding_injective

private def quotientPlacement : CentralQuotient→*p.Tilde :=
  QuotientGroup.lift centralLine (m.sourceProjection p hz) (m.sourceProjection_ker p hz).ge

private theorem quotientPlacement_injective : Function.Injective (m.quotientPlacement p hz) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (m.sourceProjection_ker p hz).symm

private theorem tilde_map_source (H : Subgroup P) :
    p.tilde (H.map m.sylowModelEmbedding)=H.map (m.sourceProjection p hz) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (y:G)∈H.map m.sylowModelEmbedding at hy
    obtain ⟨a,ha,he⟩ := hy
    refine ⟨a,ha,?_⟩
    change QuotientGroup.mk' _ (m.sourceSylowHom p hz a)=QuotientGroup.mk' _ y
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext he)
  · rintro ⟨a,ha,rfl⟩
    refine ⟨m.sourceSylowHom p hz a,?_,rfl⟩
    exact ⟨a,ha,rfl⟩

private theorem quotientPlacement_core :
    quotientCore.map (m.quotientPlacement p hz)=p.tilde m.core := by
  rw [core,m.tilde_map_source p hz,quotientCore,map_map]
  rfl

private theorem quotientPlacement_top :
    (⊤:Subgroup CentralQuotient).map (m.quotientPlacement p hz)=p.tilde d.T := by
  rw [←m.range_sylowModelEmbedding,MonoidHom.range_eq_map,m.tilde_map_source p hz]
  rw [←map_top_of_surjective centralProjection (QuotientGroup.mk'_surjective centralLine),map_map]
  rfl

/-- The original 13.9.6 data, keeping the actual marked subgroup of G. -/
@[expose] noncomputable def coreData (ht : p.t=m.t) : CoreData p where
  Q := m.core
  le_T := m.core_le_sylow
  t_mem := ht ▸ m.t_mem_core
  factors := m.coreQuaternionData
  center_eq := by rw [m.center_core,←hz]
  tilde_thompson := by
    rw [←m.quotientPlacement_core p hz,←m.quotientPlacement_top p hz,
      Stellmacher.elementaryAbelianMaxJ_map_injective _ (m.quotientPlacement_injective p hz),
      thompson_centralQuotient]
  tilde_elementary := by
    rw [←m.quotientPlacement_core p hz]
    exact IsElementaryAbelian.map _
  tilde_card := by
    rw [←m.quotientPlacement_core p hz,card_map_of_injective (m.quotientPlacement_injective p hz),card_quotientCore]

/-- Exact no-transvection input to the source centralizer-normality theorem. -/
theorem coreData_hyperplane_fixers (ht : p.t=m.t)
    (E : Subgroup p.Tilde) (hE : E≤p.tilde (m.coreData p hz ht).Q) (hcard : Nat.card E=8) :
    p.tilde d.T⊓centralizer (E:Set p.Tilde)≤centralizer (p.tilde (m.coreData p hz ht).Q:Set p.Tilde) := by
  let f := m.quotientPlacement p hz
  have hf : Function.Injective f := m.quotientPlacement_injective p hz
  change E≤p.tilde m.core at hE
  change p.tilde d.T⊓centralizer (E:Set p.Tilde)≤centralizer (p.tilde m.core:Set p.Tilde)
  have hEr : E≤f.range := by
    rw [←m.quotientPlacement_core p hz] at hE
    exact hE.trans (map_le_range _ _)
  have heq : (E.comap f).map f=E := map_comap_eq_self hEr
  have hEc : E.comap f≤quotientCore := by
    rw [←comap_map_eq_self_of_injective hf quotientCore]
    apply comap_mono
    change E≤quotientCore.map (m.quotientPlacement p hz)
    rw [m.quotientPlacement_core p hz]
    exact hE
  have hsize : Nat.card (E.comap f)=8 := by
    calc
      Nat.card (E.comap f)=Nat.card ((E.comap f).map f) := (card_map_of_injective hf).symm
      _=8 := by rw [heq,hcard]
  rintro x ⟨hx,hcent⟩
  rw [←m.quotientPlacement_top p hz] at hx
  obtain ⟨a,_,rfl⟩ := hx
  have ha : a∈centralizer (E.comap f:Set CentralQuotient) := by
    intro b hb
    apply hf
    simpa only [map_mul] using hcent (f b) hb
  have hq := SymmetricFourWreath.hyperplane_fixers (E.comap f) hEc hsize ha
  rw [←m.quotientPlacement_core p hz]
  rintro _ ⟨b,hb,rfl⟩
  simpa only [map_mul] using congrArg f (hq b hb)

theorem coreData_self_centralizer (ht : p.t=m.t) :
    p.tilde d.T⊓centralizer (p.tilde (m.coreData p hz ht).Q:Set p.Tilde)≤
      p.tilde (m.coreData p hz ht).Q := by
  change p.tilde d.T⊓centralizer (p.tilde m.core:Set p.Tilde)≤p.tilde m.core
  rintro x ⟨hx,hc⟩
  rw [←m.quotientPlacement_top p hz] at hx
  obtain ⟨a,_,rfl⟩ := hx
  rw [←m.quotientPlacement_core p hz]
  apply mem_map_of_mem
  rw [←centralizer_quotientCore]
  intro b hb
  apply m.quotientPlacement_injective p hz
  simpa only [map_mul] using hc (m.quotientPlacement p hz b)
    ((m.quotientPlacement_core p hz) ▸ mem_map_of_mem (m.quotientPlacement p hz) hb)

include hz in
theorem core_normal (ht : p.t=m.t) (h : p.ClosureData) (hE : IsEvenCharacteristicAt d.T) :
    (m.core.subgroupOf p.C).Normal :=
  (m.coreData p hz ht).normal_of_hyperplane_fixers h hE (m.coreData_hyperplane_fixers p hz ht)

include hz in
theorem centralizer_z_solvable (ht : p.t=m.t) (h : p.ClosureData) (hE : IsEvenCharacteristicAt d.T) :
    Group.IsSolvable p.C :=
  (m.coreData p hz ht).centralizer_solvable_of_hyperplane_fixers h hE (m.coreData_hyperplane_fixers p hz ht)
end CFSG.Quasithin.Chapter13.Section09.Marking
