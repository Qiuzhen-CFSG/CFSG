module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootJoinedPaths
public import Theory.Representation.SymplecticFourOrthogonalCover.CommutatorKernels

/-!
# Whole-seed kernels in the equal-root branch

Symplectic duality compares full moving-layer fixed kernels through the
literal commutators. Transporting the root decomposition to the actual
neighbor extends the comparison to its whole Z-layer, with every central
attachment. The root-intersection centralizer calculation also places its
endpoint commutator inside the starting seed. EqualRootNormalization uses
these facts for the same two source-selected neighbors.

Source: MS93 (3.3)(ii), p.867, and (5.7), p.919.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover

private theorem split_commutator_le {G : Type*} [Group G]
    (Z U D A : Subgroup G) [IsMulCommutative Z]
    (hUZ : U ≤ Z) (hZ : Z=U ⊔ D) (hDA : D ≤ centralizer (A : Set G))
    (hAn : A ≤ normalizer (U : Set G)) : ⁅Z,A⁆ ≤ ⁅U,A⁆ := by
  have hcU : ⁅U,A⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hAn
  have hn : Z ≤ normalizer ((⁅U,A⁆ : Subgroup G) : Set G) :=
    (Z.le_centralizer.trans (centralizer_le (hcU.trans hUZ))).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [hZ]
  apply commutator_sup_le_of_relative_normal Z U D A ⁅U,A⁆ hn hUZ
    (le_sup_right.trans_eq hZ.symm) le_rfl
  rw [commutator_eq_bot_iff_le_centralizer.mpr hDA]
  exact bot_le

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full root-case seed decomposition holds at the actual neighboring
vertex, transported along the original graph action. -/
theorem Input.replacement_root_neighbor_Z_decomposition
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2) :
    Z d.radical v = U d.radical v ⊔
      (Z d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))) := by
  obtain ⟨g,hg,hga⟩ := stabilizer_transitive_neighbors d.radical t
    (adjacent_symm _ hat) (adjacent_symm _ hvt)
  have ht : act d.radical g t=t := hg
  have hp := path.act g
  have hi : (Q d.radical (act d.radical g a)).relIndex
      (Z d.radical (act d.radical g z)) < Nat.card F^2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hsmall
  have ha : Adjacent d.radical (act d.radical g a) t := by
    rw [←ht]
    exact (adjacent_act_iff d.radical g a t).mpr hat
  have hx := h.replacement_root_X_eq_Z d hp hb ha hi
  have hs := h.replacement_root_X_decomposition_center d hp hb hi
  rwa [hx,hga] at hs

/-- On the literal moving layer, commutator containment reverses full
fixed-kernel containment at the same vertex marking. -/
theorem Input.replacement_moving_fixed_antitone_of_commutator_le
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {v : Vertex d.radical} (hv : color d.radical v=false)
    (A B : Subgroup (FreeAmalgam d.radical))
    (hAS : A ≤ stabilizer d.radical v) (hBS : B ≤ stabilizer d.radical v)
    (hle : ⁅A,U d.radical v⁆ ≤ ⁅B,U d.radical v⁆) :
    U d.radical v ⊓ centralizer (B : Set (FreeAmalgam d.radical)) ≤
      U d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical)) := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d hv
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let σ := MovedSection.coverAction s e
  have hact (y : stabilizer d.radical v) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (γ y) w))=y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC y))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj y w
  have hh := embedded_fixed_antitone_of_commutator_le (MovedSection.coverProjection s e) he j hj
    A B (γ.comp (inclusion hAS)) (γ.comp (inclusion hBS))
    (fun a w => hact (inclusion hAS a) w) (fun b w => hact (inclusion hBS b) w)
    (by rwa [hjr])
  rwa [hjr] at hh

/-- The whole neighboring Z-layer has the same fixed kernel whenever the
literal commutators agree; every ambient-fixed attachment is retained. -/
theorem Input.replacement_root_neighbor_fixed_antitone_of_commutator_le
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (A B : Subgroup (FreeAmalgam d.radical))
    (hAS : A ≤ stabilizer d.radical v) (hBS : B ≤ stabilizer d.radical v)
    (hle : ⁅Z d.radical v,A⁆ ≤ ⁅Z d.radical v,B⁆) :
    Z d.radical v ⊓ centralizer (B : Set (FreeAmalgam d.radical)) ≤
      Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical)) := by
  let D := Z d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))
  have hs := h.replacement_root_neighbor_Z_decomposition d path hb hat hvt hsmall
  have hv : color d.radical v=false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hvt
    have ht : color d.radical t=true := by
      cases ht : color d.radical t
      · exact False.elim (h1 (path.start_color.trans ht.symm))
      · rfl
    cases hvv : color d.radical v
    · rfl
    · exact False.elim (h2 (hvv.trans ht.symm))
  let := geometry.Z_elementary (by omega) v hv
  have hDA : D ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hAS)
  have hDB : D ≤ centralizer (B : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hBS)
  have hc := split_commutator_le (Z d.radical v) (U d.radical v) D B
    (U_le_Z v) hs hDB (hBS.trans (U_normalized v))
  have hcomm : ⁅A,U d.radical v⁆ ≤ ⁅B,U d.radical v⁆ := by
    rw [commutator_comm A,commutator_comm B]
    exact ((commutator_mono (U_le_Z v) le_rfl).trans hle).trans hc
  have hf := h.replacement_moving_fixed_antitone_of_commutator_le d geometry hb hv A B hAS hBS hcomm
  intro x hx
  have hDU : D ≤ normalizer (U d.radical v : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans ((Z d.radical v).le_centralizer.trans (centralizer_le (U_le_Z v)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hx' : x ∈ (U d.radical v : Set (FreeAmalgam d.radical))*(D : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hDU,←hs]
    exact hx.1
  obtain ⟨u,hu,c,hc,rfl⟩ := hx'
  have huB : u ∈ centralizer (B : Set (FreeAmalgam d.radical)) := by
    have hh := (centralizer (B : Set (FreeAmalgam d.radical))).mul_mem hx.2
      ((centralizer (B : Set (FreeAmalgam d.radical))).inv_mem (hDB hc))
    simpa only [mul_inv_cancel_right] using hh
  exact ⟨hx.1,(centralizer (A : Set (FreeAmalgam d.radical))).mul_mem (hf ⟨hu,huB⟩).2 (hDA hc)⟩

/-- The endpoint commutator of any full root-intersection fixed subgroup
lies in the starting seed. This also controls every intermediate subgroup
containing that seed. -/
theorem Input.replacement_root_fixed_commutator_le_seed
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2)
    (Y : Subgroup (FreeAmalgam d.radical)) (hZY : Z d.radical a ≤ Y)
    (hYS : Y ≤ stabilizer d.radical z) (hYQ : Y ≤ Q d.radical a) :
    ⁅Y ⊓ centralizer ((X d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _),
      Z d.radical z⁆ ≤ Z d.radical a := by
  rw [h.replacement_root_X_intersection_centralizer d path hb hsmall Y hZY hYS]
  have hna : Q d.radical a ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1).trans (Z_normalized d.radical a)
  apply commutator_sup_le_of_relative_normal (Q d.radical a) (Z d.radical a)
    (Y ⊓ Q d.radical z) (Z d.radical z) (Z d.radical a) hna
    (hZY.trans hYQ) (inf_le_left.trans hYQ) (critical_commutator_le_start_seed path)
  rw [commutator_comm]
  exact ((commutator_mono le_rfl inf_le_right).trans_eq (geometry.centralizes z path.end_color)).trans bot_le

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
