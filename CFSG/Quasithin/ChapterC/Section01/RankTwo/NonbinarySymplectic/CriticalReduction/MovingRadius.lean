module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusGrowth
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusFour

/-!
# Radius growth after removing the full fixed preimage

The actual fixed preimage B has residual commutator in Z. If the radius
modulo B had order below q⁴, the symplectic small-section theorem would
place the radius commutator in B. Two-perfect commutator idempotence then
places it in Z, contradicting MS3 and residual--edge generation.
Thus the q⁴ bound persists modulo the entire fixed preimage.

The q³ radius-image bound implies that every kernel within critical range
has index at least q modulo B, even without containment of B in that
kernel. In particular such a kernel cannot lie in B. These are bounds on
the full source subgroups; no central attachment or fixed factor is removed.
Source: MS93 (2.1)(iii) and the fixed-kernel arguments in (5.7)--(5.11),
printed pp.856, 919--924. Application: `RadiusTrapping`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Removing the entire fixed preimage still leaves a radius quotient of
order at least q⁴. -/
theorem Input.replacement_moving_radius_index_ge_fourth_power
    (geometry : Geometry d.radical) (hb : 2 < geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    Nat.card F ^ 4 ≤ (B d.radical a (geometry.Z_normal a)).relIndex (V d.radical a) := by
  let S := stabilizer d.radical a
  let D := B d.radical a (geometry.Z_normal a)
  have hVQ := geometry.V_le_Q hb a ha
  have hVS : V d.radical a ≤ S := hVQ.trans (fun _ hx => hx.1)
  have hnD : S ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    Escape.Propagation.Rigidity.B_normalized hb a ha
  let := finite_stabilizer d.radical a
  let : Finite (V d.radical a) := Finite.of_injective (inclusion hVS) (inclusion_injective _)
  let : Finite (Ltilde d.radical a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  let : (D.subgroupOf (V d.radical a)).Normal :=
    normal_subgroupOf_of_le_normalizer (hVS.trans hnD)
  let := h.quotient_simple
  let : IsSimpleGroup (Matrix.symplecticGroup (Fin 2) F) := h.quotientEquiv.symm.isSimpleGroup
  obtain ⟨q,hq,hker⟩ := h.replacement_residual_projection d ha
  have hpV := (Q_isPGroup d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) a ha).to_le hVQ
  have hid : ⁅⁅V d.radical a,Ltilde d.radical a⁆,Ltilde d.radical a⁆ =
      ⁅V d.radical a,Ltilde d.radical a⁆ := by
    let A := (V d.radical a).subgroupOf S
    let : A.Normal := normal_subgroupOf_of_le_normalizer (DistanceEight.V_normalized d.radical a)
    have hi := commutator_isPPerfect_idempotent (pResidual 2 S) A
      (isPPerfect_pResidual 2) hpV.comap_subtype le_normalizer_of_normal
    have hi' := congrArg (Subgroup.map S.subtype) hi
    have hA : A.map S.subtype = V d.radical a := map_subgroupOf_eq_of_le hVS
    simp only [map_commutator,hA] at hi'
    exact hi'
  have hBZ : ⁅D,Ltilde d.radical a⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff d.radical a (geometry.Z_normal a) hVS x).mp hx).2 l hl
  have hne : Z d.radical a ≠ ⊥ := by
    obtain ⟨z,hz⟩ := criticalPair_exists d.radical a (geometry.exists_critical a ha)
    intro he
    exact hz.2 (he ▸ bot_le)
  by_contra! hi
  have hVD : ⁅V d.radical a,Ltilde d.radical a⁆ ≤ D :=
    commutator_component_le_of_symplectic_section_lt_fourth_power
      (by have := h.nonbinary; omega) h.field_card rfl
      (Ltilde d.radical a) (V d.radical a) D
      (isPPerfect_embedded_pResidual_of_finite 2 _) q hq hker hpV hi
      ((Ltilde_le_stabilizer a).trans (DistanceEight.V_normalized d.radical a))
      ((Ltilde_le_stabilizer a).trans hnD)
  have hVZ : Vcirc d.radical a ≤ Z d.radical a :=
    hid.symm.le.trans ((commutator_mono hVD le_rfl).trans hBZ)
  exact radius_moving_not_le_Z_of_residual_edge_generation
    (h.replacement_characteristic d) (h.replacement_residual_edge_generation d)
    geometry hb ha hat hne hVZ

/-- Every nearby full radius kernel still has index at least q modulo the
entire fixed preimage B, not merely modulo the seed Z. -/
theorem Input.replacement_moving_radius_kernel_index_ge_field
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t z : Vertex d.radical} (ha : color d.radical a = false)
    (hz : color d.radical z = false) (hat : Adjacent d.radical a t)
    (hd : (cosetGraph d.radical).dist a z + 2 ≤ geometry.b d.radical) :
    Nat.card F ≤ (B d.radical a (geometry.Z_normal a)).relIndex
      (V d.radical a ⊓ Q d.radical z) := by
  let D := B d.radical a (geometry.Z_normal a)
  have hlo := h.replacement_moving_radius_index_ge_fourth_power d geometry (by omega) ha hat
  have hup := h.replacement_radius_image_le_cube d geometry hb ha hz hd
  let := finite_stabilizer d.radical a
  let : Finite (V d.radical a) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) a ha).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  have hi : D.relIndex (V d.radical a) ≤ (D ⊓ Q d.radical z).relIndex (V d.radical a) :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  have hprod := relIndex_inf_mul_relIndex D (Q d.radical z) (V d.radical a)
  rw [inf_comm (Q d.radical z) (V d.radical a)] at hprod
  have hm := Nat.mul_le_mul_left (D.relIndex (V d.radical a ⊓ Q d.radical z)) hup
  rw [hprod] at hm
  have hl : Nat.card F ^ 4 ≤ (D ⊓ Q d.radical z).relIndex (V d.radical a) := hlo.trans hi
  have hpos : 0 < Nat.card F ^ 3 := pow_pos (Nat.card_pos (α := F)) _
  have he : Nat.card F ^ 4 = Nat.card F * Nat.card F ^ 3 := by ring
  rw [he] at hl
  nlinarith

/-- Thus the nearby kernel is never swallowed by the full fixed preimage. -/
theorem Input.replacement_radius_kernel_not_le_B
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t z : Vertex d.radical} (ha : color d.radical a = false)
    (hz : color d.radical z = false) (hat : Adjacent d.radical a t)
    (hd : (cosetGraph d.radical).dist a z + 2 ≤ geometry.b d.radical) :
    ¬ V d.radical a ⊓ Q d.radical z ≤ B d.radical a (geometry.Z_normal a) := by
  intro hle
  have hi := h.replacement_moving_radius_kernel_index_ge_field d geometry hb ha hz hat hd
  rw [relIndex_eq_one.mpr hle] at hi
  have hq : 1 < Nat.card F := by
    rw [h.field_card]
    exact one_lt_pow₀ (by decide) (by have := h.nonbinary; omega)
  omega

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
