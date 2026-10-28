module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoMidpoint
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThree

/-!
# The original contained-core branch of MS93 (3.7)(3)

For an original critical path with critical image of order q, containment
Q_alpha <= Z_alpha Q_alpha' bounds the whole-core centralizer index by q.
Four actual critical-root conjugates and the exact natural-factor index force
Q_alpha = U_alpha C_Q_alpha(L_alpha), retaining the complete fixed factor.
Its fixed involutions lie in the incident edge center, giving X_alpha = Z_alpha.
Centrality in the containing product identifies the full overlap, and
reciprocity and conjugacy give both overlap indices equal to q.

The companion SourceThreeNoncontained excludes failure of containment for
the original nonsylow star. SourceThree applies both branches to the selected
original star, discharging shortness and innerness from its construction.
No saturation or marked-image preservation for a minimum radical is assumed.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(3), first paragraph, printed p.874, using (1.1)(ii)(1).
Internal imports reuse the proved original full-core index and the generic
finite-group centralizer-index argument from the parallel source branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

/-- The actual critical product bounds the full original core action. -/
theorem original_core_centralizer_index_of_contained_core
    {g : Geometry R} {a z : Vertex R}
    (path : CriticalPath R g a z)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (hinside : Q R a ≤ Z R a ⊔ Q R z) :
    (centralizer (Z R z : Set (FreeAmalgam R))).relIndex
      (Q R a) ≤ 2^n := by
  have hZaS : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  have hQS : Q R z ≤ stabilizer R z := fun _ hx => hx.1
  let T := Q R z ⊔ Z R a
  have hTS : T ≤ stabilizer R z := sup_le hQS hZaS
  let := finite_stabilizer R z
  let : Finite T := Finite.of_injective (inclusion hTS) (inclusion_injective _)
  have he := SaturatedDistanceTwo.centralizer_index_of_fixed_supplement T (Q R z)
    (Z R a) (Z R z) rfl (hTS.trans (Z_normalized R z))
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R z path.end_color)))
  have hCZ : (centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf
      (Z R a) = (Q R z).subgroupOf (Z R a) := by
    rw [←MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer z path.end_color]
    ext x
    exact ⟨fun hx => ⟨hZaS x.property,hx⟩,fun hx => hx.2⟩
  have hi : (centralizer (Z R z : Set (FreeAmalgam R))).relIndex
      (Z R a) = 2^n := by
    change ((centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf
      (Z R a)).index = _
    rw [hCZ]
    exact hcritical
  have hQT : Q R a ≤ T := by simpa only [T,sup_comm] using hinside
  exact (relIndex_le_of_le_right hQT index_ne_zero_of_finite).trans_eq (he.trans hi)

/-- Four critical roots force the entire original core to be its natural
layer times its complete fixed factor when its critical centralizer index
is at most the field size. -/
theorem original_core_eq_moving_sup_fixed_of_critical_centralizer_index
    (hshort : IsShort K)
    {g : Geometry R} {a z : Vertex R}
    (path : CriticalPath R g a z) (hpos : 0 < g.b R)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (hindex : (centralizer (Z R z : Set (FreeAmalgam R))).relIndex
      (Q R a) ≤ 2^n) :
    Q R a = U R a ⊔ fixedCore R a := by
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hk : (commutatorPreimage (Q R a) (Z R z)
      (fixedCore R a)).relIndex (Q R a) ≤ 2^n := by
    apply le_trans ?_ hindex
    rw [←inf_relIndex_right (centralizer (Z R z : Set (FreeAmalgam R))) (Q R a)]
    apply relIndex_le_of_le_left ?_ index_ne_zero_of_finite
    apply le_commutatorPreimage inf_le_right
    rw [commutator_eq_bot_iff_le_centralizer.mpr inf_le_left]
    exact bot_le
  have hbound := (short_original_core_fixed_index_le_critical_index_pow_four
    h hshort path hpos hcritical).trans (Nat.pow_le_pow_left hk 4)
  rw [short_original_core_fixed_index_eq_natural_mul h hshort path.start_color] at hbound
  have hq : 0 < (2^n)^4 := pow_pos (pow_pos (by decide) _) _
  have hi : (U R a ⊔ fixedCore R a).relIndex (Q R a) = 1 := by
    have hl := Nat.le_of_mul_le_mul_left
      (show (2^n)^4 * (U R a ⊔ fixedCore R a).relIndex (Q R a) ≤ (2^n)^4 * 1 by
        simpa only [mul_one] using hbound) hq
    have hp : 0 < (U R a ⊔ fixedCore R a).relIndex (Q R a) :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    omega
  have hUQ : U R a ≤ Q R a := (U_le_Z a).trans
    ((g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]; exact hpos)).trans (omegaCenter_le _))
  exact le_antisymm (relIndex_eq_one.mp hi) (sup_le hUQ inf_le_left)

omit [Finite F] [CharP F 2] in
/-- The complete fixed involutions belong to the incident edge center;
consequently a full-core decomposition identifies X with Z. -/
theorem original_X_eq_Z_of_core_decomposition
    (hinner : K ⊔ pCore 2 H = ⊤)
    (g : Geometry R) (hpos : 0 < g.b R)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    (hcore : Q R a = U R a ⊔ fixedCore R a) :
    X R a = Z R a := by
  have hZX := g.omega_bound a ha (by rw [g.distance_constant a ha]; exact hpos)
  have hUD : U R a ≤ centralizer (fixedCore R a : Set (FreeAmalgam R)) :=
    ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R a ha))).trans (centralizer_le inf_le_left)
  apply le_antisymm ?_ hZX
  intro x hx
  have hxQ : x ∈ Q R a := omegaCenter_le _ hx
  rw [hcore,←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    (hUD.trans (Subgroup.centralizer_le_normalizer _))] at hxQ
  obtain ⟨u,hu,v,hv,rfl⟩ := hxQ
  have hvX : v ∈ X R a := by
    have hh := (X R a).mul_mem
      ((X R a).inv_mem (hZX (U_le_Z a hu))) hx
    simpa only [inv_mul_cancel_left] using hh
  have hvZ : v ∈ Z R a := Sp4Four.edge_Z_le_endpoint R ha hat
    (original_fixed_X_le_edge h hinner ha hat ⟨hvX,hv.2⟩)
  exact (Z R a).mul_mem (U_le_Z a hu) hvZ

/-- The contained-core case in the first paragraph of MS93 (3.7)(3). -/
theorem original_source_three_contained_core
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hpos : 0 < g.b R)
    (hat : Adjacent R a t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (hinside : Q R a ≤ Z R a ⊔ Q R z) :
    Q R a = U R a ⊔ fixedCore R a ∧ X R a = Z R a := by
  have hc := original_core_eq_moving_sup_fixed_of_critical_centralizer_index
    h hshort path hpos hcritical
    (original_core_centralizer_index_of_contained_core h path hcritical hinside)
  exact ⟨hc,original_X_eq_Z_of_core_decomposition h hinner g hpos path.start_color hat hc⟩

/-- Both indices of the full Z-layer overlap equal the field size. -/
theorem original_source_three_contained_core_overlap
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (hinside : Q R a ≤ Z R a ⊔ Q R z) :
    (Z R z).relIndex (Z R a) = 2^n ∧
      (Z R a).relIndex (Z R z) = 2^n := by
  have hXa := (original_source_three_contained_core h hshort hinner path (by omega) hat hcritical hinside).2
  have hcentral : Z R z ⊓ Q R a ≤
      centralizer ((Z R a ⊔ Q R z :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    apply sup_le
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R a path.start_color)).trans (centralizer_le inf_le_right)
    · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R z path.end_color))).trans (centralizer_le inf_le_left)
  have hZzX := g.omega_bound z path.end_color (by
    rw [g.distance_constant z path.end_color]
    change 0 < g.b R
    omega)
  have hinter : Z R z ⊓ Q R a = Z R z ⊓ Z R a := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←hXa]
      exact mem_omegaCenter_iff.mpr ⟨hx.2,
        (mem_omegaCenter_iff.mp (hZzX hx.1)).2.1,
        (hcentral.trans (centralizer_le hinside)) hx⟩
    · exact inf_le_inf_left _ (hXa.symm ▸ omegaCenter_le (Q R a))
  have hsmall : (Q R z).relIndex (Z R a) < (2^n)^2 := by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith
  have hzq : (Q R a).relIndex (Z R z) = 2^n := by
    simpa only [h.field_card] using
      (h.original_small_critical_indices_eq_field path (by omega) (by simpa only [h.field_card] using hsmall)).2
  have hzindex : (Z R a).relIndex (Z R z) = 2^n := by
    rw [←inf_relIndex_right (Z R a),inf_comm,←hinter,inf_comm,inf_relIndex_right]
    exact hzq
  have hcard : Nat.card (Z R a) = Nat.card (Z R z) := by
    obtain ⟨u,_,he⟩ := stabilizer_transitive_neighbors R t
      (adjacent_symm R hat) (adjacent_symm R hzt)
    rw [←he,Z_act,card_map_of_injective (MulAut.conj u⁻¹).injective]
  let := finite_Z R a
  let := finite_Z R z
  let I := Z R a ⊓ Z R z
  let : Finite I := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have haI := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) I
    (Z R a) bot_le inf_le_left
  have hzI := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) I
    (Z R z) bot_le inf_le_right
  have hIA : I.relIndex (Z R a) = (Z R z).relIndex (Z R a) := by
    change (Z R a ⊓ Z R z).relIndex (Z R a) = _
    rw [inf_comm,inf_relIndex_right]
  have hIZ : I.relIndex (Z R z) = (Z R a).relIndex (Z R z) :=
    inf_relIndex_right _ _
  rw [relIndex_bot_left,relIndex_bot_left,hIA] at haI
  rw [relIndex_bot_left,relIndex_bot_left,hIZ,hzindex] at hzI
  have hi : (Z R z).relIndex (Z R a) = 2^n := by
    have hp : 0 < Nat.card I := Nat.card_pos
    nlinarith
  exact ⟨hi,hzindex⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
