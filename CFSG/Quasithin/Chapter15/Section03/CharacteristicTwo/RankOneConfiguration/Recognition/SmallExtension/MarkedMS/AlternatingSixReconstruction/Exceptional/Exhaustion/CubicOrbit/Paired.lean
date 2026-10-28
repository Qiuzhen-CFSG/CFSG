module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicOrbit
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Exponent.Model
public import Theory.Frattini.NormalClosureElementary
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Contracts
public import Theory.Frattini.Intersection

/-!
# Separation and exponent two for the cubic critical-plane pair

The cubic kernel is exactly the kernel of the original whole moved-subgroup
representation. Its equivariant natural-or-augmentation model therefore lets
us apply the six-letter fixed-hyperplane calculation to the literal opposite
core intersection. Movement misses the component-fixed attachment, including
when the whole moved cover has order thirty-two. Reversing the critical pair
puts the critical-plane commutator disjoint from the opposite attachment.

The elementary plane normally generates its orbit, so every orbit square
lies in the plane commutator. A square belonging to both paired orbits is
also fixed by the opposite component and hence vanishes by separation.
Thus the literal paired intersection and paired commutator are elementary.
This does not yet make the entire orbit elementary: its fixed-quotient
recognition and full movement, as well as the intersection bound and larger
critical distances, remain with the reconstruction owner. CubicOrbit.Source
applies the new exponent calculation to whole-core recognition.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
The six-letter calculation is reused from Natural.Exhaustion.DistanceTwo.
Geometry.PairEstimates.Exponent.Model; the Frattini argument uses
Theory.Frattini.NormalClosureElementary. All graph maps and the cubic kernel
are retained, with no Sylow or faithful-initial-kernel assumption.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
open Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => edge L R
local notation "X₀" => centralOmega L R
local notation "W" => (⁅X₀,K⁆ : Subgroup M)
local notation "π" => projection h e hz hk

include h e hz hk in
/-- The whole moved subgroup has the same retained cubic kernel as the initial action. -/
theorem moved_projection_kernel : (π).ker = centralizer (W : Set M) := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  apply le_antisymm
  · rw [projection_kernel,←hk]
    exact centralizer_le (commutator_le_left X₀ K)
  · intro g hg
    change π g = 1
    obtain ⟨p,hp,_,ha⟩ := moved_natural_projection h e hz hk
    apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
    rw [map_one]
    ext v : 1
    obtain ⟨w,rfl⟩ := hp v
    rw [←ha]
    apply congrArg p
    apply Additive.toMul.injective
    apply Subtype.ext
    change g * (w.toMul : M) * g⁻¹ = (w.toMul : M)
    rw [←hg _ w.toMul.property,mul_inv_cancel_right]

include h e hz hk in
/-- The exact six-letter marking on the whole moved subgroup, including its fixed line. -/
theorem moved_subgroup_cover_model (hb : sourceDistance h = 2) :
    let := h.relative_normal
    let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
    BinaryPermutation.SixCover.IsNaturalOrCore
      (NormalElementaryQuotient.representation W π
        (projection_surjective_of_distanceTwo h e hz hk hb) (moved_projection_kernel h e hz hk))
      (MonoidHom.id _) := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  let q := QuotientGroup.mk' (layerKernel L R)
  let E := NormalElementaryQuotient.movedEquiv X₀ q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K
  let ρ := NormalElementaryQuotient.representation W π
    (projection_surjective_of_distanceTwo h e hz hk hb) (moved_projection_kernel h e hz hk)
  have hE (g : M) (v : Additive W) :
      E (ρ (π g) v) = (layerSection h).space.toRepresentation (q g) (E v) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.representation_apply W π
      (projection_surjective_of_distanceTwo h e hz hk hb) (moved_projection_kernel h e hz hk) g v).trans
      (NormalElementaryQuotient.representation_apply X₀ q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) g (E v).val).symm
  rcases moved_cover_model h e hz hk hb with ⟨f,hf⟩ | ⟨f,hf⟩
  · left
    refine ⟨E.trans f,?_⟩
    intro a v
    obtain ⟨g,rfl⟩ := projection_surjective_of_distanceTwo h e hz hk hb a
    exact (congrArg f (hE g v)).trans (hf (q g) (E v))
  · right
    refine ⟨E.trans f,?_⟩
    intro a v
    obtain ⟨g,rfl⟩ := projection_surjective_of_distanceTwo h e hz hk hb a
    exact (congrArg f (hE g v)).trans (hf (q g) (E v))

include h e hz hk in
/-- Movement on the opposite-core intersection misses the original component-fixed attachment. -/
theorem critical_intersection_commutator_inf_base_fixed_eq_bot
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b) :
    ⁅Q T c,Z T (alpha T) ⊓ Q T c⁆ ⊓
      centralizer (Ltilde T (alpha T) : Set (FreeAmalgam T)) = ⊥ := by
  let := h.relative_normal
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left X₀ K)
  let A := (Z T c).comap (embedM T)
  let B := (Q T c).comap (embedM T)
  let S := (Z T b).comap (embedM T)
  let V := (Z T (alpha T) ⊓ Q T c).comap (embedM T)
  have hc0 := critical_endpoint_color T (alpha T) rfl _ hc
  have hb0 := CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.edge_color hab
  have hQc := Q_le_adjacent_h T hb0 hcb
  have hQM : Q T c ≤ (embedM T).range := by
    apply le_trans _ (stabilizer_m_base T).le
    exact hQc.trans (fun _ hx => hx.2 _ (adjacent_symm T hab))
  have hZcQ : Z T c ≤ Q T c :=
    ((sourceGeometry h).omega_bound c hc0 (by
      rw [(sourceGeometry h).distance_constant c hc0]
      exact sourceDistance_pos h)).trans (omegaCenter_le _)
  have hBm : B.map (embedM T) = Q T c := map_comap_eq_self hQM
  have hAm : A.map (embedM T) = Z T c := map_comap_eq_self (hZcQ.trans hQM)
  have hVm : V.map (embedM T) = Z T (alpha T) ⊓ Q T c :=
    map_comap_eq_self (inf_le_right.trans hQM)
  have hZM : Z T b ≤ (embedM T).range := by
    apply le_trans _ (stabilizer_m_base T).le
    have he : Z T b = omegaCenter (Q T b) := by
      simp only [Z,hb0,Bool.true_eq_false,if_false,edgeOmega]
    exact (he ▸ omegaCenter_le (Q T b)).trans
      (fun _ hx => hx.2 _ (adjacent_symm T hab))
  have hSm : S.map (embedM T) = Z T b := map_comap_eq_self hZM
  have hZA : Z T c ≤ centralizer (Q T c : Set (FreeAmalgam T)) :=
    commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q T c hc0)
  have hBA : B ≤ centralizer (A : Set M) := by
    intro x hx a ha
    apply embedM_injective T
    rw [map_mul,map_mul]
    exact (hZA ha _ hx).symm
  have hVS : V ≤ W ⊔ S := by
    apply (map_le_map_iff_of_injective (embedM_injective T)).mp
    rw [Subgroup.map_sup,hSm,←graph_Z_eq_moved_sup_edge h e hz hab,hVm]
    exact inf_le_left
  have hVA : V ≤ centralizer (A : Set M) :=
    (comap_mono (show Z T (alpha T) ⊓ Q T c ≤ Q T c from inf_le_right)).trans hBA
  have hS : S ≤ centralizer (B : Set M) := by
    intro s hs x hx
    apply embedM_injective T
    rw [map_mul,map_mul]
    have hsZ : embedM T s ∈ omegaCenter (Q T b) := by
      change embedM T s ∈ Z T b at hs
      simpa only [Z,hb0,Bool.true_eq_false,if_false,edgeOmega] using hs
    exact (mem_omegaCenter_iff.mp hsZ).2.2 _ (hQc hx)
  have hSA : S ≤ centralizer (A : Set M) := hS.trans
    (centralizer_le (comap_mono hZcQ))
  obtain ⟨t,ht,htA⟩ := critical_image_eq_zpowers_transposition h e hz hk hb c hc
  have hA : A.map π = zpowers t := (critical_Z_image_eq h e hz hk hb c hc).trans htA
  have hzero := PairEstimates.commutator_inf_fixed_of_transposition W π
    (projection_surjective_of_distanceTwo h e hz hk hb) (moved_projection_kernel h e hz hk)
    K (component_image h e hz hk) (moved_subgroup_cover_model h e hz hk hb)
    A B S V t ht hA hBA hSA hS hVS hVA
  have hDm : (⁅B,V⁆ : Subgroup M).map (embedM T) =
      ⁅Q T c,Z T (alpha T) ⊓ Q T c⁆ := by rw [map_commutator,hBm,hVm]
  apply _root_.eq_bot_iff.mpr
  rintro x ⟨hx,hxK⟩
  rw [←hDm] at hx
  obtain ⟨z,hzmem,rfl⟩ := hx
  have hzK : z ∈ centralizer (K : Set M) := by
    intro k hkK
    apply embedM_injective T
    rw [map_mul,map_mul]
    exact hxK (embedM T k) ((graph_component h).symm ▸ mem_map_of_mem (embedM T) hkK)
  have hz1 : z = 1 := mem_bot.mp (hzero ▸ ⟨hzmem,hzK⟩)
  rw [hz1,map_one]
  exact one_mem _

include h e hz hk in
/-- Reversing the critical pair preserves separation from the opposite fixed attachment. -/
theorem critical_intersection_commutator_inf_opposite_fixed_eq_bot
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b) :
    ⁅Q T (alpha T),Z T c ⊓ Q T (alpha T)⁆ ⊓
      centralizer (Ltilde T c : Set (FreeAmalgam T)) = ⊥ := by
  have hc0 := critical_endpoint_color T (alpha T) rfl _ hc
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    (alpha T) rfl (sourceDistance_pos h) c hc0 hc
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color T hc0
  have hg : act T g⁻¹ c = alpha T := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  have hc' : color T (act T g⁻¹ c) = false := by rw [hg];rfl
  have hd0 := (criticalPair_act_iff T g⁻¹ c (alpha T)
    ((sourceGeometry h).exists_critical c hc0)
    ((sourceGeometry h).exists_critical (act T g⁻¹ c) hc')).mpr hr
  have hd : CriticalPair T (alpha T) (act T g⁻¹ (alpha T))
      ((sourceGeometry h).exists_critical _ rfl) := by simpa only [hg] using hd0
  have hdb := (adjacent_act_iff T g⁻¹ (alpha T) b).mpr hab
  have hab' : Adjacent T (alpha T) (act T g⁻¹ b) := by
    simpa only [hg] using (adjacent_act_iff T g⁻¹ c b).mpr hcb
  let f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  apply (map_eq_bot_iff_of_injective (f := f) _ (MulAut.conj (g⁻¹)⁻¹).injective).mp
  rw [←map_inf_centralizer_of_injective f (MulAut.conj (g⁻¹)⁻¹).injective,
    map_commutator,Subgroup.map_inf _ _ f (MulAut.conj (g⁻¹)⁻¹).injective,
    ←Q_act,←Z_act,←Ltilde_act,hg]
  exact critical_intersection_commutator_inf_base_fixed_eq_bot h e hz hk hb hd hab' hdb

include h e hz hk in
/-- The actual maximal-plane commutator misses the entire opposite fixed attachment. -/
theorem plane_commutator_inf_opposite_fixed_eq_bot
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b) :
    ⁅Q T (alpha T),criticalPlane T c b⁆ ⊓
      centralizer (Ltilde T c : Set (FreeAmalgam T)) = ⊥ := by
  have hPQ : criticalPlane T c b ≤ Q T (alpha T) := by
    apply (criticalPlane_le_orbit (sourceGeometry h) hb hc b).trans
    rw [criticalOrbit,Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact map_mono (critical_orbit_le_core h e hz hk hb hc hab hcb)
  apply le_bot_iff.mp
  apply (inf_le_inf_right _ (commutator_mono le_rfl
    (le_inf (criticalPlane_le_opposite c b) hPQ))).trans
  exact (critical_intersection_commutator_inf_opposite_fixed_eq_bot h e hz hk hb hc hab hcb).le

include h e hz hk in
/-- Normal generation by the elementary plane traps every orbit square in its literal commutator. -/
theorem orbit_square_mem_plane_commutator
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b)
    {x : FreeAmalgam T} (hx : x ∈ criticalOrbit T c b) :
    x ^ 2 ∈ ⁅Q T (alpha T),criticalPlane T c b⁆ := by
  let A := criticalOrbitNative T c b
  let P := (criticalPlane T c b).comap (embedM T)
  have hAQ := critical_orbit_le_core h e hz hk hb hc hab hcb
  have hc0 := critical_endpoint_color T (alpha T) rfl _ hc
  let := Z_elementary_of_positive T (sourceGeometry h) c hc0 (by
    rw [(sourceGeometry h).distance_constant c hc0]
    exact sourceDistance_pos h)
  let : IsElementaryAbelian 2 (criticalPlane T c b) :=
    IsElementaryAbelian.of_le (criticalPlane_le_opposite c b)
  let : IsElementaryAbelian 2 P :=
    IsElementaryAbelian.comap_of_injective _ (embedM_injective T) _
  let : Fact (IsPGroup 2 A) := ⟨pCore_isPGroup.of_injective
    (inclusion hAQ) (inclusion_injective _)⟩
  obtain ⟨y,hy,rfl⟩ := hx
  have hphi : y ^ 2 ∈ (frattini A).map A.subtype :=
    mem_map_of_mem A.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨y,hy⟩ : A))
  have hcmt := normalClosure_frattini_image_le_commutator P (pCore 2 M)
    pCore_isPGroup hAQ hphi
  have hh := mem_map_of_mem (embedM T) hcmt
  rw [map_commutator,←Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le,
    map_pow] at hh
  rw [←orbit_commutator_eq_plane h e hz hk hb hc hab hcb]
  exact hh

include h e hz hk in
/-- Orbit squares lie in the common edge layer and centralize the original component. -/
theorem orbit_square_central_edge
    (hb : sourceDistance h = 2) {c b : Vertex T}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b)
    {x : FreeAmalgam T} (hx : x ∈ criticalOrbit T c b) :
    x ^ 2 ∈ Z T b ⊓ centralizer (Ltilde T (alpha T) : Set (FreeAmalgam T)) := by
  have hp := orbit_square_mem_plane_commutator h e hz hk hb hc hab hcb hx
  refine ⟨criticalPlane_commutator_le (sourceGeometry h) hb hc hab hcb hp,?_⟩
  rw [←orbit_commutator_eq_plane h e hz hk hb hc hab hcb] at hp
  apply commutator_eq_bot_iff_le_centralizer.mp _ hp
  rw [Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le,
    criticalOrbit,graph_component h,←map_commutator,←map_commutator,
    orbit_commutator_centralizes_component h e hz hk hb hc hab hcb,Subgroup.map_bot]

include h e hz hk in
/-- The square bound follows the specified conjugation of the opposite orbit. -/
theorem rebased_square_central_edge
    (hb : sourceDistance h = 2) {c b : Vertex T} {B : Subgroup (FreeAmalgam T)}
    (hr : RebasedOrbit T (sourceGeometry h) c b B)
    {x : FreeAmalgam T} (hx : x ∈ B) :
    x ^ 2 ∈ Z T b ⊓ centralizer (Ltilde T c : Set (FreeAmalgam T)) := by
  obtain ⟨g,d,hga,_,hgb,hd,hdb,rfl⟩ := hr
  obtain ⟨y,hy,rfl⟩ := hx
  let i := (MulAut.conj g⁻¹).toMonoidHom
  have hZ : (Z T (beta T)).map i = Z T b := by rw [←Z_act,hgb]
  have hL : (Ltilde T (alpha T)).map i = Ltilde T c := by rw [←Ltilde_act,hga]
  obtain ⟨hyZ,hyC⟩ := orbit_square_central_edge h e hz hk hb hd (base_adjacent T) hdb hy
  change (i y) ^ 2 ∈ _
  rw [←map_pow]
  refine ⟨hZ ▸ mem_map_of_mem i hyZ,?_⟩
  intro k hkK
  rw [←hL] at hkK
  obtain ⟨z,hzK,rfl⟩ := hkK
  exact (map_mul i z (y^2)).symm.trans ((congrArg i (hyC z hzK)).trans (map_mul i (y^2) z))

include h e hz hk in
/-- The intersection of the actual paired orbits has exponent two. -/
theorem paired_intersection_elementary
    (hb : sourceDistance h = 2) {c b : Vertex T} {B : Subgroup (FreeAmalgam T)}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b)
    (hr : RebasedOrbit T (sourceGeometry h) c b B) :
    IsElementaryAbelian 2 (criticalOrbit T c b ⊓ B : Subgroup (FreeAmalgam T)) := by
  let D := (criticalOrbit T c b ⊓ B : Subgroup (FreeAmalgam T))
  have hs (x : D) : x ^ 2 = 1 := by
    apply Subtype.ext
    exact mem_bot.mp ((plane_commutator_inf_opposite_fixed_eq_bot h e hz hk hb hc hab hcb) ▸
      ⟨orbit_square_mem_plane_commutator h e hz hk hb hc hab hcb x.property.1,
       (rebased_square_central_edge h e hz hk hb hr x.property.2).2⟩)
  exact {
    toIsMulCommutative := ⟨⟨fun a b =>
      Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

include h e hz hk in
/-- The rebased orbit stays in its original vertex core with the original normalization. -/
theorem rebased_orbit_core_and_normalized
    (hb : sourceDistance h = 2) {c b : Vertex T} {B : Subgroup (FreeAmalgam T)}
    (hr : RebasedOrbit T (sourceGeometry h) c b B) :
    B ≤ Q T c ∧ stabilizer T c ≤ normalizer (B : Set (FreeAmalgam T)) := by
  obtain ⟨g,d,hga,_,hgb,hd,hdb,rfl⟩ := hr
  let i := (MulAut.conj g⁻¹).toMonoidHom
  have hQ : (Q T (alpha T)).map i = Q T c := by rw [←Q_act,hga]
  have hS : (stabilizer T (alpha T)).map i = stabilizer T c := by rw [←stabilizer_act,hga]
  constructor
  · rw [←hQ,Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact map_mono (map_mono (critical_orbit_le_core h e hz hk hb hd (base_adjacent T) hdb))
  · rw [←hS]
    exact (map_mono (criticalOrbit_normalized (R := T) d (beta T))).trans (le_normalizer_map i)

include h e hz hk in
/-- Both normalizations place the paired commutator in the proved elementary intersection. -/
theorem paired_commutator_elementary
    (hb : sourceDistance h = 2) {c b : Vertex T} {B : Subgroup (FreeAmalgam T)}
    (hc : CriticalPair T (alpha T) c ((sourceGeometry h).exists_critical _ rfl))
    (hab : Adjacent T (alpha T) b) (hcb : Adjacent T c b)
    (hr : RebasedOrbit T (sourceGeometry h) c b B) :
    IsElementaryAbelian 2 (⁅criticalOrbit T c b,B⁆ : Subgroup (FreeAmalgam T)) := by
  let := paired_intersection_elementary h e hz hk hb hc hab hcb hr
  obtain ⟨hBQ,hBN⟩ := rebased_orbit_core_and_normalized h e hz hk hb hr
  have hAQ : criticalOrbit T c b ≤ Q T (alpha T) := by
    rw [criticalOrbit,Q_alpha T h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact map_mono (critical_orbit_le_core h e hz hk hb hc hab hcb)
  have hBG : B ≤ stabilizer T (alpha T) :=
    (hBQ.trans (Q_le_adjacent_h T
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.edge_color hab) hcb)).trans
        (fun _ hx => hx.2 _ (adjacent_symm T hab))
  have hAG : criticalOrbit T c b ≤ stabilizer T c :=
    hAQ.trans (CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer hab hcb)
  exact IsElementaryAbelian.of_le (le_inf
    (le_normalizer_iff_commutator_le_left.mp (hBG.trans (criticalOrbit_normalized c b)))
    (le_normalizer_iff_commutator_le_right.mp (hAG.trans hBN)))

end AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
