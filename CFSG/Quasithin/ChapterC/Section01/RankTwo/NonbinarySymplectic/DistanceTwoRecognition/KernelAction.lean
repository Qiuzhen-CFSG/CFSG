module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.RootCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.NonFrattini
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.CentralLayers

/-!
# The opposite-kernel action and the secondary fixed layer

The actual critical commutator covers a nonzero field line, centralized by
Q_alpha. Fixing this line makes the whole Q_alpha action inner on the opposite
natural quotient. Its marking has exactly the kernel Q_alpha intersect
Q_alpha', and Z_alpha acts by transvections at the original field degree.

The symplectic two-group commutator calculation therefore puts the secondary
orbit's commutator in the opposite kernel. Normality and the faithful simple
component place this commutator, and the entire Frattini image, in the fixed
part of X_alpha. That fixed part is retained, not assumed trivial.

Source: MS93 (3.6), printed p.871. The paired secondary-orbit contradiction
and field restriction of (3.7) remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
section KernelAction
variable {M J V E : Type*} [Group M] [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  {T : Subgroup M} {geometry : Geometry T} {a z : Vertex T}
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]

private theorem critical_kernel_image_le_component
    (path : CriticalPath T geometry a z) (hb : geometry.b T = 2)
    (hcard : 2 < Nat.card E)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := E)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam T)
    (hj : Function.Injective j) (hjr : j.range = U T z)
    (κ : stabilizer T z →* J)
    (hconj : ∀ (g : stabilizer T z) (v : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
        (g : FreeAmalgam T)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam T)⁻¹)
    (β : Z T a →* L (K := E))
    (hβ : ∀ x : Z T a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) v)) =
        (x : FreeAmalgam T)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam T)⁻¹)
    (hβcard : Nat.card β.range = Nat.card E) :
    ∀ u : Q T a, ∀ hu : u.val ∈ stabilizer T z, κ ⟨u,hu⟩ ∈ B := by
  have hex : ∃ x : Z T a, β x ≠ 1 := by
    by_contra hn
    push Not at hn
    have hr : β.range = ⊥ := by
      apply le_bot_iff.mp
      rintro _ ⟨x,rfl⟩
      exact hn x
    rw [hr,card_bot] at hβcard
    omega
  obtain ⟨x,hx⟩ := hex
  have hexv : ∃ v : Vector E, binaryNatural (β x) v - v ≠ 0 := by
    by_contra hn
    push Not at hn
    have he : binaryNatural (β x) = binaryNatural (1 : L (K := E)) := by
      apply LinearMap.ext
      intro v
      simpa only [map_one,Module.End.one_apply] using sub_eq_zero.mp (hn v)
    exact hx (binaryNatural_injective he)
  obtain ⟨v,hv⟩ := hexv
  let v₀ := binaryNatural (β x) v - v
  let p := MovedSection.coverProjection s e
  let σ := MovedSection.coverAction s e
  let d : L (K := E) ≃* Sp E :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard)).trans
      Subgroup.topEquiv
  have hZa : Z T a ≤ X T a := geometry.omega_bound a path.start_color (by
    rw [geometry.distance_constant a path.start_color]
    change 0 < geometry.b T
    omega)
  intro u hu
  apply SymplecticNaturalNormalizer.mem_component_of_fixes_field_line B (hcent ▸ bot_le)
    hcard (e.groupEquiv.trans d) (MovedSection.ambientAction s e)
    (fun b w => MovedSection.ambientAction_component s e b w) (κ ⟨u,hu⟩) v₀ hv
  intro c
  obtain ⟨w,hw⟩ := hp.1 (c • v)
  let y := σ (β x) w - w
  have hy : j (Multiplicative.ofAdd y) ∈ Z T a := by
    dsimp only [y]
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hβ]
    apply CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path
    apply commutator_mem_commutator x.property
    apply DistanceEight.U_le_Z T z
    rw [←hjr]
    exact ⟨Multiplicative.ofAdd w,rfl⟩
  have hpy : p y = c • v₀ := by
    dsimp only [y]
    rw [map_sub,p.isIntertwining,hw]
    change symplecticDerivedNatural 2 (β x) (c • v) - c • v =
      c • (symplecticDerivedNatural 2 (β x) v - v)
    rw [map_smul,smul_sub]
  have hfix : s.space.toRepresentation (κ ⟨u,hu⟩) y = y := by
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hconj,←Q_le_centralizer_X T a u.property _ (hZa hy),mul_inv_cancel_right]
  rw [←hpy,←MovedSection.coverProjection_ambient,hfix]

end KernelAction

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

set_option maxHeartbeats 400000 in
/-- The entire original two-kernel has an inner marked action on the opposite
natural layer. Its exact kernel is the intersection of the two graph kernels,
and the original Z-layer acts by transvections. -/
theorem replacement_nonfrattini_kernel_root_action
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    ∃ E : BinaryField, E.degree = n ∧ ∃ f : Q d.radical a →* Sp E.Carrier,
      f.ker.map (Q d.radical a).subtype = Q d.radical a ⊓ Q d.radical z ∧
      (∀ u : Q d.radical a, (u : FreeAmalgam d.radical) ∈ Z d.radical a →
        Module.finrank E.Carrier (InvolutionTypes.movedSpace (f u)) ≤ 1) := by
  let := replacementComponent_normal h d
  let B := replacementComponent d
  let s := replacementMovedSection h d
  obtain ⟨he,ha⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega)
    (replacement_critical_index_lt_field_sq_of_nonfrattini h d path hb hlarge)
  obtain ⟨⟨E,hE,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  have hFcard : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFcard]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (quotient_image_card _ _ _ hAZ κ hκQ).trans (he.trans hFcard.symm)
  have hδ : ∀ x : Z d.radical a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := inner_root_actor_of_field_index path (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a path.start_color)
    h.nonbinary hFcard s e hecov (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ hδ hδcard (ha.trans hFcard.symm)
  have hQS : Q d.radical a ≤ stabilizer d.radical z :=
    Q_le_stabilizer_of_dist_two d.radical a z path.start_color
      (path.critical.1.trans ((g.distance_constant a path.start_color).trans hb))
  let δQ := κ.comp (inclusion hQS)
  have hinner (u : Q d.radical a) : δQ u ∈ B :=
    critical_kernel_image_le_component path hb hcard s e hecov
      (replacement_component_image_structure h d).2.2.2.2 j hj hjr κ hconj β hβ hβcard
      u (hQS u.property)
  let βQ := e.groupEquiv.toMonoidHom.comp (δQ.codRestrict B hinner)
  let f := (commutator (Sp E.Carrier)).subtype.comp βQ
  have hmark (u : Q d.radical a) : (e.groupEquiv.symm (βQ u) : _) = δQ u := by
    change (e.groupEquiv.symm (e.groupEquiv ⟨δQ u,_⟩) : _) = δQ u
    rw [e.groupEquiv.symm_apply_apply]
  have hfk : f.ker = δQ.ker := by
    ext u
    change ((e.groupEquiv ⟨δQ u,hinner u⟩ : L (K := E.Carrier)) : Sp E.Carrier) = 1 ↔ δQ u = 1
    constructor
    · intro hu
      have hh : e.groupEquiv ⟨δQ u,hinner u⟩ = 1 := Subtype.ext hu
      exact congrArg Subtype.val (e.groupEquiv.map_eq_one_iff.mp hh)
    · intro hu
      have hh : (⟨δQ u,hinner u⟩ : B) = 1 := Subtype.ext hu
      rw [hh,map_one]
      rfl
  refine ⟨E,hE,f,?_,?_⟩
  · rw [hfk]
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,hκQ ▸ mem_map_of_mem (stabilizer d.radical z).subtype
        (show inclusion hQS u ∈ κ.ker from hu)⟩
    · rintro ⟨hxa,hxz⟩
      refine ⟨⟨x,hxa⟩,?_,rfl⟩
      rw [←hκQ] at hxz
      obtain ⟨u,hu,he⟩ := hxz
      have he' : u = inclusion hQS ⟨x,hxa⟩ := Subtype.ext he
      change κ (inclusion hQS ⟨x,hxa⟩) = 1
      change κ u = 1 at hu
      rwa [he'] at hu
  · intro u hu
    let v : Z d.radical a := ⟨u,hu⟩
    have hsame : βQ u = β v := by
      apply e.groupEquiv.symm.injective
      apply Subtype.ext
      rw [hmark,hβmark]
      rfl
    have hm : InvolutionTypes.movedSpace (f u) ≤
        displacementSpace (β.range.map (commutator (Sp E.Carrier)).subtype) := by
      rintro w ⟨v₀,rfl⟩
      change (βQ u).val • v₀ - v₀ ∈ _
      rw [hsame]
      exact Coinvariants.sub_mem_ker
        (ρ := (symplecticNatural 2).comp
          (β.range.map (commutator (Sp E.Carrier)).subtype).subtype)
        ⟨(β v).val,⟨β v,⟨v,rfl⟩,rfl⟩⟩ v₀
    exact (Submodule.finrank_mono hm).trans_eq hd
/-- In the failed whole-core branch, the entire secondary commutator and its
Frattini image lie in the component-fixed part of X. The fixed part is retained. -/
theorem replacement_secondary_orbit_fixed_bounds
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    {t : Vertex d.radical} (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let Y := Sp4Four.secondarySeed d.radical a t z
    let A := Sp4Four.secondaryOrbit d.radical a Y
    let D := X d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))
    ⁅A,Q d.radical a⁆ ≤ D ∧ (frattini A).map A.subtype ≤ D := by
  let Y := Sp4Four.secondarySeed d.radical a t z
  let A := Sp4Four.secondaryOrbit d.radical a Y
  let S := stabilizer d.radical a
  have hYQ := replacement_secondary_seed_le_kernel h d path hb hat hzt hlarge
  obtain ⟨hAQ,hbound,_⟩ := replacement_secondary_orbit_bounds h d path hb hat hzt hlarge
  obtain ⟨E,hE,f,hf,hroot⟩ := replacement_nonfrattini_kernel_root_action h d path hb hlarge
  have hcard : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  let : IsElementaryAbelian 2 Y :=
    Sp4Four.secondarySeed_elementary d.radical g path.end_color (by omega)
  have hNQ : ⁅A,Q d.radical a⁆ ≤ Q d.radical z := by
    have hh := Sp4Four.CoreReconstruction.conjugatesIn_commutator_le_marked_kernel hcard
      (Nat.le_of_lt h.nonbinary) Y S (Q d.radical a) (Z d.radical a)
      (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d) a path.start_color)
      hYQ (Q_normalized d.radical a) hbound f hroot
    rw [hf] at hh
    exact hh.trans inf_le_right
  have hAS : A ≤ S := hAQ.trans (fun _ hx => hx.1)
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  let : (A.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (NormalizerTransfer.conjugatesIn_normalized Y S)
  let : ((Q d.radical a).subgroupOf S).Normal := Q_normal d.radical a
  let N := ⁅A.subgroupOf S,(Q d.radical a).subgroupOf S⁆
  have hNm : N.map S.subtype = ⁅A,Q d.radical a⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hAS,map_subgroupOf_eq_of_le hQS]
  have hn : S ≤ normalizer (⁅A,Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) := by
    have hh := N.le_normalizer_map S.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hNm] at hh
  have hfixed := replacement_critical_X_layer_le_fixed h d g path hb ⁅A,Q d.radical a⁆
    (hbound.trans (g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]
      change 0 < g.b d.radical
      omega))) hNQ hn
  exact ⟨hfixed,(Sp4Four.secondary_orbit_frattini_le d.radical g (replacement_isPGroup h d)
    (replacement_core_le h d) path.start_color path.end_color (by omega) Y
    (Sp4Four.secondarySeed_le d.radical a t z) hYQ).trans hfixed⟩

/-- The opposite two-kernel lies in the actual component times the original
local two-kernel, rather than merely acting inner on an unmarked quotient. -/
theorem replacement_nonfrattini_kernel_le_component
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Q d.radical a ≤ Ltilde d.radical z ⊔ Q d.radical z := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨he,ha⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega)
    (replacement_critical_index_lt_field_sq_of_nonfrattini h d path hb hlarge)
  obtain ⟨⟨E,hE,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  have hFcard : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFcard]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (quotient_image_card _ _ _ hAZ κ hκQ).trans (he.trans hFcard.symm)
  have hδ : ∀ x : Z d.radical a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := inner_root_actor_of_field_index path (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a path.start_color)
    h.nonbinary hFcard s e hecov (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ hδ hδcard (ha.trans hFcard.symm)
  have hQS : Q d.radical a ≤ stabilizer d.radical z :=
    Q_le_stabilizer_of_dist_two d.radical a z path.start_color
      (path.critical.1.trans ((g.distance_constant a path.start_color).trans hb))
  have hinner : (Q d.radical a).subgroupOf (stabilizer d.radical z) ≤
      (replacementComponent d).comap κ := by
    intro u hu
    exact critical_kernel_image_le_component path hb hcard s e hecov
      (replacement_component_image_structure h d).2.2.2.2 j hj hjr κ hconj β hβ hβcard
      ⟨u.val,hu⟩ u.property
  rw [←hκL,comap_map_eq] at hinner
  have hh := map_mono (f := (stabilizer d.radical z).subtype) hinner
  rwa [map_subgroupOf_eq_of_le hQS,Subgroup.map_sup,
    map_subgroupOf_eq_of_le (Ltilde_le_stabilizer z),hκQ] at hh


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
