module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IntersectionMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootEscape

/-!
# Full critical-intersection fixed kernels on the characteristic replacement

The full natural cover identifies the pointwise fixer of the critical root
hyperplane with the original root modulo Q. This gives the literal fixed
kernel in any endpoint actor containing the starting seed, first on the
whole Z-intersection and then on the whole X-intersection. All central
attachments stay in the subgroups and in the quotient kernel.

For a trapped neighboring seed the endpoint consequently normalizes its
fixed kernel joined with the starting seed. This supplies the endpoint
normalization clause in MS93 (5.7), printed p.919, using (3.3)(ii), p.867.
The other generator's normalization and the small index bound are still
needed to exclude trapping; this module does not assert distance two.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.OneCohomology Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
section Model
variable {H J V F : Type*} [Group H] [Finite H] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  {R : Subgroup H} {geometry : Geometry R} {a z : Vertex R}

omit [Finite H] in
private theorem root_intersection_fixed_kernel_of_cover
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hCz : C R z = Q R z) (hF : 2 < Nat.card F)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z)
    (κ : stabilizer R z →* J)
    (hκC : κ.ker.map (stabilizer R z).subtype = C R z)
    (hκ : ∀ x : stabilizer R z, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (β : Z R a →* L (K := F))
    (hAZ : Z R a ≤ stabilizer R z)
    (hβmark : ∀ x : Z R a, (e.groupEquiv.symm (β x) : J)=κ (inclusion hAZ x))
    (hβ : ∀ x : Z R a, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (hd : Module.finrank F (displacementSpace (β.range.map (commutator (Sp F)).subtype))=1)
    (hc : Nat.card β.range=Nat.card F)
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ stabilizer R z)
    (hZY : Z R a ≤ Y) :
    Y ⊓ centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _) =
      Z R a ⊔ (Y ⊓ Q R z) := by
  let p := MovedSection.coverProjection s e
  let σ := MovedSection.coverAction s e
  let ψ := MovedSection.ambientAction s e
  let d : L (K := F) ≃* Sp F :=
    (MulEquiv.subgroupCongr
      (OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF)).trans Subgroup.topEquiv
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary hb a path.start_color
  have hP : IsPGroup 2 β.range :=
    (IsElementaryAbelian.isPGroup 2 (Z R a)).of_surjective β.rangeRestrict β.rangeRestrict_surjective
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  have hroot (y : Y)
      (hyfix : y.val ∈ centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) :
      ∃ x : Z R a,
      κ (inclusion hAZ x) = κ (inclusion hYZ y) := by
    have hfixed (w : s.space.toSubmodule)
        (hw : w ∈ OneCohomology.fixed (σ.comp β.range.subtype)) :
        s.space.toRepresentation (κ (inclusion hYZ y)) w = w := by
      have hjw : j (Multiplicative.ofAdd w) ∈ U R z := by
        rw [←hjr]
        exact ⟨Multiplicative.ofAdd w,rfl⟩
      have hcentral : j (Multiplicative.ofAdd w) ∈ centralizer (Z R a : Set _) := by
        intro x hx
        have he := hw (⟨β ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩⟩ : β.range)
        change MovedSection.coverAction s e (β ⟨x,hx⟩) w = w at he
        have hh := hβ ⟨x,hx⟩ w
        rw [he] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh.symm
      have hQa : j (Multiplicative.ofAdd w) ∈ Q R a := by
        rw [←hCa]
        exact ⟨hZA (U_le_Z z hjw),hcentral⟩
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hκ]
      have hh := hyfix _ ⟨U_le_Z z hjw,hQa⟩
      change (y : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (y : FreeAmalgam R)⁻¹ = _
      rw [←hh,mul_inv_cancel_right]
    obtain ⟨t,ht,he⟩ := SymplecticNaturalNormalizer.mem_root_image_of_fixes_cover_seed B
      (hcent ▸ bot_le) hF (e.groupEquiv.trans d) ψ
      (fun b v => MovedSection.ambientAction_component s e b v)
      p hp β.range hP hd hc (κ (inclusion hYZ y))
      (s.space.toRepresentation (κ (inclusion hYZ y)))
      (fun w => MovedSection.coverProjection_ambient s e _ w) hfixed
    obtain ⟨x,rfl⟩ := ht
    refine ⟨x,?_⟩
    rw [←hβmark x]
    exact he
  apply le_antisymm
  · rintro y ⟨hy,hfix⟩
    obtain ⟨x,hx⟩ := hroot ⟨y,hy⟩ hfix
    let c : stabilizer R z := (inclusion hAZ x)⁻¹ * inclusion hYZ ⟨y,hy⟩
    have hk : c ∈ κ.ker := by
      change κ c=1
      simp only [c,map_mul,map_inv,hx,inv_mul_cancel]
    have hcQ : c.val ∈ Q R z := by
      rw [←hCz,←hκC]
      exact ⟨c,hk,rfl⟩
    have hcY : c.val ∈ Y := Y.mul_mem (Y.inv_mem (hZY x.property)) hy
    have hm := (Z R a ⊔ (Y ⊓ Q R z)).mul_mem (mem_sup_left x.property)
      (mem_sup_right ⟨hcY,hcQ⟩)
    change x.val * (x.val⁻¹ * y) ∈ _ at hm
    simpa only [mul_inv_cancel_left] using hm
  · apply sup_le
    · exact le_inf hZY
        ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)).trans
          (centralizer_le inf_le_right))
    · exact le_inf inf_le_left (inf_le_right.trans
        ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (geometry.centralizes z path.end_color))).trans (centralizer_le inf_le_left)))

end Model

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- At a field-sized critical pair the full Z-intersection has exactly
its original root and quotient kernel as pointwise fixer in any endpoint actor. -/
theorem Input.replacement_root_Z_intersection_centralizer
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hZY : Z d.radical a ≤ Y) (hYZ : Y ≤ stabilizer d.radical z) :
    Y ⊓ centralizer ((Z d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) =
      Z d.radical a ⊔ (Y ⊓ Q d.radical z) := by
  obtain ⟨hz,ha⟩ := h.replacement_small_critical_indices_eq_field d path hb hsmall
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  have hFc : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hAut : Nat.card (E.Carrier ≃+* E.Carrier) < Nat.card E.Carrier := by
    rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card E.Carrier = 2 ^ n by rw [E.card_eq,hE]),E.card_eq,hE]
    exact n.lt_two_pow_self
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hAZ κ hκQ).trans (hz.trans hFc.symm)
  have hδ : ∀ x : Z d.radical a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  have hCa := C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hcent := (h.replacement_component_image_structure d).2.2.2.2
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := critical_inner_root_actor_of_field path hb hCa hFl
    s e he hcent j hj hjr δ hδ hδcard (ha.trans hFc.symm) hAut
  have hCz := C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) z path.end_color
  exact root_intersection_fixed_kernel_of_cover path hb hCa hCz hFl s e he hcent
    j hj hjr κ hκC hconj β hAZ hβmark hβ hd hβcard Y hYZ hZY

/-- The same exact fixer formula holds on the whole X-intersection.
The retained central omega attachments are centralized by the full Q-kernel. -/
theorem Input.replacement_root_X_intersection_centralizer
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hZY : Z d.radical a ≤ Y) (hYZ : Y ≤ stabilizer d.radical z) :
    Y ⊓ centralizer ((X d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) =
      Z d.radical a ⊔ (Y ⊓ Q d.radical z) := by
  have hZX : Z d.radical z ≤ X d.radical z := geometry.omega_bound z path.end_color
    (by rwa [geometry.distance_constant z path.end_color])
  apply le_antisymm
  · exact (inf_le_inf_left Y (centralizer_le (inf_le_inf_right _ hZX))).trans_eq
      (h.replacement_root_Z_intersection_centralizer d path hb hsmall Y hZY hYZ)
  · apply sup_le
    · exact le_inf hZY
        ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)).trans
          (centralizer_le inf_le_right))
    · exact le_inf inf_le_left (inf_le_right.trans
        ((Q_le_centralizer_X d.radical z).trans (centralizer_le inf_le_left)))

/-- A trapped neighbor supplies every source premise for endpoint normalization
of the fixed kernel on the full X-intersection. The actual path, radical,
and full starting and neighboring Z-layers are retained. -/
theorem Input.replacement_trapped_root_endpoint_normalizes_fixed_kernel
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    let A := X d.radical z ⊓ Q d.radical a
    (Z d.radical v ⊔ Z d.radical a) ⊓ centralizer (A : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊔ ((Z d.radical v ⊔ Z d.radical a) ⊓ Q d.radical z) ∧
    Z d.radical z ≤ normalizer (((Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ⊔
      Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  dsimp only
  let Y := Z d.radical v ⊔ Z d.radical a
  let A := X d.radical z ⊓ Q d.radical a
  let D := (Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ⊔ Z d.radical a
  have hYV : Z d.radical v ≤ V d.radical a := le_sup_left.trans
    (neighbor_seed_join_le_radius hat hvt)
  have hvS : Z d.radical v ≤ stabilizer d.radical z :=
    (le_inf hYV htrap).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hvQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  obtain ⟨hi,_⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
    (by omega) (Z d.radical v) hvS hvQ hn
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2 := by
    rw [hi]
    nlinarith
  have haS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hcent := h.replacement_root_X_intersection_centralizer d path (by omega)
    hsmall Y le_sup_right (sup_le hvS haS)
  refine ⟨hcent,?_⟩
  have hYQ : Y ≤ Q d.radical a :=
    (neighbor_seed_join_le_radius hat hvt).trans
      (geometry.V_le_Q (by omega) a path.start_color)
  have hDQ : D ≤ Z d.radical a ⊔ (Y ⊓ Q d.radical z) := by
    apply sup_le _ le_sup_left
    exact (inf_le_inf le_sup_left le_rfl).trans_eq hcent
  have hna : Q d.radical a ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1).trans
      (Z_normalized d.radical a)
  have hc : ⁅Y ⊓ Q d.radical z,Z d.radical z⁆ = ⊥ := by
    rw [commutator_comm]
    exact le_bot_iff.mp ((commutator_mono le_rfl inf_le_right).trans
      (geometry.centralizes z path.end_color).le)
  apply le_normalizer_iff_commutator_le_left.mpr
  exact ((commutator_mono hDQ le_rfl).trans
    (commutator_sup_le_of_relative_normal (Q d.radical a) (Z d.radical a) (Y ⊓ Q d.radical z)
      (Z d.radical z) (Z d.radical a) hna (le_sup_right.trans hYQ) (inf_le_left.trans hYQ)
      (critical_commutator_le_start_seed path) (hc ▸ bot_le))).trans le_sup_right

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
