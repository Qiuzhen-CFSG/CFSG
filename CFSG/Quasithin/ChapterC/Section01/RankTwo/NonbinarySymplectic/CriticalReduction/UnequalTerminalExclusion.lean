module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.ContradictionGeometry

/-!
# Excluding unequal terminal movers above distance six

The actual unequal terminal sequence supplies a nonzero commutator of two
full critical kernels and field-sized critical images. Join the preceding
endpoint kernel with the critical endpoint seed. Both lie in the endpoint
radius group, which is abelian for b > 4. The starting seed normalizes that
radius group, so the joined actor acts quadratically on the full starting Z.

For b > 6, the radius centralizes the two endpoint seeds in the consecutive
selected generating pairs. The displacement's first-edge intersection
therefore propagates into the full starting vertex center. The faithful
cover bounds the joined actor's image by the field order. Its critical seed
already has that image order, so the two actors have the same fixed subgroup
on the full critical kernel. This contradicts the nonzero mutual commutator.
Together with the distance-six exclusion and evenness, this proves equality
of the neighboring smaller movers at the start of every critical path for
b > 4, retaining every central attachment and the literal edge kernels.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10), printed pp.922--923. The strict radius-image estimate and
commutator exclusions in (5.11), the distance-four argument (5.12), and the
actual minimum characteristic-replacement distance-two witness remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
private theorem embedded_quadratic
    {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (V A : Subgroup G) (σ : Representation (ZMod 2) D W)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range = V)
    (f : A →* D)
    (hact : ∀ (x : A) (w : W), j (Multiplicative.ofAdd (σ (f x) w)) =
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹)
    (hq : ⁅⁅V,A⁆,A⁆ = ⊥) :
    ∀ x ∈ f.range, ∀ y ∈ f.range, ∀ w : W,
      σ x (σ y w-w) = σ y w-w := by
  rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩ w
  have hjw : j (Multiplicative.ofAdd w) ∈ V := hjr ▸ (show _ ∈ j.range from ⟨_,rfl⟩)
  have hd : j (Multiplicative.ofAdd (σ (f y) w-w)) = ⁅y.val,j (Multiplicative.ofAdd w)⁆ := by
    rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
    rfl
  have hm : ⁅y.val,j (Multiplicative.ofAdd w)⁆ ∈ ⁅V,A⁆ := by
    rw [commutator_comm V A]
    exact commutator_mem_commutator y.property hjw
  have hc := (commutator_eq_bot_iff_le_centralizer.mp hq) hm x.val x.property
  apply Multiplicative.ofAdd.injective
  apply hj
  rw [hact,hd,hc,mul_inv_cancel_right]

private theorem embedded_natural_quadratic
    {G E W : Type*} [Group G] [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (V A : Subgroup G) (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : Function.Surjective p)
    (j : Multiplicative W →* G) (hj : Function.Injective j) (hjr : j.range=V)
    (f : A →* L (K := E))
    (hact : ∀ (x : A) (w : W), j (Multiplicative.ofAdd (σ (f x) w)) =
      x.val*j (Multiplicative.ofAdd w)*x.val⁻¹)
    (hq : ⁅⁅V,A⁆,A⁆=⊥) :
    let α := (commutator (Sp E)).subtype.comp f
    ∀ x ∈ α.range, ∀ y ∈ α.range, ∀ v : Vector E, x • (y • v-v)=y • v-v := by
  dsimp only
  have hqW := embedded_quadratic V A σ j hj hjr f hact hq
  rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩ v
  obtain ⟨w,rfl⟩ := hp v
  have hh := congrArg p (hqW _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ w)
  change binaryNatural (f x) (binaryNatural (f y) (p w)-p w) =
    binaryNatural (f y) (p w)-p w
  simpa only [map_sub,p.isIntertwining] using hh

private theorem embedded_fixed_mem_omegaCenter
    {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (T : Subgroup G) (j : Multiplicative W →* G)
    (hjT : j.range ≤ T) (σ : Representation (ZMod 2) D W) (β : T →* D)
    (hact : ∀ (a : T) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (w : W) (hw : ∀ y : T, σ (β y) w=w)
    (hp : j (Multiplicative.ofAdd w)^2=1) :
    j (Multiplicative.ofAdd w) ∈ omegaCenter T := by
  apply mem_omegaCenter_iff.mpr
  refine ⟨hjT ⟨_,rfl⟩,hp,?_⟩
  intro y hy
  have hh := (hact ⟨y,hy⟩ w).symm.trans
    (congrArg (fun w => j (Multiplicative.ofAdd w)) (hw ⟨y,hy⟩))
  exact mul_inv_eq_iff_eq_mul.mp hh

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

-- As in TerminalIndices, the literal full-cover coordinate application
-- needs a local allowance; the generic lemmas and terminal exclusions use
-- the default budget.
set_option maxHeartbeats 400000 in
/-- A quadratic actor in the literal edge kernel has at most field-sized
image if its full displacement meets the edge seed only in the vertex center. -/
theorem Input.replacement_quadratic_edge_actor_index_le_field
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAT : A ≤ Q d.radical t)
    (hq : ⁅⁅Z d.radical a,A⁆,A⁆=⊥)
    (hcentral : ⁅Z d.radical a,A⁆ ⊓ Z d.radical t ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    (Q d.radical a).relIndex A ≤ Nat.card F := by
  let T := Q d.radical t
  have ht : color d.radical t=true := by
    have hn := adjacent_color_ne d.radical hat
    rw [ha] at hn
    cases hh : color d.radical t <;> simp_all
  have hTS : T ≤ stabilizer d.radical a := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hUT : U d.radical a ≤ T := by
    obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) ha hat
    apply (U_le_Z a).trans
    apply ((Z_le_VBall d.radical a 2).trans (geometry.V_le_Q (by omega) a ha)).trans
    rw [←hiQ,show T=Q d.radical t from rfl,←hiR]
    exact map_mono (h.replacement_core_le d)
  let := finite_stabilizer d.radical t
  let : Finite T := Finite.of_injective
    (inclusion (show T ≤ stabilizer d.radical t from fun _ hx => hx.1)) (inclusion_injective _)
  have hT : IsPGroup 2 T := by
    obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) ha hat
    rw [show T=Q d.radical t from rfl,←hiR]
    exact (h.replacement_two_group d).map i
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d ha
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let β := (e.groupEquiv.toMonoidHom.comp κC).comp (inclusion hTS)
  let α := (commutator (Sp E.Carrier)).subtype.comp (β.comp (inclusion hAT))
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hact (y : T) (w : s.space.toSubmodule) : j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hTS y)))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hTS y) w
  let : IsElementaryAbelian 2 (Z d.radical a) := geometry.Z_elementary (by omega) a ha
  have hfixed (w : s.space.toSubmodule) (hw : ∀ y : T, σ (β y) w=w) :
      j (Multiplicative.ofAdd w) ∈ Z d.radical t := by
    rw [Z,if_neg (by simp [ht])]
    apply embedded_fixed_mem_omegaCenter T j (hjr.le.trans hUT) σ β hact w hw
    exact elemPow_eq_one_of_isElementaryAbelian _ (U_le_Z a (hjr ▸ ⟨_,rfl⟩))
  have hcentral' : ⁅A,U d.radical a⁆ ⊓ Z d.radical t ≤
      centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_trans _ (hcentral.trans (centralizer_le (Ltilde_le_stabilizer a)))
    rw [commutator_comm A]
    exact inf_le_inf_right _ (commutator_mono (U_le_Z a) le_rfl)
  have hquad : ∀ x ∈ α.range, ∀ y ∈ α.range, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    have hqU : ⁅⁅U d.radical a,A⁆,A⁆=⊥ := le_bot_iff.mp
      ((commutator_mono (commutator_mono (U_le_Z a) le_rfl) le_rfl).trans_eq hq)
    exact embedded_natural_quadratic (U d.radical a) A σ p he.1 j hj hjr
      (β.comp (inclusion hAT)) (fun x w => hact (inclusion hAT x) w) hqU
  have hbound := embedded_actor_card_le_of_central_fixed_intersection (F := E.Carrier)
    (W := s.space.toSubmodule) (G := FreeAmalgam d.radical) σ p he
    (U d.radical a) A T (centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)))
    (Z d.radical t) hT hAT j hjr β hact hker hfixed hcentral' hquad
  have hk : α.ker=(Q d.radical a).subgroupOf A := by
    ext x
    change ((e.groupEquiv (κC (inclusion hTS (inclusion hAT x)))).val=1) ↔ x.val ∈ Q d.radical a
    rw [show ∀ u : L (K := E.Carrier), (u.val=1 ↔ u=1) from fun u => ⟨fun hu => Subtype.ext hu,fun hu => congrArg Subtype.val hu⟩,
      e.groupEquiv.map_eq_one_iff]
    have heq : κC (inclusion hTS (inclusion hAT x))=1 ↔
        inclusion hTS (inclusion hAT x) ∈ κ.ker := Subtype.ext_iff
    rw [heq]
    constructor
    · intro hx
      exact hκQ ▸ mem_map_of_mem (stabilizer d.radical a).subtype hx
    · intro hx
      obtain ⟨y,hy,hyx⟩ := hκQ.symm ▸ hx
      have he : y=inclusion hTS (inclusion hAT x) := Subtype.ext hyx
      exact he ▸ hy
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hbound' : (Q d.radical a).relIndex A ≤ Nat.card F := by
    rw [←index_ker,hk,hFc] at hbound
    exact hbound
  exact hbound'


omit h in
private theorem centralizes_of_relative_index_bound
    {G : Type*} [Group G] (A B Q E : Subgroup G) [Finite A]
    (hBA : B ≤ A) (hQC : Q ≤ centralizer (E : Set G))
    (hBC : B ≤ centralizer (E : Set G))
    (hi : Q.relIndex A ≤ Q.relIndex B) : A ≤ centralizer (E : Set G) := by
  let : Finite B := Finite.of_injective (inclusion hBA) (inclusion_injective _)
  let : Finite (centralizer (E : Set G) ⊓ A : Subgroup G) :=
    Finite.of_injective (inclusion inf_le_right) (inclusion_injective _)
  have hlo := Q.relIndex_le_of_le_right (le_inf hBC hBA) index_ne_zero_of_finite
  have hmul := relIndex_inf_mul_relIndex Q (centralizer (E : Set G)) A
  rw [inf_of_le_left hQC] at hmul
  have hp : 0 < Q.relIndex B := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hc : 0 < (centralizer (E : Set G)).relIndex A :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  apply relIndex_eq_one.mp
  nlinarith

/-- Above distance six the actual unequal terminal paths yield a quadratic
joined actor with the same image as their critical endpoint. It therefore
fixes the full critical kernel, contradicting the nonzero mutual commutator. -/
theorem Input.replacement_mover_agreement_of_six_lt
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 6 < geometry.b d.radical) : pathMoverAgreement (Nat.card F) p 0 := by
  by_contra hne
  have hb4 : 4 < geometry.b d.radical := by omega
  obtain ⟨s,hs0,hs,hsne,hover,hindices,hnotB,hdisp⟩ :=
    h.replacement_unequal_terminal_normalizer_escape d p hb4 hne
  let a := (s 3).first
  let z := (s 3).last
  let c := (s 2).first
  let e := (s 2).last
  let E := Z d.radical a ⊓ Q d.radical z
  let A := (Z d.radical e ⊓ Q d.radical c) ⊔ Z d.radical z
  obtain ⟨w,hw,hcw,haw,hfirst⟩ := (hs 2).choice
  obtain ⟨v,hv,hcv₀,hcv,hfirst₀⟩ := (hs 1).choice
  obtain ⟨y,hy,hyv,hyw,hidx⟩ := hw.1
  have he := (hs 1).overlap 0 (by omega)
  simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he
  rw [he] at hyv
  have hwcol : color d.radical w=true := by
    have hn := adjacent_color_ne d.radical hcw
    rw [(s 2).path.start_color] at hn
    cases hh : color d.radical w <;> simp_all
  have hze : (cosetGraph d.radical).dist z e=2 :=
    shifted_last_distance (unequalPathChoice geometry (Nat.card F)) s hs 2 1 (by omega)
  have hzf : (cosetGraph d.radical).dist z (s 1).last=4 :=
    shifted_last_distance (unequalPathChoice geometry (Nat.card F)) s hs 1 2 (by omega)
  have heVz : Z d.radical e ≤ V d.radical z :=
    le_iSup_of_le e (le_iSup_of_le (by rw [SimpleGraph.dist_comm,hze]) le_rfl)
  have hAV : A ≤ V d.radical z :=
    sup_le (inf_le_left.trans heVz) (Z_le_VBall d.radical z 2)
  have haSz : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a (s 3).path.start_color)
      (s 3).path.critical.1.le
  have hDV : ⁅Z d.radical a,A⁆ ≤ V d.radical z :=
    (commutator_mono le_rfl hAV).trans
      (le_normalizer_iff_commutator_le_right.mp (haSz.trans (DistanceEight.V_normalized d.radical z)))
  have hVCV : V d.radical z ≤ centralizer (V d.radical z : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff_isMulCommutative.mpr
      (V_abelian_of_four_lt d.radical (s 3).path.end_color hb4)
  have hquad : ⁅⁅Z d.radical a,A⁆,A⁆=⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hDV.trans (hVCV.trans (centralizer_le hAV)))
  have hVzCe : V d.radical z ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (seed_centralizes_radius_of_distance geometry
      (s 2).path.end_color (s 3).path.end_color (by rw [SimpleGraph.dist_comm,hze]; omega))
  have hVzCf : V d.radical z ≤ centralizer (Z d.radical (s 1).last : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (seed_centralizes_radius_of_distance geometry
      (s 1).path.end_color (s 3).path.end_color (by rw [SimpleGraph.dist_comm,hzf]; omega))
  have hgenC : stabilizer d.radical c ≤ Q d.radical w ⊔ Z d.radical e := hw.2.1.ge
  have hgen₀ : stabilizer d.radical (s 1).first ≤ Q d.radical v ⊔ Z d.radical (s 1).last := hv.2.1.ge
  have hcentral : ⁅Z d.radical a,A⁆ ⊓ Z d.radical w ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) :=
    (central_intersection_propagates (⁅Z d.radical a,A⁆ ⊓ Z d.radical w)
      hwcol hcw hcv inf_le_right (inf_le_left.trans (hDV.trans hVzCe))
      (inf_le_left.trans (hDV.trans hVzCf)) hgenC hgen₀ y
      (Ltilde_le_stabilizer _ hy) hyv.symm).2.2
  have hzQw : Z d.radical z ≤ Q d.radical w := by
    apply Z_le_Q_of_dist_lt _ z (geometry.exists_critical z (s 3).path.end_color)
    rw [geometry.distance_constant z (s 3).path.end_color,SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist w (s 3).last < geometry.b d.radical
    rw [←hfirst,(s 3).path.dist_end,(s 3).path.length_eq_b]
    omega
  have hAT : A ≤ Q d.radical w :=
    sup_le (inf_le_right.trans (Q_le_adjacent_h d.radical hwcol hcw)) hzQw
  have hbound := h.replacement_quadratic_edge_actor_index_le_field d geometry hb4.le
    (s 3).path.start_color haw A hAT hquad hcentral
  have hQCE : Q d.radical a ≤ centralizer (E : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a (s 3).path.start_color))).trans (centralizer_le inf_le_left)
  have hzCE : Z d.radical z ≤ centralizer (E : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (inf_le_right.trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical z (s 3).path.end_color))))
  let := finite_stabilizer d.radical w
  let : Finite A := Finite.of_injective
    (inclusion (hAT.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hAC := centralizes_of_relative_index_bound A (Z d.radical z) (Q d.radical a) E
    le_sup_right hQCE hzCE (by rw [(hindices 1).2]; exact hbound)
  have hbot : ⁅E,Z d.radical e ⊓ Q d.radical c⁆=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact le_centralizer_iff.mp (le_sup_left.trans hAC)
  exact (hdisp 0).2.1 hbot

/-- At every nonbinary degree, neighboring movers agree at the start of
any critical path of length greater than four. -/
theorem Input.replacement_mover_agreement_of_four_lt
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) : pathMoverAgreement (Nat.card F) p 0 := by
  by_contra hne
  have hn6 := h.replacement_unequal_distance_ne_six d p hne
  have heven : Even (geometry.b d.radical) := geometry.even (alpha d.radical) rfl
  obtain ⟨k,hk⟩ := heven
  exact hne (h.replacement_mover_agreement_of_six_lt d p (by omega))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
