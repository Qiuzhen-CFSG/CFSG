module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwo

/-!
# The large-movement image comparison in MS93 (3.7)(2)

Suppose the opposite whole core moves more than q squared cosets of U.
The natural displacement then has dimension at least three. The reversed
source triple makes T₀ fix that displacement, so symplectic orthogonality
bounds its own displacement by one field dimension and its image order by q.
The complete central cover and its exact full-core kernel transport this
bound to [T₀ : T₀ ∩ Q′].

The common edge center lies in Q′, and Z = U Z_t retains its whole fixed
attachment. Thus the critical-image lower bound forces the T₀, U and Z
images in the opposite quotient all to have order q. Their images coincide,
and the source factorization T₀ = U (T₀ ∩ Q′) follows with relative normality
inside the original full radical. The reciprocal critical image also has
order q.

Together with the proved small-movement branch, this reduces (3.7)(2) to
its remaining large-movement fixed-core contradiction. In particular, the
quadratic action of the complete fixed attachment, the ensuing full-core
index estimates and the final field restriction are not asserted here.
Source: Meierfrankenfeld--Stellmacher (1993), printed p.873, the paragraph
beginning the large-movement case of (3.7)(2).
-/

public noncomputable section
open scoped commutatorElement IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover

private theorem cover_moving_index
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F))
    (hact : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹) :
    (centralizer (A : Set G)).relIndex U =
      Nat.card F ^ Module.finrank F
        (displacementSpace ((commutator (Sp F)).subtype.comp β).range) := by
  let α := (commutator (Sp F)).subtype.comp β
  have hi := embedded_centralizer_index σ U A j hj hjr β hact
  rw [fixedCodim_of_binaryCover p hp] at hi
  have hfixed : fixedSpace (binaryNatural (K := F)) β.range =
      (TwoLocalCover.fixedSpace α.range).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨a,rfl⟩ := hx
      exact hv ⟨β a,⟨a,rfl⟩⟩
    · intro hv x
      obtain ⟨a,ha⟩ := x.property
      change binaryNatural x.val v=v
      rw [←ha]
      exact hv (α a) ⟨a,rfl⟩
  rw [hi]
  change 2 ^ Module.finrank (ZMod 2)
    (Vector F ⧸ fixedSpace (binaryNatural (K := F)) β.range)=_
  rw [hfixed]
  have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
    (TwoLocalCover.fixedSpace α.range)).toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  rw [hc,fixed_quotient_card]

private theorem cover_large_movement_actor_bound
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (U A B : Subgroup G) (j : Multiplicative W →* G) (hj : Function.Injective j)
    (hjr : j.range=U) (β : A →* L (K := F)) (γ : B →* L (K := F))
    (hactA : ∀ (a : A) (w : W), j (Multiplicative.ofAdd (σ (β a) w))=
      a.val*j (Multiplicative.ofAdd w)*a.val⁻¹)
    (hactB : ∀ (b : B) (w : W), j (Multiplicative.ofAdd (σ (γ b) w))=
      b.val*j (Multiplicative.ofAdd w)*b.val⁻¹)
    (hlarge : Nat.card F^2 < (centralizer (A : Set G)).relIndex U)
    (htriple : ⁅⁅U,A⁆,B⁆=⊥) :
    Nat.card (((commutator (Sp F)).subtype.comp γ).range) ≤ Nat.card F := by
  let α := (commutator (Sp F)).subtype.comp β
  let δ := (commutator (Sp F)).subtype.comp γ
  have hAB : displacementSpace α.range ≤ TwoLocalCover.fixedSpace δ.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩ b hb
    change b • (a.val • v-v)=a.val • v-v
    obtain ⟨a,ha⟩ := a.property
    rw [←ha]
    obtain ⟨b,rfl⟩ := hb
    obtain ⟨w,rfl⟩ := hp.1 v
    have hval : j (Multiplicative.ofAdd (σ (β a) w-w)) =
        ⁅a.val,j (Multiplicative.ofAdd w)⁆ := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hactA]
      rfl
    have hc : b.val*⁅a.val,j (Multiplicative.ofAdd w)⁆ =
        ⁅a.val,j (Multiplicative.ofAdd w)⁆*b.val := by
      apply commutator_eq_bot_iff_le_centralizer.mp htriple
      · rw [commutator_comm]
        exact commutator_mem_commutator a.property (hjr ▸ ⟨_,rfl⟩)
      · exact b.property
    have he : σ (γ b) (σ (β a) w-w)=σ (β a) w-w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hactB,hval,hc,mul_inv_cancel_right]
    have hh := congrArg p he
    rw [p.isIntertwining,map_sub,p.isIntertwining] at hh
    exact hh
  rw [cover_moving_index σ p hp U A j hj hjr β hactA] at hlarge
  have hdim : 2 < Module.finrank F (displacementSpace α.range) :=
    (pow_lt_pow_iff_right₀ (Finite.one_lt_card : 1 < Nat.card F)).mp hlarge
  have hle := Submodule.finrank_mono hAB
  rw [←orthogonal_displacementSpace,
    LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate] at hle
  have hv : Module.finrank F (Theory.SpecificGroups.SymplecticFour.Vector F)=4 := by
    simp [Theory.SpecificGroups.SymplecticFour.Vector]
  rw [hv] at hle
  have hd := (displacementSpace δ.range).finrank_le
  rw [hv] at hd
  have hδ : Module.finrank F (displacementSpace δ.range) ≤ 1 := by omega
  exact (card_actor_le_displacement_dimension δ.range).trans
    (by simpa only [pow_one] using
      Nat.pow_le_pow_right (Nat.card_pos (α := F)) (show
        (Module.finrank F (displacementSpace δ.range))^2 ≤ 1 by nlinarith))

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- An actor fixing the large displacement has image of order at most q
in the actual endpoint quotient, with its entire two-core as kernel. -/
theorem moving_triple_index_le_of_large_movement
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    {z : Vertex d.radical} (hz : color d.radical z=false)
    (A B : Subgroup (FreeAmalgam d.radical))
    (hAS : A ≤ stabilizer d.radical z) (hBS : B ≤ stabilizer d.radical z)
    (hlarge : (2^n)^2 < (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z))
    (htriple : ⁅⁅U d.radical z,A⁆,B⁆=⊥) :
    (Q d.radical z).relIndex B ≤ 2^n := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d hz
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g hb)
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have haction (x : stabilizer d.radical z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  let βA := γ.comp (inclusion hAS)
  let βB := γ.comp (inclusion hBS)
  let αB := (commutator (Sp E.Carrier)).subtype.comp βB
  have hbound := cover_large_movement_actor_bound (MovedSection.coverAction s e)
    (MovedSection.coverProjection s e) he (U d.radical z) A B j hj hjr βA βB
    (fun a => haction (inclusion hAS a)) (fun b => haction (inclusion hBS b))
    (by simpa only [E.card_eq,hE] using hlarge) htriple
  have hk : αB.ker = (Q d.radical z).subgroupOf B := by
    have hkκ : κ.ker = (Q d.radical z).subgroupOf (stabilizer d.radical z) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    dsimp only [αB,βB,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.comp_assoc,MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      ←MonoidHom.comap_ker,MonoidHom.ker_codRestrict,hkκ,comap_inclusion_subgroupOf]
  have hi : (Q d.radical z).relIndex B = Nat.card αB.range := by
    rw [relIndex,←hk,index_ker]
  rw [hi]
  simpa only [E.card_eq,hE] using hbound

/-- Large whole-core movement identifies the component-radical, natural
and critical images in the opposite quotient, all with order q. The marked
image of the whole saturated radical has order q cubed or q to the fourth power. -/
theorem source_two_large_movement_images
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    (Q d.radical z).relIndex (componentRadical d a t) = 2^n ∧
      (Q d.radical z).relIndex (U d.radical a) = 2^n ∧
      (Q d.radical z).relIndex (Z d.radical a) = 2^n ∧
      componentRadical d a t ⊔ Q d.radical z = U d.radical a ⊔ Q d.radical z := by
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion c'.edge_le) (inclusion_injective _)
  let : ((Q d.radical z).subgroupOf (Q d.radical t)).Normal := c'.core_normal
  have hU₀ : U d.radical a ≤ componentRadical d a t :=
    (c.componentRadical_inf_core g hb path.start_color).symm.le.trans inf_le_left
  have hUT := hU₀.trans (show componentRadical d a t ≤ Q d.radical t from inf_le_left)
  have hZtQ : Z d.radical t ≤ Q d.radical z :=
    (Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt).trans
      ((g.omega_bound z path.end_color (by
        rw [g.distance_constant z path.end_color]; change 0 < g.b d.radical; omega)).trans
        (omegaCenter_le _))
  have hZa : Z d.radical a ≤ U d.radical a ⊔ Q d.radical z := by
    rw [Z_eq_moving_sup_edge_of_distance_two h d g hb path.start_color hat]
    exact sup_le_sup_left hZtQ _
  have hsup (B : Subgroup (FreeAmalgam d.radical)) (hBT : B ≤ Q d.radical t) :
      (Q d.radical z).relIndex (B ⊔ Q d.radical z) = (Q d.radical z).relIndex B := by
    rw [←relIndex_subgroupOf (sup_le hBT c'.core_le_edge),
      subgroupOf_sup hBT c'.core_le_edge,relIndex_sup_right,
      relIndex_subgroupOf hBT]
  have hfinite (B : Subgroup (FreeAmalgam d.radical)) (hBT : B ≤ Q d.radical t) :
      (Q d.radical z).relIndex B ≠ 0 := by
    let : Finite B := Finite.of_injective (inclusion hBT) (inclusion_injective _)
    exact index_ne_zero_of_finite
  have htriple := (paired_source_triples h d g hb hsat path hat hzt c c').2.1
  have hbound := moving_triple_index_le_of_large_movement h d g (by omega) path.end_color
    (Q d.radical a) (componentRadical d a t)
    (c.core_le_edge.trans c'.edge_le) (inf_le_left.trans c'.edge_le) hlarge
    (le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      htriple.le) bot_le)
  have hlow := (replacement_critical_indices_ge_field h d path (by omega)).1
  have hZU : (Q d.radical z).relIndex (Z d.radical a) ≤
      (Q d.radical z).relIndex (U d.radical a) := by
    have hh := relIndex_le_of_le_right hZa (hfinite _ (sup_le hUT c'.core_le_edge))
    rwa [hsup _ hUT] at hh
  have hU₀i := relIndex_le_of_le_right hU₀ (hfinite _ inf_le_left)
  have hUi : (Q d.radical z).relIndex (U d.radical a) = 2^n := by omega
  have h₀i : (Q d.radical z).relIndex (componentRadical d a t) = 2^n := by omega
  refine ⟨h₀i,hUi,by omega,?_⟩
  have hQX : Q d.radical z ≤ U d.radical a ⊔ Q d.radical z := le_sup_right
  have hXY : U d.radical a ⊔ Q d.radical z ≤ componentRadical d a t ⊔ Q d.radical z :=
    sup_le_sup_right hU₀ _
  have hm := relIndex_mul_relIndex (Q d.radical z)
    (U d.radical a ⊔ Q d.radical z) (componentRadical d a t ⊔ Q d.radical z) hQX hXY
  rw [hsup _ hUT,hsup (componentRadical d a t) inf_le_left,hUi,h₀i] at hm
  have hqi : (U d.radical a ⊔ Q d.radical z).relIndex
      (componentRadical d a t ⊔ Q d.radical z)=1 := by
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^n) (by simpa using hm)
  exact le_antisymm (relIndex_eq_one.mp hqi) hXY

/-- The literal source factorization T₀ = U (T₀ ∩ Q′) in the large-movement
case. Normality is used only within the common full radical. -/
theorem source_two_large_movement_component_factorization
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex (U d.radical z)) :
    componentRadical d a t = U d.radical a ⊔ (componentRadical d a t ⊓ Q d.radical z) := by
  have hU₀ : U d.radical a ≤ componentRadical d a t :=
    (c.componentRadical_inf_core g hb path.start_color).symm.le.trans inf_le_left
  have he := (source_two_large_movement_images h d g hb hsat path hat hzt c c' hlarge).2.2.2
  apply le_antisymm ?_ (sup_le hU₀ inf_le_left)
  intro x hx
  have hx' : x ∈ U d.radical a ⊔ Q d.radical z := he ▸ mem_sup_left hx
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    ((hU₀.trans inf_le_left).trans (c'.edge_le.trans (Q_normalized d.radical z)))] at hx'
  obtain ⟨u,hu,q,hq,rfl⟩ := hx'
  have hq₀ : q ∈ componentRadical d a t := by
    have hh := (componentRadical d a t).mul_mem
      ((componentRadical d a t).inv_mem (hU₀ hu)) hx
    simpa only [inv_mul_cancel_left] using hh
  exact mul_mem (mem_sup_left hu) (mem_sup_right ⟨hq₀,hq⟩)

/-- Either (3.7)(2)'s midpoint containment holds, or its remaining
large-movement branch has both actual critical images of order q and the
full component-radical factorization needed for the fixed-core comparison. -/
theorem source_two_reduction
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsat : (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 = d.radical)
    {a z t : Vertex d.radical} (path : CriticalPath d.radical g a z)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t) :
    ⁅Z d.radical z,Q d.radical a⁆ ≤ Z d.radical t ∨
      ((2^n)^2 < (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z) ∧
      (Q d.radical z).relIndex (componentRadical d a t) = 2^n ∧
      (Q d.radical z).relIndex (U d.radical a) = 2^n ∧
      (Q d.radical z).relIndex (Z d.radical a) = 2^n ∧
      (Q d.radical a).relIndex (Z d.radical z) = 2^n ∧
      componentRadical d a t ⊔ Q d.radical z = U d.radical a ⊔ Q d.radical z ∧
      componentRadical d a t = U d.radical a ⊔ (componentRadical d a t ⊓ Q d.radical z)) := by
  by_cases hm : (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ (2^n)^2
  · exact Or.inl (source_two_of_small_core_movement h d g hb hsat path hat hzt c c' hm)
  have hm := lt_of_not_ge hm
  obtain ⟨hT,hU,hZ,he⟩ := source_two_large_movement_images h d g hb hsat path hat hzt c c' hm
  have hother := (replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hZ]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  exact Or.inr ⟨hm,hT,hU,hZ,hother,he,
    source_two_large_movement_component_factorization h d g hb hsat path hat hzt c c' hm⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
