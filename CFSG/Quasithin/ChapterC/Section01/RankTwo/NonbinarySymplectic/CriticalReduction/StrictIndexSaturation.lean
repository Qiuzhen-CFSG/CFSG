module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexOrbit

/-!
# Whole-cover displacement from the actual quotient image

A local actor of U-fixed index at most q has image of order at most q
modulo the full Q-kernel. A contained actor of image order at least q
therefore has the same image and exactly the same displacement on the
whole Z-layer. This uses equality of quotient images, rather than a
claim that every nonzero displacement subgroup is the full displacement.

A subgroup moving the full fixed intersection in a natural cover has
fixed index at least q: the fixed preimage projects onto a field subspace,
and a proper fixed subspace has codimension at least one. The entire
vertex-fixed attachment extends this bound from U to Z. Identifying the
literal C(Z_alpha) with Q_alpha gives the critical-intersection bound.

These estimates feed the terminal orbit argument in StrictIndexTerminal.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), first orbit span in (5.9), printed p.920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
private theorem small_fixed_actor_card
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (A : Subgroup (Sp F))
    (hi : 2 ^ fixedCodim (restrictScalars (k := ZMod 2)
      (symplecticNatural (k := F) 2)) A ≤ Nat.card F) : Nat.card A ≤ Nat.card F := by
  let N := TwoLocalCover.fixedSpace A
  have hfixed : fixedSpace (restrictScalars (k := ZMod 2)
      (symplecticNatural (k := F) 2)) A=N.restrictScalars (ZMod 2) := by
    ext v
    exact ⟨fun hv x hx => hv ⟨x,hx⟩,fun hv x => hv x.val x.property⟩
  have he := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) N).toEquiv
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at he
  change 2 ^ Module.finrank (ZMod 2) (_ ⧸ fixedSpace _ A) ≤ _ at hi
  rw [hfixed,he] at hi
  change Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace A) ≤ Nat.card F at hi
  rw [fixed_quotient_card] at hi
  have hd : Module.finrank F (displacementSpace A) ≤ 1 := by
    exact (Nat.pow_le_pow_iff_right (show 1 < Nat.card F from Finite.one_lt_card)).mp
      (hi.trans_eq (pow_one _).symm)
  exact (card_actor_le_displacement_dimension A).trans
    ((Nat.pow_le_pow_right Nat.card_pos (show (Module.finrank F (displacementSpace A))^2 ≤ 1 by
      nlinarith)).trans_eq (pow_one _))

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A U-fixed index at most q bounds the image modulo the full Q-kernel. -/
theorem Input.replacement_field_fixed_index_image_bound
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ stabilizer d.radical a)
    (hi : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F) :
    (Q d.radical a).relIndex A ≤ Nat.card F := by
  obtain ⟨E,hE,f,hf,hfQ,hidx⟩ := h.replacement_inner_natural_indices d geometry hb ha
  let S := stabilizer d.radical a
  let A₀ := A.subgroupOf S
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have he := hidx A₀
  rw [←Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective,
    map_subgroupOf_eq_of_le hAS,map_subgroupOf_eq_of_le hUS] at he
  have hcard : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hbnd := small_fixed_actor_card (A₀.map f) (by rwa [←he,hcard])
  have hk : f.ker=(Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have heq : (Q d.radical a).relIndex A=Nat.card (A₀.map f) := by
    rw [←relIndex_subgroupOf (H := Q d.radical a) hAS,←hk,relIndex_ker]
  rw [heq,←hcard]
  exact hbnd


omit h [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem same_image_commutator
    {G : Type*} [Group G] (U A T Q : Subgroup G)
    (hA : A ≤ T) (hQ : Q ≤ centralizer (U : Set G))
    (hAQ : A ≤ normalizer (Q : Set G))
    (he : A ⊔ Q=T ⊔ Q) : ⁅U,A⁆=⁅U,T⁆ := by
  apply le_antisymm (commutator_mono le_rfl hA)
  apply commutator_le.mpr
  intro u hu t ht
  have ht' : t ∈ (A : Set G) * (Q : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right A Q hAQ,he]
    exact mem_sup_left ht
  obtain ⟨a,ha,q,hq,rfl⟩ := ht'
  have hc : ⁅u,q⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hQ hq u hu)
  rw [commutatorElement_mul_right_eq_mul_conj,hc,mul_one,mul_inv_cancel_right]
  exact commutator_mem_commutator hu ha

/-- A contained actor of image size at least q has the same image and whole-Z displacement as the original small-index actor. -/
theorem Input.replacement_field_index_actor_saturates
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (A T : Subgroup (FreeAmalgam d.radical)) (hAT : A ≤ T)
    (hTS : T ≤ stabilizer d.radical a)
    (hi : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F)
    (hlo : Nat.card F ≤ (Q d.radical a).relIndex A) :
    A ⊔ Q d.radical a=T ⊔ Q d.radical a ∧
      ⁅Z d.radical a,A⁆=⁅Z d.radical a,T⁆ := by
  obtain ⟨E,hE,f,hf,hfQ,hidx⟩ := h.replacement_inner_natural_indices d geometry hb ha
  let S := stabilizer d.radical a
  let A₀ := A.subgroupOf S
  let T₀ := T.subgroupOf S
  have hAS := hAT.trans hTS
  have hk : f.ker=(Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have heq (B : Subgroup (FreeAmalgam d.radical)) (hBS : B ≤ S) :
      Nat.card ((B.subgroupOf S).map f)=(Q d.radical a).relIndex B := by
    rw [←relIndex_ker,hk,relIndex_subgroupOf hBS]
  have hmaps : A₀.map f=T₀.map f := eq_of_le_of_card_ge (map_mono (comap_mono hAT))
    (by rw [heq T hTS,heq A hAS]; exact
      (h.replacement_field_fixed_index_image_bound d geometry hb ha T hTS hi).trans hlo)
  have hsup := congrArg (Subgroup.map S.subtype) (congrArg (Subgroup.comap f) hmaps)
  rw [comap_map_eq,comap_map_eq,Subgroup.map_sup,Subgroup.map_sup,
    map_subgroupOf_eq_of_le hAS,map_subgroupOf_eq_of_le hTS,hfQ] at hsup
  exact ⟨hsup,same_image_commutator _ _ _ _ hAT
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)))
    (hAS.trans (Q_normalized d.radical a)) hsup⟩

omit h [Group H] [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem covered_fixed_space_index_lower
    {E V G : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Group G]
    {σ : Representation (ZMod 2) (Representation.SymplecticFourOrthogonalCover.L (K := E)) V}
    (p : σ.IntertwiningMap (Representation.SymplecticFourOrthogonalCover.binaryNatural (K := E)))
    (hp : Representation.OneCohomology.IsCover p)
    (j : Multiplicative V →* G) (hj : Function.Injective j)
    (Y T : Subgroup G)
    (β : Y →* Representation.SymplecticFourOrthogonalCover.L (K := E))
    (γ : T →* Representation.SymplecticFourOrthogonalCover.L (K := E))
    (hact : ∀ y : Y, ∀ v : V, j (Multiplicative.ofAdd (σ (β y) v))=y.val*j (Multiplicative.ofAdd v)*y.val⁻¹)
    (hactT : ∀ t : T, ∀ v : V, j (Multiplicative.ofAdd (σ (γ t) v))=t.val*j (Multiplicative.ofAdd v)*t.val⁻¹)
    (hn : ⁅Y,j.range ⊓ centralizer (T : Set G)⁆≠⊥) :
    Nat.card E ≤ (centralizer (Y : Set G)).relIndex (j.range ⊓ centralizer (T : Set G)) := by
  let α := (commutator (Sp E)).subtype.comp β
  let τ := (commutator (Sp E)).subtype.comp γ
  let P := TwoLocalCover.fixedSpace τ.range
  let C := (TwoLocalCover.fixedSpace α.range).comap P.subtype
  let W := (P.restrictScalars (ZMod 2)).comap p.toLinearMap
  have hfixed (B : Subgroup G) (f : B →* Representation.SymplecticFourOrthogonalCover.L (K := E))
      (hactB : ∀ b : B, ∀ v : V, j (Multiplicative.ofAdd (σ (f b) v))=b.val*j (Multiplicative.ofAdd v)*b.val⁻¹)
      (v : V) : j (Multiplicative.ofAdd v) ∈ centralizer (B : Set G) ↔
        p v ∈ TwoLocalCover.fixedSpace ((commutator (Sp E)).subtype.comp f).range := by
    constructor
    · intro hv b hb
      obtain ⟨b,rfl⟩ := hb
      have hvf : σ (f b) v=v := by
        apply Multiplicative.ofAdd.injective
        apply hj
        rw [hactB,hv b.val b.property,mul_inv_cancel_right]
      exact (LinearMap.congr_fun (p.isIntertwining' (f b)) v).symm.trans (congrArg p hvf)
    · intro hv b hb
      have hh := Representation.SymplecticFourOrthogonalCover.cover_fixed_of_projection_fixed p hp
        (f ⟨b,hb⟩) v (hv _ ⟨⟨b,hb⟩,rfl⟩)
      have he := congrArg (fun v => j (Multiplicative.ofAdd v)) hh
      rw [hactB,mul_inv_eq_iff_eq_mul] at he
      exact he
  let jW := j.comp W.subtype.toAddMonoidHom.toMultiplicative
  have hWE : jW.range ≤ j.range ⊓ centralizer (T : Set G) := by
    rintro _ ⟨v,rfl⟩
    exact ⟨⟨_,rfl⟩,(hfixed T γ hactT v.toAdd.val).mpr v.toAdd.property⟩
  let pP : W →ₗ[ZMod 2] P := (p.toLinearMap.comp W.subtype).codRestrict
    (P.restrictScalars (ZMod 2)) (fun v => v.property)
  have hpP : Function.Surjective pP := by
    intro v
    obtain ⟨w,hw⟩ := hp.1 v.val
    refine ⟨⟨w, ?_⟩, Subtype.ext hw⟩
    change p w ∈ P
    rw [hw]
    exact v.property
  have hC : C≠⊤ := by
    intro he
    apply hn
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    rintro u ⟨⟨v,rfl⟩,hv⟩
    have hvP := (hfixed T γ hactT v.toAdd).mp hv
    have hvC : (⟨p v.toAdd,hvP⟩ : P) ∈ C := he ▸ Submodule.mem_top
    exact (hfixed Y β hact v.toAdd).mpr hvC
  have hlo : Nat.card E ≤ Nat.card (P ⧸ C) := by
    have hpos := Submodule.finrank_lt hC
    have hsum := C.finrank_quotient_add_finrank
    rw [Module.natCard_eq_pow_finrank (K := E) (V := P ⧸ C)]
    exact (pow_one (Nat.card E)).symm.trans_le
      (Nat.pow_le_pow_right Nat.card_pos (show 1 ≤ Module.finrank E (P ⧸ C) by omega))
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite j.range := Finite.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  let : Finite (j.range ⊓ centralizer (T : Set G) : Subgroup G) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hidx := quotient_card_le_centralizer_index_of_projection
    (j.range ⊓ centralizer (T : Set G)) Y jW hWE pP hpP (C.restrictScalars (ZMod 2))
    (fun v hv => (hfixed Y β hact v.val).mp hv)
  have hcard := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) C).toEquiv
  rw [hcard] at hidx
  exact hlo.trans hidx

open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open ChapterB.QuasisimpleSource MSCentralOrbit

/-- Nonzero movement of the full fixed U-intersection has index at least the original field size. -/
theorem Input.replacement_fixed_U_moving_index_lower
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {z : Vertex d.radical} (hz : color d.radical z=false)
    (Y T : Subgroup (FreeAmalgam d.radical))
    (hYS : Y ≤ stabilizer d.radical z) (hTS : T ≤ stabilizer d.radical z)
    (hn : ⁅Y,U d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical))⁆ ≠ ⊥) :
    Nat.card F ≤ (centralizer (Y : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical))) := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d hz
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let σ := MovedSection.coverAction s e
  have hact (y : stabilizer d.radical z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (γ y) w))=y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC y))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj y w
  have hh := covered_fixed_space_index_lower (MovedSection.coverProjection s e) he j hj
    Y T (γ.comp (inclusion hYS)) (γ.comp (inclusion hTS))
    (fun y w => hact (inclusion hYS y) w) (fun t w => hact (inclusion hTS t) w)
    (by rwa [hjr])
  rwa [hjr,hFc] at hh

/-- The same lower bound on the full Z-intersection retains all vertex-fixed attachments. -/
theorem Input.replacement_fixed_Z_moving_index_lower
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {z : Vertex d.radical} (hz : color d.radical z=false)
    (Y T : Subgroup (FreeAmalgam d.radical))
    (hYS : Y ≤ stabilizer d.radical z) (hTS : T ≤ stabilizer d.radical z)
    (hn : ⁅Y,Z d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical))⁆ ≠ ⊥) :
    Nat.card F ≤ (centralizer (Y : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical))) := by
  let D := Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  have hD : D ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans (Z_le_stabilizer d.radical z)).trans (U_normalized z)
  have hnU : ⁅Y,U d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical))⁆ ≠ ⊥ := by
    intro he
    apply hn
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    intro v hv
    have hvprod : v ∈ (U d.radical z : Set (FreeAmalgam d.radical)) * (D : Set _) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hD,←h.replacement_Z_eq_U_sup_fixed d geometry hb hz]
      exact hv.1
    obtain ⟨u,hu,c,hc,heq⟩ := hvprod
    have huT : u ∈ centralizer (T : Set (FreeAmalgam d.radical)) := by
      have hm := (centralizer (T : Set (FreeAmalgam d.radical))).mul_mem hv.2
        ((centralizer (T : Set (FreeAmalgam d.radical))).inv_mem (centralizer_le hTS hc.2))
      simpa only [←heq,mul_inv_cancel_right] using hm
    rw [←heq]
    exact (centralizer (Y : Set (FreeAmalgam d.radical))).mul_mem
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)) ⟨hu,huT⟩)
      (centralizer_le hYS hc.2)
  let := finite_Z d.radical z
  let : Finite (Z d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  exact (h.replacement_fixed_U_moving_index_lower d geometry hb hz Y T hYS hTS hnU).trans
    (relIndex_le_of_le_right (inf_le_inf_right _ (U_le_Z z)) index_ne_zero_of_finite)

/-- The actual critical intersection is the whole fixed Z-layer, with the literal C equals Q identification. -/
theorem Input.replacement_critical_intersection_moving_index_lower
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYS : Y ≤ stabilizer d.radical z)
    (hn : ⁅Y,Z d.radical z ⊓ Q d.radical a⁆ ≠ ⊥) :
    Nat.card F ≤ (centralizer (Y : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z ⊓ Q d.radical a) := by
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have he : Z d.radical z ⊓ Q d.radical a=
      Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [←hCa]
    ext x
    exact ⟨fun hx => ⟨hx.1,hx.2.2⟩,fun hx =>
      ⟨hx.1,path.endpoint_Z_le_start_stabilizer (by omega) hx.1,hx.2⟩⟩
  rw [he] at hn ⊢
  exact h.replacement_fixed_Z_moving_index_lower d geometry hb path.end_color Y (Z d.radical a) hYS
    (Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le) hn


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
