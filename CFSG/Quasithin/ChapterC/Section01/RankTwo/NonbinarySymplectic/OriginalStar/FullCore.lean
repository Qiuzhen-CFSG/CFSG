module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.OriginalCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.WholeKernel

/-!
# The full original core as a naturally marked dual cover

The distance-two replacement identifies the full original commutator core
with U. Since this layer is central elementary, the quotient Q/C_Q(L) is
an elementary module. The three-subgroups identity makes Q act trivially
on that quotient, so the action descends through the literal original
vertex quotient. Perfectness removes its component-fixed vectors.

The original natural-cover projection and the full-core coordinate map
have the same kernel on U. They therefore embed the natural module as a
dual cover in the full quotient, retaining the entire fixed attachment.
The actual original critical actor admits no invariant quadratic refinement;
applying the dual-cover fixed-vector theorem gives C_Q(Z') <= U C_Q(L).

This constructs the full-core dual-module input used in the opening of
MS93 (3.7), printed p.872, from the established (3.6) core comparison.
The distance-two premise belongs only to the characteristic replacement;
no transfer of that distance or radical saturation to the original graph
is assumed. The two small normal seed factors and marked-star preservation
remain separate source obligations.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The whole two-core admits the original local quotient action after dividing
by its full fixed subgroup; no elementary structure of the two-core is assumed. -/
theorem original_wholeKernelQuotient_over
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex R} (ha : color R a = false)
    {J : Type*} [Group J] (κ : stabilizer R a →* J)
    (hκ : Function.Surjective κ)
    (hκQ : κ.ker.map (stabilizer R a).subtype = Q R a) :
    ∃ s : WholeKernelQuotient R a J, s.quotient = κ := by
  let S := stabilizer R a
  let A := Q R a
  let L₀ := Ltilde R a
  let U₀ := U R a
  let C₀ := A ⊓ centralizer (L₀ : Set (FreeAmalgam R))
  have hAS : A ≤ S := fun _ hx => hx.1
  have hLS : L₀ ≤ S := Ltilde_le_stabilizer _
  have hSL : S ≤ normalizer (L₀ : Set (FreeAmalgam R)) := by
    have ht := le_normalizer_map (H := pResidual 2 S) S.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
    exact ht
  have hSN : S ≤ normalizer (C₀ : Set (FreeAmalgam R)) :=
    (le_inf (Q_normalized R a)
      (hSL.trans (normalizer_le_normalizer_centralizer L₀))).trans
      inf_normalizer_le_normalizer_inf
  let : (C₀.subgroupOf A).Normal :=
    normal_subgroupOf_of_le_normalizer (hAS.trans hSN)
  have hN : C₀.subgroupOf A =
      (centralizer (L₀ : Set (FreeAmalgam R))).subgroupOf A := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨x.property,hx⟩⟩
  let : ((centralizer (L₀ : Set (FreeAmalgam R))).subgroupOf A).Normal :=
    hN ▸ inferInstance
  have hmove : ⁅A,L₀⁆ ≤ U₀ := (original_core_eq_U_of_distance_two_replacement h d g hb ha).le
  have hc : U₀ ≤ centralizer (A : Set (FreeAmalgam R)) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (le_antisymm ((commutator_mono (U_le_Z a) le_rfl).trans_eq
        (Z_centralizes_Q R a ha)) bot_le)
  let : IsElementaryAbelian 2 U₀ := h.vertex_moving_elementary ha
  let : IsElementaryAbelian 2
      (A ⧸ (centralizer (L₀ : Set (FreeAmalgam R))).subgroupOf A) :=
    central_displacement_quotient_elementary A L₀ U₀ hmove hc
  let : IsElementaryAbelian 2 (A ⧸ C₀.subgroupOf A) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.quotientMulEquivOfEq hN).symm.toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hN).symm.surjective
  have hrot : ⁅⁅A,L₀⁆,A⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hmove.trans hc)
  have hAA : ⁅A,A⁆ ≤ centralizer (L₀ : Set (FreeAmalgam R)) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_commutator_eq_bot_of_rotate hrot (by rwa [commutator_comm L₀ A]))
  obtain ⟨σ,c,_⟩ := BinaryConjugationSection.exists_descended_actor S A C₀ hAS inf_le_left
    (Q_normalized R a) hSN κ hκ (by
      intro x hx y hy
      have hxA : (x : FreeAmalgam R) ∈ A :=
        by
          change (x : FreeAmalgam R) ∈ Q R a
          rw [←hκQ]
          exact mem_map_of_mem S.subtype hx
      have hm := commutator_mem_commutator hxA hy
      exact ⟨(Subgroup.commutator_le_sup A A |>.trans (sup_idem A).le) hm,hAA hm⟩)
  let : Group.IsPerfect K := h.component.perfect
  let : Group.IsPerfect L₀ := by
    obtain ⟨v,rfl⟩ := exists_mVertex_of_color R ha
    have hv : mVertex R v = act R v (alpha R) := by
      simp [alpha,act_mVertex]
    have he : L₀ = (K.map (embedM R)).map
        (MulAut.conj v⁻¹).toMonoidHom := by
      dsimp only [L₀]
      rw [hv,Ltilde_act,Ltilde_alpha,h.residual_eq]
    let : Group.IsPerfect (K.map (embedM R)) := Group.IsPerfect.map _
    exact he.symm ▸ Group.IsPerfect.map _
  have hfixed := BinaryConjugationSection.fixed_section_eq_bot S A L₀ hLS
    (hAS.trans hSL) κ σ c
  let : Finite S := finite_stabilizer _ _
  let : Finite A := Finite.of_injective (inclusion hAS) (inclusion_injective _)
  exact ⟨{
    Carrier := Additive (A ⧸ C₀.subgroupOf A)
    quotient := κ
    quotient_surjective := hκ
    quotient_kernel := hκQ
    action := σ
    sectionData := c
    fixed_eq_bot := hfixed },rfl⟩

omit h d [Finite H] in
private theorem original_wholeKernelDualCover_of_marked_cover
    {E J V : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (a : Vertex R) (s₀ : MovedSection ρ B)
    (e : ActionEquiv (s₀.action.comp B.subtype) (binaryNatural (K := E)))
    (he : IsCover (MovedSection.coverProjection s₀ e))
    (j : Multiplicative s₀.space.toSubmodule →* FreeAmalgam R)
    (hjr : j.range = U R a)
    (s : WholeKernelQuotient R a J)
    (hκL : ((Ltilde R a).subgroupOf
      (stabilizer R a)).map s.quotient = B)
    (hconj : ∀ (g : stabilizer R a) (v : s₀.space.toSubmodule),
      j (Multiplicative.ofAdd (s₀.space.toRepresentation (s.quotient g) v)) =
        (g : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam R)⁻¹)
    (hker : ∀ v : s₀.space.toSubmodule, MovedSection.coverProjection s₀ e v = 0 ↔
      j (Multiplicative.ofAdd v) ∈
        centralizer (Ltilde R a : Set (FreeAmalgam R)))
    (hZQ : Z R a ≤ Q R a)
    (hcomm : ⁅Q R a,Ltilde R a⁆ ≤
      U R a) :
    let γ : L (K := E) →* J := B.subtype.comp e.groupEquiv.symm.toMonoidHom
    ∃ i : (binaryNatural (K := E)).IntertwiningMap (s.action.comp γ),
      Function.Injective i ∧ IsDualCover i.range ∧
      ∀ w, w ∈ i.toLinearMap.range ↔
        ∃ x : Q R a, (x : FreeAmalgam R) ∈
          U R a ∧ (s.sectionData.coordinates x).toAdd = w := by
  let γ : L (K := E) →* J := B.subtype.comp e.groupEquiv.symm.toMonoidHom
  have hγ : γ.range = B := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.groupEquiv.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  let L₀ := Ltilde R a
  let S := stabilizer R a
  have hLS : L₀ ≤ S := Ltilde_le_stabilizer _
  let f₀ : L₀ →* B := (s.quotient.comp (inclusion hLS)).codRestrict B (by
    intro l
    exact hκL.le (mem_map_of_mem s.quotient (show inclusion hLS l ∈ L₀.subgroupOf S from l.property)))
  have hf₀ : Function.Surjective f₀ := by
    intro c
    obtain ⟨l,hl,he⟩ := (hκL.symm ▸ c.property : c.val ∈ (L₀.subgroupOf S).map s.quotient)
    exact ⟨⟨l.val,hl⟩,Subtype.ext he⟩
  let f := e.groupEquiv.toMonoidHom.comp f₀
  have hf : Function.Surjective f := e.groupEquiv.surjective.comp hf₀
  have hγf (l : L₀) : γ (f l) = s.quotient (inclusion hLS l) := by
    change (e.groupEquiv.symm (e.groupEquiv (f₀ l)) : J) = _
    rw [e.groupEquiv.symm_apply_apply]
    rfl
  let σ := s.action.comp γ
  let π := s.sectionData.coordinates
  have hUA : U R a ≤ Q R a :=
    (U_le_Z _).trans hZQ
  have hLA : L₀ ≤ normalizer (Q R a : Set (FreeAmalgam R)) :=
    hLS.trans (Q_normalized _ _)
  have hact (l : L₀) (a : Q R a) :
      (π ⟨(l : FreeAmalgam R)*a*(l : FreeAmalgam R)⁻¹,
        (mem_normalizer_iff.mp (hLA l.property) a).mp a.property⟩).toAdd =
          σ (f l) (π a).toAdd := by
    change _ = s.action (γ (f l)) (π a).toAdd
    rw [hγf]
    exact s.sectionData.equivariant (inclusion hLS l) a
  have hjact (l : L₀) (v : s₀.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s₀ e (f l) v)) =
        (l : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(l : FreeAmalgam R)⁻¹ := by
    change j (Multiplicative.ofAdd (s₀.space.toRepresentation (γ (f l)) v)) = _
    rw [hγf]
    exact hconj (inclusion hLS l) v
  have hkernel (v : s₀.space.toSubmodule) : MovedSection.coverProjection s₀ e v = 0 ↔
      π ⟨j (Multiplicative.ofAdd v),hUA (hjr ▸ ⟨Multiplicative.ofAdd v,rfl⟩)⟩ = 1 := by
    have hvU : j (Multiplicative.ofAdd v) ∈ U R a :=
      hjr ▸ ⟨Multiplicative.ofAdd v,rfl⟩
    have hvQ : j (Multiplicative.ofAdd v) ∈ Q R a :=
      hUA hvU
    apply (hker v).trans
    exact (show (j (Multiplicative.ofAdd v) ∈ centralizer (L₀ : Set (FreeAmalgam R))) ↔
      j (Multiplicative.ofAdd v) ∈ Q R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))
      from ⟨fun hv => ⟨hUA hvU,hv⟩,fun hv => hv.2⟩).trans
      (s.sectionData.coordinates_eq_one_iff ⟨j (Multiplicative.ofAdd v),hUA hvU⟩).symm
  have hmap : ((Ltilde R a).subgroupOf S).map s.quotient = B := by
    exact hκL
  have hfixed : OneCohomology.fixed σ = ⊥ := by
    apply bot_unique
    intro v hv
    apply s.fixed_eq_bot.le
    intro c
    have hc : c.val ∈ B := hmap.le c.property
    obtain ⟨g,hg⟩ := (hγ.symm ▸ hc : c.val ∈ γ.range)
    change s.action c.val v = v
    rw [←hg]
    exact hv g
  obtain ⟨i,hi,hdual,_,hrange⟩ := exists_dualCover_of_conjugation_section
    (Q R a) (U R a) L₀ hUA hLA
    hcomm
    (MovedSection.coverAction s₀ e) σ (binaryNatural (K := E))
    (MovedSection.coverProjection s₀ e) he.1 j hjr π s.sectionData.onto f hf hjact hact hkernel hfixed
  exact ⟨i,hi,hdual,hrange⟩


/-- The full original two-core modulo its entire fixed factor is a dual
cover of the naturally marked module. Every original critical endpoint
supplies a refinement-free actor under this very same marking. -/
theorem original_wholeKernel_natural_dualCover
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a : Vertex R} (ha : color R a = false) :
    ∃ E : BinaryField, E.degree = n ∧
    ∃ s : WholeKernelQuotient R a (H ⧸ pCore 2 H),
    ∃ γ : L (K := E.Carrier) →* (H ⧸ pCore 2 H),
      Function.Injective γ ∧
      γ.range = K.map (QuotientGroup.mk' (pCore 2 H)) ∧
      ((Ltilde R a).subgroupOf (stabilizer R a)).map s.quotient = γ.range ∧
    ∃ i : (binaryNatural (K := E.Carrier)).IntertwiningMap (s.action.comp γ),
      Function.Injective i ∧ IsDualCover i.range ∧
      (∀ w, w ∈ i.toLinearMap.range ↔
        ∃ x : Q R a, (x : FreeAmalgam R) ∈ U R a ∧
          (s.sectionData.coordinates x).toAdd = w) ∧
      ∀ (geometry : Geometry R), 0 < geometry.b R →
        ∀ (z : Vertex R) (_path : CriticalPath R geometry z a),
          ∃ β : Z R z →* L (K := E.Carrier),
            (∀ (x : Z R z) (hx : (x : FreeAmalgam R) ∈ stabilizer R a),
              γ (β x) = s.quotient ⟨x,hx⟩) ∧
            ¬ ∃ c : Natural (K := E.Carrier), ∀ b : β.range, ∀ v,
              Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors.refinement c
                (binaryNatural b.val v) =
              Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors.refinement c v := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let C₀ := K.map q
  let : C₀.Normal := h.component_image_structure.2.1
  let ρ₀ := NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)
  let s₀ := MovedSection.ofNormal ρ₀ C₀
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex ha
  change ActionEquiv (s₀.action.comp C₀.subtype) (binaryNatural (K := E.Carrier)) at e
  change IsCover (MovedSection.coverProjection s₀ e) at he
  change Multiplicative s₀.space.toSubmodule →* FreeAmalgam R at j
  obtain ⟨s,hs⟩ := original_wholeKernelQuotient_over h d g hb ha κ hκ hκQ
  let γ : L (K := E.Carrier) →* (H ⧸ pCore 2 H) :=
    C₀.subtype.comp e.groupEquiv.symm.toMonoidHom
  have hγ : γ.range = C₀ := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.groupEquiv.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hγinj : Function.Injective γ := Subtype.val_injective.comp e.groupEquiv.symm.injective
  obtain ⟨geometry,hpos,_⟩ := h.positive_even_geometry
  have hZQ : Z R a ≤ Q R a :=
    (geometry.omega_bound a ha (by
      rw [geometry.distance_constant a ha]
      exact hpos)).trans (omegaCenter_le _)
  obtain ⟨i,hi,hdual,hrange⟩ := original_wholeKernelDualCover_of_marked_cover a s₀ e he j hjr s
    (by rw [hs]; exact hκL) (by intro x v; rw [hs]; exact hconj x v) hker hZQ
    (original_core_eq_U_of_distance_two_replacement h d g hb ha).le
  refine ⟨E,hE,s,γ,hγinj,hγ,?_,i,hi,hdual,hrange,?_⟩
  · rw [hs,hγ]
    exact hκL
  · intro geometry hpos z path
    obtain ⟨β,hβmark,hβno⟩ := h.original_refinement_free_inner_actor (ρ := ρ₀) (B := C₀)
      (show Nat.card E.Carrier = Nat.card F by rw [E.card_eq,hE,h.field_card]) path hpos
      s₀ e he h.component_image_structure.2.2.2.2 j hj hjr κ hκQ hconj
    exact ⟨β,fun x hx => by rw [hs]; exact hβmark x hx,hβno⟩

/-- The dual-module argument applies to the full original core: its
centralizer of an original critical endpoint lies in the natural layer
with the complete fixed factor. The only distance-two premise belongs
to the supplied characteristic replacement. -/
theorem original_critical_core_centralizer_le_moving_fixed
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {geometry : Geometry R} (hpos : 0 < geometry.b R)
    {a z : Vertex R} (path : CriticalPath R geometry z a) :
    Q R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)) ≤
      U R a ⊔ fixedCore R a := by
  obtain ⟨E,hE,s,γ,hγ,hγC,hmap,i,hi,hdual,hrange,hcritical⟩ :=
    original_wholeKernel_natural_dualCover h d g hb path.end_color
  obtain ⟨β,hβ,hno⟩ := hcritical geometry hpos z path
  have hZS : Z R z ≤ stabilizer R a :=
    Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.start_color) path.critical.1.le
  intro b hbB
  let bA : Q R a := ⟨b,hbB.1⟩
  have hfix : (s.sectionData.coordinates bA).toAdd ∈
      OneCohomology.fixed ((s.action.comp γ).comp β.range.subtype) := by
    rintro ⟨a,⟨x,rfl⟩⟩
    change s.action (γ (β x)) (s.sectionData.coordinates bA).toAdd = _
    rw [hβ x (hZS x.property)]
    have he := s.sectionData.equivariant ⟨x,hZS x.property⟩ bA
    change (s.sectionData.coordinates ⟨(x : FreeAmalgam R)*b*
      (x : FreeAmalgam R)⁻¹,_⟩).toAdd =
        s.action (s.quotient ⟨x,hZS x.property⟩) (s.sectionData.coordinates bA).toAdd at he
    rw [←he]
    congr 2
    apply Subtype.ext
    exact (congrArg (fun t => t*(x : FreeAmalgam R)⁻¹) (hbB.2 x x.property)).trans
      (mul_inv_cancel_right b (x : FreeAmalgam R))
  have hmem := dualCover_fixed_le_natural_of_no_refinement i hi hdual β.range hno hfix
  obtain ⟨u,hu,he⟩ := (hrange _).mp hmem
  have hdiff : (u⁻¹*bA : Q R a) ∈ s.sectionData.coordinates.ker := by
    change s.sectionData.coordinates (u⁻¹*bA) = 1
    rw [map_mul,map_inv,show s.sectionData.coordinates u = s.sectionData.coordinates bA
      from Multiplicative.toAdd.injective he,inv_mul_cancel]
  rw [s.sectionData.kernel_eq] at hdiff
  have hd : ((u⁻¹*bA : Q R a) : FreeAmalgam R) ∈ fixedCore R a := hdiff
  have hmul := mul_mem (mem_sup_left hu) (mem_sup_right hd)
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_cancel_left] using hmul

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
