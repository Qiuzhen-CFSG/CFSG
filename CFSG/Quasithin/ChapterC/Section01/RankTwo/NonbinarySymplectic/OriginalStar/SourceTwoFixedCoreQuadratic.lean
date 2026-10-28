module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoFixedCore
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCore
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoFixedCore
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwo
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.FullCore
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.OriginalTriples
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceTwoLarge

/-!
# The original-star fixed-core quadraticity step

Write T for the original source star, T₀ for its component intersection,
Q and Q′ for the two complete endpoint cores, and D = C_Q(L). The source
star has its own intrinsic input, original quotient marking, inner ambient
action and distance-two graph. Its component is short by the supplied
minimum replacement's whole-core theorem. We work on this actual star;
no saturation or marked preservation of the minimum radical is assumed.

For a nonsylow original radical, the full source triples follow from the
abelian marked radical and T₀ ∩ Q = U. If Q moves more than q² cosets on U′,
symplectic orthogonality bounds the T₀ image by q. Criticality supplies the
opposite inequality. Retaining the entire common edge center gives
T₀ Q′ = U Q′ and hence T₀ = U (T₀ ∩ Q′).

If D also moves more than q² cosets, its natural fixed space is the line
filled by [U′,U]. Lifting through the complete cover puts
T₀ ∩ U′D′ inside UD′. The factorization then bounds the fixed index on
Q′/D′ by r′ = [Q′ : U′D′]. Four actual critical roots give the strict
opposite bound, a contradiction. Thus D moves at most q² cosets and acts
quadratically on U′. Restoring the full edge center proves [Z′,D,D] = 1.

The short-component versions of the original full-core calculations are
private supporting lemmas: they allow application to the source star
without postulating a minimum replacement or its saturation there.
Internal imports reuse the existing generic cover and relative-index
arguments, which do not assume a saturated minimum radical.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.7)(1) and the fixed-core quadraticity paragraph of (3.7)(2),
printed p.873, using (1.1)(ii)(1). The remaining q² fixed-core movement
comparison on pp.873--874, minimum marked preservation, the Sylow branch,
field restriction and block assembly remain separate obligations.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

private theorem short_original_core_eq_U (hshort : IsShort K)
    {a : Vertex R} (ha : color R a = false) :
    core R a = U R a := by
  let := h.component_normal
  have hblock : IsBlock K :=
    ⟨inferInstance,hshort,
      h.component.subnormal⟩
  have hcore : core R (alpha R) = U R (alpha R) := by
    rw [graphCore_eq_intrinsic K R h.radical.isPGroup h.radical.twoCore_le h.residual_eq]
    change ((blockU K).map K.subtype).map (embedM R) = _
    rw [←BlockOmega.omega_commutator hblock,←h.initialCore_eq]
    rw [U,Z_alpha_eq_omegaOrbit,Ltilde_alpha,h.residual_eq,←map_commutator]
  obtain ⟨v,rfl⟩ := exists_mVertex_of_color R ha
  have hv : mVertex R v = act R v (alpha R) := by
    simp [alpha,act_mVertex]
  rw [hv,core_act,U_act,hcore]

private theorem short_original_wholeKernelQuotient_over
    (hshort : IsShort K)
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
  have hmove : ⁅A,L₀⁆ ≤ U₀ := (short_original_core_eq_U h hshort ha).le
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

private theorem short_original_wholeKernel_natural_dualCover
    (hshort : IsShort K)
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
  obtain ⟨s,hs⟩ := short_original_wholeKernelQuotient_over h hshort ha κ hκ hκQ
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
    (short_original_core_eq_U h hshort ha).le
  refine ⟨E,hE,s,γ,hγinj,hγ,?_,i,hi,hdual,hrange,?_⟩
  · rw [hs,hγ]
    exact hκL
  · intro geometry hpos z path
    obtain ⟨β,hβmark,hβno⟩ := h.original_refinement_free_inner_actor (ρ := ρ₀) (B := C₀)
      (show Nat.card E.Carrier = Nat.card F by rw [E.card_eq,hE,h.field_card]) path hpos
      s₀ e he h.component_image_structure.2.2.2.2 j hj hjr κ hκQ hconj
    exact ⟨β,fun x hx => by rw [hs]; exact hβmark x hx,hβno⟩

private theorem short_original_critical_core_centralizer_le_moving_fixed
    (hshort : IsShort K)
    {geometry : Geometry R} (hpos : 0 < geometry.b R)
    {a z : Vertex R} (path : CriticalPath R geometry z a) :
    Q R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)) ≤
      U R a ⊔ fixedCore R a := by
  obtain ⟨E,hE,s,γ,hγ,hγC,hmap,i,hi,hdual,hrange,hcritical⟩ :=
    short_original_wholeKernel_natural_dualCover h hshort path.end_color
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

omit [Finite F] [CharP F 2] in
private theorem original_edge_inner
    (hinner : K ⊔ pCore 2 H = ⊤)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    Q R t ≤ Ltilde R a ⊔ Q R a := by
  obtain ⟨u,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
  swap
  · cases ha
  have ha : mVertex R u = act R u (alpha R) := by simp [alpha,act_mVertex]
  have ht : hVertex R u = act R u (beta R) := by simp [beta,act_hVertex]
  rw [ha,ht,Q_act,Ltilde_act,Q_act,←Subgroup.map_sup]
  apply map_mono
  rw [Ltilde_alpha,h.residual_eq,Q_alpha R h.radical.isPGroup h.radical.twoCore_le,
    ←Subgroup.map_sup,hinner,Q_beta]
  exact map_mono le_top

omit [Finite F] [CharP F 2] in
private theorem original_fixed_X_le_edge
    (hinner : K ⊔ pCore 2 H = ⊤)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≤ Z R t := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have hcentral : Q R t ≤ centralizer
      ((X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    apply (original_edge_inner h hinner ha hat).trans
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      ((Q_le_centralizer_X R a).trans (centralizer_le inf_le_left))
  intro x hx
  simp only [Z,ht,Bool.true_eq_false,↓reduceIte,edgeOmega]
  exact mem_omegaCenter_iff.mpr
    ⟨Q_le_adjacent_h R ht hat ((omegaCenter_le _) hx.1),
      (mem_omegaCenter_iff.mp hx.1).2.1, (le_centralizer_iff.mp hcentral) hx⟩

private theorem original_Z_le_moving_sup_fixed
    (hshort : IsShort K)
    (g : Geometry R) (hb : g.b R = 2)
    {a : Vertex R} (ha : color R a = false) :
    Z R a ≤ U R a ⊔ fixedCore R a := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := R) (geometry := g) ha
  have hd : (cosetGraph R).dist a z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two R a z hd
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hZQ : Z R a ≤ Q R a :=
    (g.omega_bound a ha (by
      rw [g.distance_constant a ha]; change 0 < g.b R; omega)).trans (omegaCenter_le _)
  have hseed : edgeOmega R t ≤ U R a ⊔ fixedCore R a := by
    apply (show edgeOmega R t ≤ Q R a ⊓
      centralizer (Z R z : Set (FreeAmalgam R)) from ?_).trans
      (short_original_critical_core_centralizer_le_moving_fixed h hshort (by omega) rev)
    have hZz : Z R z ≤ Q R t :=
      Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color) (by
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
          g.distance_constant z path.end_color]
        change 1 < g.b R
        omega)
    refine le_inf ((show edgeOmega R t ≤ Z R a from ?_).trans hZQ)
      (fun x hx y hy => (mem_omegaCenter_iff.mp hx).2.2 y (hZz hy))
    rw [Z,if_pos ha]
    exact le_iSup_of_le t (le_iSup_of_le hat le_rfl)
  have hSL : stabilizer R a ≤ normalizer (Ltilde R a : Set (FreeAmalgam R)) := by
    have hh := le_normalizer_map (H := pResidual 2 (stabilizer R a))
      (stabilizer R a).subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hD : stabilizer R a ≤ normalizer
      (fixedCore R a : Set (FreeAmalgam R)) :=
    (le_inf (Q_normalized R a)
      (hSL.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hn := (le_inf (U_normalized a) hD).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rw [Z,if_pos ha]
  apply iSup_le
  intro b
  apply iSup_le
  intro hab
  obtain ⟨u,hu,hub⟩ := stabilizer_transitive_neighbors R a hat hab
  rw [←hub,edgeOmega_act]
  exact (map_mono hseed).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer R a).inv_mem hu)))

/-- The full Z-layer has the actual incident edge center as fixed supplement
at every nonbinary distance-two endpoint. No order-q or Sylow premise is used. -/
private theorem original_Z_eq_moving_sup_edge
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (g : Geometry R) (hb : g.b R = 2)
    {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) :
    Z R a = U R a ⊔ Z R t := by
  have hZX := g.omega_bound a ha (by
    rw [g.distance_constant a ha]; change 0 < g.b R; omega)
  have hUZ : U R a ≤ Z R a := U_le_Z a
  have hUD : U R a ≤ centralizer (fixedCore R a : Set (FreeAmalgam R)) :=
    (hUZ.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R a ha))).trans (centralizer_le inf_le_left)
  apply le_antisymm ?_ (sup_le hUZ (Sp4Four.edge_Z_le_endpoint R ha hat))
  intro x hx
  have hprod := original_Z_le_moving_sup_fixed h hshort g hb ha hx
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    (hUD.trans (Subgroup.centralizer_le_normalizer _))] at hprod
  obtain ⟨u,hu,v,hv,rfl⟩ := hprod
  have hvX : v ∈ X R a := by
    have hh := (X R a).mul_mem
      ((X R a).inv_mem (hZX (hUZ hu))) (hZX hx)
    simpa only [inv_mul_cancel_left] using hh
  exact mul_mem (mem_sup_left hu) (mem_sup_right
    (original_fixed_X_le_edge h hinner ha hat ⟨hvX,hv.2⟩))

private theorem original_moving_triple_index_le
    (hinner : K ⊔ pCore 2 H = ⊤)
    {z : Vertex R} (hz : color R z=false)
    (A B : Subgroup (FreeAmalgam R))
    (hAS : A ≤ stabilizer R z) (hBS : B ≤ stabilizer R z)
    (hlarge : (2^n)^2 < (centralizer (A : Set (FreeAmalgam R))).relIndex
      (U R z))
    (htriple : ⁅⁅U R z,A⁆,B⁆=⊥) :
    (Q R z).relIndex B ≤ 2^n := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex hz
  have hCtop : C = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (C) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have haction (x : stabilizer R z) (w : s.space.toSubmodule) :
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
    (MovedSection.coverProjection s e) he (U R z) A B j hj hjr βA βB
    (fun a => haction (inclusion hAS a)) (fun b => haction (inclusion hBS b))
    (by simpa only [E.card_eq,hE] using hlarge) htriple
  have hk : αB.ker = (Q R z).subgroupOf B := by
    have hkκ : κ.ker = (Q R z).subgroupOf (stabilizer R z) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    dsimp only [αB,βB,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.comp_assoc,MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      ←MonoidHom.comap_ker,MonoidHom.ker_codRestrict,hkκ,comap_inclusion_subgroupOf]
  have hi : (Q R z).relIndex B = Nat.card αB.range := by
    rw [relIndex,←hk,index_ker]
  rw [hi]
  simpa only [E.card_eq,hE] using hbound


private theorem original_derived_le_core
    (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    ⁅R,R⁆ ≤ pCore 2 H := by
  obtain ⟨d⟩ := exists_characteristicReduction_of_core_le (L := K) h.radical.twoCore_le
  let D := (R.subgroupOf K).map (componentProjection h)
  let : IsMulCommutative D := original_marked_nonsylow_commutative h d hnsyl
  have hderived : ⁅K ⊓ R,K ⊓ R⁆ ≤ pCore 2 H := by
    apply commutator_le.mpr
    intro x hx y hy
    let xK : K := ⟨x,hx.1⟩
    let yK : K := ⟨y,hy.1⟩
    have hxD : componentProjection h xK ∈ D := mem_map_of_mem _ hx.2
    have hyD : componentProjection h yK ∈ D := mem_map_of_mem _ hy.2
    have hc : Commute (componentProjection h xK) (componentProjection h yK) :=
      congrArg Subtype.val (mul_comm (⟨_,hxD⟩ : D) ⟨_,hyD⟩)
    have hk : ⁅xK,yK⁆ ∈ pCore 2 K := by
      rw [←componentProjection_kernel h]
      change componentProjection h ⁅xK,yK⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr hc
    exact (pCoreIn_le_of_subnormal 2 h.component.subnormal)
      (mem_map_of_mem K.subtype hk)
  let q := QuotientGroup.mk' (pCore 2 H)
  have him : R.map q ≤ (K ⊓ R).map q := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨k,hk,r,hr,he⟩ := mem_sup_of_normal_right.mp (hinner.symm ▸ mem_top x)
    have hkR : k ∈ R := by
      have hh := R.mul_mem hx (R.inv_mem (h.radical.twoCore_le hr))
      rwa [←he,mul_inv_cancel_right] at hh
    refine ⟨k,⟨hk,hkR⟩,?_⟩
    have hq : q r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    rw [←he,map_mul,hq,mul_one]
  have hzero : ⁅R,R⁆.map q = ⊥ := by
    apply le_bot_iff.mp
    rw [map_commutator]
    apply (commutator_mono him him).trans
    rw [←map_commutator,map_le_iff_le_comap]
    change ⁅K ⊓ R,K ⊓ R⁆ ≤ q.ker
    rw [QuotientGroup.ker_mk']
    exact hderived
  exact ((Subgroup.map_eq_bot_iff _).mp hzero).trans_eq (QuotientGroup.ker_mk' _)

private theorem original_component_core_intersection
    (hshort : IsShort K) {a : Vertex R} (ha : color R a = false) :
    Ltilde R a ⊓ Q R a = U R a := by
  let := h.component_normal
  have hbase : Ltilde R (alpha R) ⊓ Q R (alpha R) = U R (alpha R) := by
    rw [←short_original_core_eq_U h hshort rfl,
      graphCore_eq_intrinsic K R h.radical.isPGroup h.radical.twoCore_le h.residual_eq,
      Ltilde_alpha,h.residual_eq,Q_alpha R h.radical.isPGroup h.radical.twoCore_le,
      ←map_inf _ _ _ (embedM_injective R),original_component_inf_core h,map_map]
    rw [map_map]
    rfl
  obtain ⟨v,rfl⟩ := exists_mVertex_of_color R ha
  have hv : mVertex R v = act R v (alpha R) := by simp [alpha,act_mVertex]
  rw [hv,Ltilde_act,Q_act,U_act,←map_inf _ _ _ (MulAut.conj v⁻¹).injective,hbase]

private theorem original_edge_derived_le
    (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ⁅Q R t,Q R t⁆ ≤ Q R a := by
  obtain ⟨u,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
  swap
  · cases ha
  have ha : mVertex R u = act R u (alpha R) := by simp [alpha,act_mVertex]
  have ht : hVertex R u = act R u (beta R) := by simp [beta,act_hVertex]
  rw [ha,ht,Q_act,Q_act,←map_commutator]
  apply map_mono
  rw [Q_beta,Q_alpha R h.radical.isPGroup h.radical.twoCore_le,←map_commutator]
  exact map_mono (original_derived_le_core h hinner hnsyl)

omit h [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem original_residual_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (Ltilde R a : Set (FreeAmalgam R)) := by
  have ht := le_normalizer_map (H := pResidual 2 (stabilizer R a)) (stabilizer R a).subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
  exact ht

private theorem original_component_radical_triples
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅Z R z,Q R t ⊓ Ltilde R a⁆ ≤ U R a ∧
      ⁅⁅Z R z,Q R a⁆,Q R t ⊓ Ltilde R a⁆ = ⊥ := by
  let T := Q R t
  let B := T ⊓ Ltilde R a
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQT : Q R a ≤ T := Q_le_adjacent_h R ht hat
  have hTS : T ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTB : T ≤ normalizer (B : Set (FreeAmalgam R)) :=
    (le_inf T.le_normalizer (hTS.trans (original_residual_normalized a))).trans
      inf_normalizer_le_normalizer_inf
  have hZt : Z R z ≤ T := by
    apply Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b R
    omega
  have hd := original_edge_derived_le h hinner hnsyl path.start_color hat
  have hd' := original_edge_derived_le h hinner hnsyl path.end_color hzt
  have hBQ : B ⊓ Q R a ≤ U R a :=
    (inf_le_inf_right _ inf_le_right).trans_eq (original_component_core_intersection h hshort path.start_color)
  have hmove : ⁅Z R z,B⁆ ≤ U R a :=
    (le_inf (le_normalizer_iff_commutator_le_right.mp (hZt.trans hTB))
      ((commutator_mono hZt inf_le_left).trans hd)).trans hBQ
  have h1 : ⁅⁅Q R a,B⁆,Z R z⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (((commutator_mono hQT inf_le_left).trans hd').trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q R z path.end_color))))
  have h2 : ⁅⁅B,Z R z⁆,Q R a⁆ = ⊥ := by
    rw [commutator_comm B]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hmove.trans ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R a path.start_color))))
  exact ⟨hmove,commutator_commutator_eq_bot_of_rotate h1 h2⟩

/-- In the original large-movement branch, the component part and the
moving layer have the same order-q image in the opposite full-core quotient. -/
private theorem original_large_movement_images
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (Q R z).relIndex (Q R t ⊓ Ltilde R a) = 2^n ∧
      (Q R z).relIndex (U R a) = 2^n ∧
      (Q R z).relIndex (Z R a) = 2^n ∧
      (Q R t ⊓ Ltilde R a) ⊔ Q R z = U R a ⊔ Q R z := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective (inclusion hTSz) (inclusion_injective _)
  let : ((Q R z).subgroupOf (Q R t)).Normal :=
    normal_subgroupOf_of_le_normalizer (hTSz.trans (Q_normalized R z))
  have hULQ := (original_component_core_intersection h hshort path.start_color).ge
  have hU₀ : U R a ≤ Q R t ⊓ Ltilde R a :=
    le_inf (hULQ.trans (inf_le_right.trans hQaT)) (hULQ.trans inf_le_left)
  have hUT := hU₀.trans inf_le_left
  have hZtQ : Z R t ≤ Q R z :=
    (Sp4Four.edge_Z_le_endpoint R path.end_color hzt).trans
      ((g.omega_bound z path.end_color (by
        rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans (omegaCenter_le _))
  have hZa : Z R a ≤ U R a ⊔ Q R z := by
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat]
    exact sup_le_sup_left hZtQ _
  have hsup (B : Subgroup (FreeAmalgam R)) (hBT : B ≤ Q R t) :
      (Q R z).relIndex (B ⊔ Q R z) = (Q R z).relIndex B := by
    rw [←relIndex_subgroupOf (sup_le hBT hQzT),
      subgroupOf_sup hBT hQzT,relIndex_sup_right,relIndex_subgroupOf hBT]
  have hfinite (B : Subgroup (FreeAmalgam R)) (hBT : B ≤ Q R t) :
      (Q R z).relIndex B ≠ 0 := by
    let : Finite B := Finite.of_injective (inclusion hBT) (inclusion_injective _)
    exact index_ne_zero_of_finite
  have htriple := (original_component_radical_triples h hshort hinner hnsyl g hb path hat hzt).2
  have hbound := original_moving_triple_index_le h hinner path.end_color
    (Q R a) (Q R t ⊓ Ltilde R a)
    (hQaT.trans hTSz) (inf_le_left.trans hTSz) hlarge
    (le_antisymm ((commutator_mono (commutator_mono (U_le_Z z) le_rfl) le_rfl).trans
      htriple.le) bot_le)
  have hlow := (h.original_critical_indices_ge_field path (by omega)).1
  rw [h.field_card] at hlow
  have hZU : (Q R z).relIndex (Z R a) ≤ (Q R z).relIndex (U R a) := by
    have hh := relIndex_le_of_le_right hZa (hfinite _ (sup_le hUT hQzT))
    rwa [hsup _ hUT] at hh
  have hU₀i := relIndex_le_of_le_right hU₀ (hfinite _ inf_le_left)
  have hUi : (Q R z).relIndex (U R a) = 2^n := by omega
  have h₀i : (Q R z).relIndex (Q R t ⊓ Ltilde R a) = 2^n := by omega
  refine ⟨h₀i,hUi,by omega,?_⟩
  have hQX : Q R z ≤ U R a ⊔ Q R z := le_sup_right
  have hXY : U R a ⊔ Q R z ≤ (Q R t ⊓ Ltilde R a) ⊔ Q R z := sup_le_sup_right hU₀ _
  have hm := relIndex_mul_relIndex (Q R z)
    (U R a ⊔ Q R z) ((Q R t ⊓ Ltilde R a) ⊔ Q R z) hQX hXY
  rw [hsup _ hUT,hsup (Q R t ⊓ Ltilde R a) inf_le_left,hUi,h₀i] at hm
  have hqi : (U R a ⊔ Q R z).relIndex ((Q R t ⊓ Ltilde R a) ⊔ Q R z) = 1 :=
    Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2^n) (by simpa using hm)
  exact le_antisymm (relIndex_eq_one.mp hqi) hXY

/-- MS93 (3.7)(2), p.873: large movement gives the literal factorization
T₀ = U (T₀ ∩ Q′) in the original graph. The whole opposite core is retained.
Innerness and shortness are supplied by the actual source star below. -/
theorem original_large_movement_component_factorization
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hlarge : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (Q R t ⊓ Ltilde R a) = U R a ⊔ ((Q R t ⊓ Ltilde R a) ⊓ Q R z) := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hULQ := (original_component_core_intersection h hshort path.start_color).ge
  have hU₀ : U R a ≤ Q R t ⊓ Ltilde R a :=
    le_inf (hULQ.trans (inf_le_right.trans hQaT)) (hULQ.trans inf_le_left)
  have he := (original_large_movement_images h hshort hinner hnsyl g hb path hat hzt hlarge).2.2.2
  apply le_antisymm ?_ (sup_le hU₀ inf_le_left)
  intro x hx
  have hx' : x ∈ U R a ⊔ Q R z := he ▸ mem_sup_left hx
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    ((hU₀.trans inf_le_left).trans (hTSz.trans (Q_normalized R z)))] at hx'
  obtain ⟨u,hu,q,hq,rfl⟩ := hx'
  have hq₀ : q ∈ Q R t ⊓ Ltilde R a := by
    have hh := (Q R t ⊓ Ltilde R a).mul_mem
      ((Q R t ⊓ Ltilde R a).inv_mem (hU₀ hu)) hx
    simpa only [inv_mul_cancel_left] using hh
  exact mul_mem (mem_sup_left hu) (mem_sup_right ⟨hq₀,hq⟩)

/-- The actual original marked star supplies every premise of the
large-movement factorization, including its own distance-two graph.
No saturation or marked-image equality of the minimum replacement is assumed. -/
theorem exists_source_star_large_movement_factorization
    (d : CharacteristicReduction K R) (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       let S := T.subgroupOf M
       ∃ hs : Input (K.subgroupOf M) S n F, ∃ gs : Geometry S,
         hs.quotientEquiv = (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv ∧
         S = R.subgroupOf M ∧
         (normalizer (S : Set M)).pCoreIn 2 = S ∧
         ((T.subgroupOf K).map (componentProjection h)) =
           (R.subgroupOf K).map (componentProjection h) ∧
         gs.b S = 2 ∧
         ∀ (a z t : Vertex S) (_path : CriticalPath S gs a z),
           Adjacent S a t → Adjacent S z t →
           (2^n)^2 < (centralizer (Q S a : Set (FreeAmalgam S))).relIndex (U S z) →
           Q S t ⊓ Ltilde S a = U S a ⊔ ((Q S t ⊓ Ltilde S a) ⊓ Q S z)) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl,gs,hgs⟩ :=
    exists_source_star_intrinsic_distance_two h d g hb
  have hshort := (short_and_natural_of_distance_two h d g hb).1
  have hstarshort : IsShort (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype)) :=
    hshort.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm
  have hstar_nsyl : ¬ ∃ S' : Sylow 2 (Sp F), (S' : Subgroup (Sp F)) =
      ((((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)).subgroupOf
          (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))).map (componentProjection hs) := by
    intro he
    exact hnsyl ((original_sylow_iff_marked_sylow h).mp
      (hsyl.mp ((original_sylow_iff_marked_sylow hs).mpr he)))
  refine ⟨P,Y,hY,hn,hmin,hs,gs,hquot,hrest,hsat,hmark,hgs,?_⟩
  intro a z t path hat hzt hlarge
  exact original_large_movement_component_factorization hs hstarshort hinner
    hstar_nsyl gs hgs path hat hzt hlarge

private theorem short_original_core_relIndex_natural_sup_fixed_le
    (hshort : IsShort K)
    {a : Vertex R} (ha : color R a = false) :
    (U R a ⊔ fixedCore R a).relIndex (Q R a) ≤ 2^n := by
  obtain ⟨E,hE,s,γ,hγinj,hγ,hmap,i,hi,hd,hrange,_⟩ :=
    short_original_wholeKernel_natural_dualCover h hshort ha
  have hrank := original_natural_dualCover_quotient_bound (s.action.comp γ) i hi hd
  have hdegree : Module.finrank (ZMod 2) E.Carrier = n := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E.Carrier)
    rw [Nat.card_zmod,E.card_eq,hE] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2) hc).symm
  rw [hdegree] at hrank
  let V := i.toLinearMap.range
  let π := s.sectionData.coordinates
  let f : Q R a →* Multiplicative (s.Carrier ⧸ V) :=
    V.mkQ.toAddMonoidHom.toMultiplicative.comp π
  have hf : Function.Surjective f := V.mkQ_surjective.comp s.sectionData.onto
  have hV : V.toAddSubgroup.toSubgroup =
      ((U R a).subgroupOf (Q R a)).map π := by
    ext w
    change w.toAdd ∈ i.toLinearMap.range ↔ _
    rw [hrange]
    constructor
    · rintro ⟨x,hx,he⟩
      exact ⟨x,hx,Multiplicative.toAdd.injective he⟩
    · rintro ⟨x,hx,he⟩
      exact ⟨x,hx,congrArg Multiplicative.toAdd he⟩
  have hk : f.ker = (V.toAddSubgroup.toSubgroup).comap π := by
    ext x
    change V.mkQ (π x).toAdd = 0 ↔ (π x).toAdd ∈ V
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  have hUQ : U R a ≤ Q R a := by
    obtain ⟨geometry,hpos,_⟩ := h.positive_even_geometry
    apply (U_le_Z _).trans
    exact (geometry.omega_bound a ha (by
      rw [geometry.distance_constant a ha]; exact hpos)).trans (omegaCenter_le _)
  have hkernel : f.ker.map (Q R a).subtype =
      U R a ⊔ fixedCore R a := by
    rw [hk,hV,comap_map_eq,Subgroup.map_sup,s.sectionData.kernel_eq,
      map_subgroupOf_eq_of_le hUQ,map_subgroupOf_eq_of_le s.sectionData.kernel_le]
    rfl
  have hindex : (U R a ⊔ fixedCore R a).relIndex (Q R a) =
      Nat.card (s.Carrier ⧸ V) := by
    rw [←hkernel]
    have hh := relIndex_map_map_of_injective (f := (Q R a).subtype)
      f.ker ⊤ (Q R a).subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype,relIndex_top_right,index_ker,
      MonoidHom.range_eq_top.mpr hf,
      Nat.card_congr (topEquiv :
        (⊤ : Subgroup (Multiplicative (s.Carrier ⧸ V))) ≃* _).toEquiv] at hh
    exact hh
  rw [hindex,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) hrank

/- The natural dual-cover image has dimension `4n`; the quotient index
   therefore factors through the complete fixed attachment as in (3.7). -/
private theorem short_original_core_fixed_index_eq_natural_mul
    (hshort : IsShort K)
    {a : Vertex R} (ha : color R a = false) :
    (fixedCore R a).relIndex (Q R a) = (2^n)^4 *
      (U R a ⊔ fixedCore R a).relIndex (Q R a) := by
  obtain ⟨E,hE,s,γ,hγinj,hγ,hmap,i,hi,hd,hrange,_⟩ :=
    short_original_wholeKernel_natural_dualCover h hshort ha
  obtain ⟨geometry,hpos,_⟩ := h.positive_even_geometry
  have hUQ : U R a ≤ Q R a :=
    (U_le_Z a).trans ((geometry.omega_bound a ha (by
      rw [geometry.distance_constant a ha]; exact hpos)).trans (omegaCenter_le _))
  have himage : s.sectionData.imageSpace (U R a) = i.toLinearMap.range := by
    ext w
    rw [hrange,s.sectionData.mem_imageSpace_iff]
  have hiU : (fixedCore R a).relIndex (U R a) = (2^n)^4 := by
    have hic : Nat.card (s.sectionData.imageSpace (U R a)) =
        (fixedCore R a).relIndex (U R a) :=
      s.sectionData.imageSpace_card_eq_relIndex (U R a) hUQ
    rw [←hic,himage,
      ←Nat.card_congr (LinearEquiv.ofInjective i.toLinearMap hi).toEquiv]
    rw [Module.natCard_eq_pow_finrank (K := E.Carrier)]
    simp [Natural,E.card_eq,hE]
  let : ((fixedCore R a).subgroupOf (Q R a)).Normal :=
    s.sectionData.kernel_normal
  have hiUD : (fixedCore R a).relIndex (U R a ⊔ fixedCore R a) = (2^n)^4 := by
    rw [←relIndex_subgroupOf
      (sup_le hUQ (show fixedCore R a ≤ Q R a from inf_le_left)),
      subgroupOf_sup hUQ (show fixedCore R a ≤ Q R a from inf_le_left),
      relIndex_sup_right,relIndex_subgroupOf hUQ,hiU]
  exact (relIndex_mul_relIndex (fixedCore R a)
    (U R a ⊔ fixedCore R a) (Q R a) le_sup_right
    (sup_le hUQ inf_le_left)).symm.trans (by rw [hiUD])

private theorem short_original_core_fixed_index_le_critical_index_pow_four
    (hshort : IsShort K)
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hpos : 0 < geometry.b R)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n) :
    (fixedCore R a).relIndex (Q R a) ≤
      ((commutatorPreimage (Q R a) (Z R z)
        (fixedCore R a)).relIndex (Q R a))^4 := by
  let := h.component_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let s₀ := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  obtain ⟨s,hs⟩ := short_original_wholeKernelQuotient_over h hshort path.start_color κ hκ hκQ
  let B := K.map (QuotientGroup.mk' (pCore 2 H))
  let γ := B.subtype.comp e.groupEquiv.symm.toMonoidHom
  have hZQ : Z R a ≤ Q R a :=
    (geometry.omega_bound a path.start_color (by
      rw [geometry.distance_constant a path.start_color]; exact hpos)).trans
      (omegaCenter_le _)
  let σ := s.action.comp γ
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R geometry hedge a path.start_color
        (by rw [geometry.distance_constant a path.start_color]; exact hpos)
        z path.end_color path.critical }
  have hsmall : (Q R z).relIndex (Z R a) < (2^n)^2 := by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ))
      (by have := h.nonbinary; omega)
    nlinarith
  obtain ⟨haq,hzq⟩ := h.original_small_critical_indices_eq_field path hpos
    (by simpa only [h.field_card] using hsmall)
  rw [h.field_card] at haq hzq
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZA κ hκQ).trans (hzq.trans hFc.symm)
  have hδ : ∀ x : Z R z, ∀ v : s₀.space.toSubmodule,
      j (Multiplicative.ofAdd (s₀.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hZA x) v
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev hpos
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer z path.end_color)
    h.nonbinary hFc s₀ e he h.component_image_structure.2.2.2.2
    j hj hjr δ hδ hδcard (haq.trans hFc.symm)
  have hmap : ((Z R z).subgroupOf (stabilizer R a)).map κ = β.range.map γ := by
    have heq : γ.comp β = δ := by
      ext x
      exact hβmark x
    rw [←MonoidHom.range_comp,heq]
    apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
    · rintro y ⟨x,rfl⟩
      exact ⟨inclusion hZA x,x.property,rfl⟩
  have hSN : stabilizer R a ≤ normalizer
      ((Q R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))) : Set (FreeAmalgam R)) := by
    have hSL : stabilizer R a ≤ normalizer (Ltilde R a : Set (FreeAmalgam R)) := by
      have ht := le_normalizer_map (H := pResidual 2 (stabilizer R a))
        (stabilizer R a).subtype
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
      exact ht
    exact (le_inf (Q_normalized R a)
      (hSL.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hfixed : fixedSpace σ ⊤ = ⊥ := by
    apply bot_unique
    intro v hv
    apply s.fixed_eq_bot.le
    rintro ⟨x,hx⟩
    rw [hs,hκL] at hx
    obtain ⟨b,hb⟩ := (e.groupEquiv.symm.surjective ⟨x,hx⟩)
    have he : γ b = x := congrArg Subtype.val hb
    change s.action x v = v
    rw [←he]
    exact hv ⟨b,mem_top _⟩
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  obtain ⟨f,hf⟩ := derived_four_conjugates_of_displacement_one
    hcard β.range hβcard hβdim hβquad
  have hdim := fixedCodim_le_card_mul_of_subgroup_conjugates σ ⊤ β.range f hf.ge
  have htotal := fixedCodim_add_finrank σ ⊤
  rw [hfixed,finrank_bot,add_zero] at htotal
  rw [htotal,Fintype.card_fin] at hdim
  have hindex := s.sectionData.fixed_index_of_relative_normalizers (Z R z)
    hZA (s.sectionData.section_le.trans hSN) (hZA.trans hSN)
  unfold fixedCodim at hindex
  rw [fixedSpace_comp_map,hs,hmap,←fixedSpace_comp_map] at hindex
  change (commutatorPreimage (Q R a) (Z R z)
    (fixedCore R a)).relIndex (Q R a) = 2^fixedCodim σ β.range at hindex
  have horder : (fixedCore R a).relIndex (Q R a) = Nat.card s.Carrier := by
    change ((fixedCore R a).subgroupOf (Q R a)).index = _
    have hk : s.sectionData.coordinates.ker =
        (fixedCore R a).subgroupOf (Q R a) := s.sectionData.kernel_eq
    rw [←hk,index_ker,MonoidHom.range_eq_top.mpr s.sectionData.onto,
      card_top]
    rfl
  rw [horder,hindex,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,←pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by simpa only [Nat.mul_comm] using hdim)

/-- Four critical-root conjugates make the full fixed-core index strictly
larger than the natural index. -/
private theorem short_original_core_critical_fixed_index_gt_natural_index
    (hshort : IsShort K)
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hpos : 0 < geometry.b R)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n) :
    (U R a ⊔ fixedCore R a).relIndex (Q R a) <
      (commutatorPreimage (Q R a) (Z R z)
        (fixedCore R a)).relIndex (Q R a) := by
  let q := 2^n
  let r := (U R a ⊔ fixedCore R a).relIndex (Q R a)
  let k := (commutatorPreimage (Q R a) (Z R z)
    (fixedCore R a)).relIndex (Q R a)
  have hq : 1 < q := one_lt_pow₀ (by decide : 1 < (2:ℕ))
    (by have := h.nonbinary; omega)
  have hr : r ≤ q := short_original_core_relIndex_natural_sup_fixed_le h hshort path.start_color
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hrpos : 0 < r := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hh : q^4*r ≤ k^4 := by
    rw [←short_original_core_fixed_index_eq_natural_mul h hshort path.start_color]
    exact short_original_core_fixed_index_le_critical_index_pow_four h hshort path hpos hcritical
  by_contra! hkr
  have hle : q^4*r ≤ q^3*r := calc
    _ ≤ k^4 := hh
    _ ≤ r^4 := Nat.pow_le_pow_left hkr 4
    _ = r^3*r := pow_succ r 3
    _ ≤ q^3*r := Nat.mul_le_mul_right r (Nat.pow_le_pow_left hr 3)
  have he := Nat.le_of_mul_le_mul_right hle hrpos
  exact (not_le_of_gt ((pow_lt_pow_iff_right₀ hq).mpr (by decide : 3 < 4))) he


omit h [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem original_fixedCore_normalized
    {a t : Vertex R} (hat : Adjacent R a t) :
    Q R t ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) := by
  have hTS : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  exact (le_inf (hTS.trans (Q_normalized R a))
    ((hTS.trans (original_residual_normalized a)).trans
      (normalizer_le_normalizer_centralizer (Ltilde R a)))).trans inf_normalizer_le_normalizer_inf

omit [Finite F] [CharP F 2] in
private theorem original_component_radical_sup_core
    (hinner : K ⊔ pCore 2 H = ⊤)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    (Q R t ⊓ Ltilde R a) ⊔ Q R a = Q R t := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all
  have hQT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  apply le_antisymm (sup_le inf_le_left hQT)
  intro x hx
  have hxs := original_edge_inner h hinner ha hat hx
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _
    ((Ltilde_le_stabilizer a).trans (Q_normalized R a))] at hxs
  obtain ⟨l,hl,q,hq,he⟩ := hxs
  have hlT : l ∈ Q R t := by
    have hh := (Q R t).mul_mem hx ((Q R t).inv_mem (hQT hq))
    simpa only [←he,mul_inv_cancel_right] using hh
  rw [←he]
  exact mul_mem (mem_sup_left ⟨hlT,hl⟩) (mem_sup_right hq)

private theorem original_fixedCore_large_centralizer_comparison
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (himage : (Q R z).relIndex (U R a) = 2^n)
    (hlarge : (2^n)^2 <
      (centralizer (fixedCore R a : Set (FreeAmalgam R))).relIndex (U R z)) :
    (Q R t ⊓ Ltilde R a) ⊓ (U R z ⊔ fixedCore R z) ≤
      U R a ⊔ fixedCore R z := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hUa : U R a ≤ Ltilde R a ⊓ Q R a := (original_component_core_intersection h hshort path.start_color).ge
  have hUz : U R z ≤ Ltilde R z ⊓ Q R z := (original_component_core_intersection h hshort path.end_color).ge
  let A := fixedCore R a
  let B := U R a
  have hAT : A ≤ Q R t := inf_le_left.trans hQaT
  have hB₀ : B ≤ (Q R t ⊓ Ltilde R a) :=
    le_inf (hUa.trans (inf_le_right.trans hQaT)) (hUa.trans inf_le_left)
  have hBT : B ≤ Q R t := hB₀.trans inf_le_left
  have hAS : A ≤ stabilizer R z := hAT.trans hTSz
  have hBS : B ≤ stabilizer R z := hBT.trans hTSz
  have hz := path.end_color
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex hz
  have hCtop : C = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (C) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have haction (x : stabilizer R z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  let βA := γ.comp (inclusion hAS)
  let βB := γ.comp (inclusion hBS)
  let αB := (commutator (Sp E.Carrier)).subtype.comp βB
  have hk : αB.ker = (Q R z).subgroupOf B := by
    have hkκ : κ.ker = (Q R z).subgroupOf (stabilizer R z) := by
      rw [←hκQ,subgroupOf_map_subtype_eq]
    dsimp only [αB,βB,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.comp_assoc,MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      ←MonoidHom.comap_ker,MonoidHom.ker_codRestrict,hkκ,comap_inclusion_subgroupOf]
  have hi : Nat.card αB.range = 2^n := by
    rw [←index_ker,hk]
    exact himage
  have hBlarge : 1 < Nat.card αB.range := by
    rw [hi]
    exact one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  have hmove : ⁅B,U R z⁆ ≤ U R a := by
    rw [commutator_comm]
    exact (commutator_mono (U_le_Z z) hB₀).trans
      (original_component_radical_triples h hshort hinner hnsyl g hb path hat hzt).1
  have htriple : ⁅⁅U R z,B⁆,A⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [commutator_comm (U R z)]
    exact hmove.trans (((U_le_Z a).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a path.start_color))).trans
      (centralizer_le (show A ≤ Q R a from inf_le_left)))
  have hUzT : U R z ≤ Q R t := hUz.trans (inf_le_right.trans hQzT)
  have hkernel (w : s.space.toSubmodule) :
      MovedSection.coverProjection s e w=0 ↔
        j (Multiplicative.ofAdd w) ∈ fixedCore R z := by
    constructor
    · intro hw
      refine ⟨?_,(hker w).mp hw⟩
      exact ((U_le_Z z).trans ((g.omega_bound z path.end_color (by
        rw [g.distance_constant z path.end_color]; change 0 < g.b R; omega)).trans
          (omegaCenter_le _))) (hjr ▸ ⟨_,rfl⟩)
    · exact fun hw => (hker w).mpr hw.2
  have hfixed := cover_large_centralizer_le (MovedSection.coverAction s e)
    (MovedSection.coverProjection s e) he (U R z) A B
    (U R a) (fixedCore R z) j hj hjr βA βB
    (fun x => haction (inclusion hAS x)) (fun x => haction (inclusion hBS x))
    (by simpa only [E.card_eq,hE] using hlarge) hBlarge htriple hmove hkernel
    (hUzT.trans (original_fixedCore_normalized hzt))
  apply component_intersection_le_of_fixed_preimage (Q R t)
    ((Q R t ⊓ Ltilde R a)) A (U R z) (U R a)
    (fixedCore R z) inf_le_left hUzT (inf_le_left.trans hQzT)
    (le_normalizer_iff_commutator_le_left.mp (hAT.trans (original_fixedCore_normalized hzt)))
    (original_fixedCore_normalized hzt) ?_ hfixed
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (centralizer_le (show Q R t ⊓ Ltilde R a ≤ Ltilde R a from inf_le_right)))


/-- The full fixed core moves at most q² cosets of the opposite natural cover. -/
theorem original_fixedCore_movement_le_square
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    (centralizer (fixedCore R a : Set (FreeAmalgam R))).relIndex
      (U R z) ≤ (2^n)^2 := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hQzT : Q R z ≤ Q R t := Q_le_adjacent_h R ht hzt
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hTSa : Q R t ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  let := finite_stabilizer R z
  let : Finite (Q R t) := Finite.of_injective
    (inclusion hTSz) (inclusion_injective _)
  have hUzQ : U R z ≤ Q R z :=
    (original_component_core_intersection h hshort path.end_color).ge.trans inf_le_right
  have hUaQ : U R a ≤ Q R a :=
    (original_component_core_intersection h hshort path.start_color).ge.trans inf_le_right
  let : Finite (U R z) := Finite.of_injective
    (inclusion (hUzQ.trans hQzT)) (inclusion_injective _)
  by_contra! hlarge
  have hlargeQ : (2^n)^2 <
      (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (U R z) :=
    hlarge.trans_le (relIndex_le_of_le_left (centralizer_le
      (show fixedCore R a ≤ Q R a from inf_le_left)) index_ne_zero_of_finite)
  obtain ⟨hT,hU,hZ,he⟩ := original_large_movement_images h hshort hinner hnsyl g hb path hat hzt hlargeQ
  have hfactor := original_large_movement_component_factorization h hshort hinner hnsyl g hb path hat hzt hlargeQ
  have hcomp := original_fixedCore_large_centralizer_comparison h hshort hinner hnsyl g hb path hat hzt hU hlarge
  have hZaT : Z R a ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R a (g.exists_critical a path.start_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
      g.distance_constant a path.start_color]
    change 1 < g.b R
    omega
  have hbound := fixed_index_le_of_component_intersection (Q R t)
    ((Q R t ⊓ Ltilde R a)) (Q R a) (Q R z)
    (U R a) (U R z) (fixedCore R z) (Z R a)
    (original_component_radical_sup_core h hinner path.start_color hat) hfactor hUaQ hQzT hUzQ inf_le_left
    (hTSa.trans (Q_normalized R a)) (original_fixedCore_normalized hzt) hZaT
    (by rw [commutator_comm]; exact Z_centralizes_Q R a path.start_color)
    (hcomp.trans (sup_le_sup_right hUaQ _))
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hother := (h.original_small_critical_indices_eq_field path (by omega) (by
    rw [h.field_card]
    rw [hZ]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  exact (not_le_of_gt (short_original_core_critical_fixed_index_gt_natural_index h hshort rev (by omega) (by simpa only [h.field_card] using hother))) hbound


private theorem original_moving_quadratic_of_small_index
    (hinner : K ⊔ pCore 2 H = ⊤)
    {z : Vertex R} (hz : color R z = false)
    (A : Subgroup (FreeAmalgam R)) (hAS : A ≤ stabilizer R z)
    (hA : IsPGroup 2 A)
    (hsmall : (centralizer (A : Set (FreeAmalgam R))).relIndex
      (U R z) ≤ (2^n)^2) :
    ⁅⁅U R z,A⁆,A⁆ = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex hz
  have hCtop : C = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (C) (fun x => hCtop ▸ mem_top (κ x))
  let β := e.groupEquiv.toMonoidHom.comp (κC.comp (inclusion hAS))
  have hβ (x : A) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hAS x)))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hAS x) w
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hαr : α.range=β.range.map (commutator (Sp E.Carrier)).subtype :=
    MonoidHom.range_comp _ _
  have hαP : IsPGroup 2 α.range := hA.of_surjective α.rangeRestrict α.rangeRestrict_surjective
  have hi := embedded_centralizer_index (MovedSection.coverAction s e)
    (U R z) A j hj hjr β hβ
  rw [hi,fixedCodim_of_binaryCover (MovedSection.coverProjection s e) he] at hsmall
  let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
  have hm := fixedCodim_map_equivariant (binaryNatural (K := E.Carrier)) τ
    (commutator (Sp E.Carrier)).subtype (LinearEquiv.refl _ _) (fun _ _ => rfl) β.range
  rw [←hαr] at hm
  rw [hm] at hsmall
  have hquad := quadratic_of_small_natural_index α.range hαP
    (by simpa only [E.card_eq,hE] using hsmall)
  apply embedded_quadratic_of_natural_quadratic (U R z) A j hjr β
    (MovedSection.coverAction s e) hβ (MovedSection.coverProjection s e) he
  exact fun a b v => hquad (α a) ⟨a,rfl⟩ (α b) ⟨b,rfl⟩ v


/-- The full fixed core acts quadratically on the entire opposite Z-layer
of the original source pair, including both complete fixed attachments. -/
theorem original_fixedCore_quadratic
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅⁅Z R z,fixedCore R a⁆,fixedCore R a⁆ = ⊥ := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQaT : Q R a ≤ Q R t := Q_le_adjacent_h R ht hat
  have hTSz : Q R t ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hAT : fixedCore R a ≤ Q R t := inf_le_left.trans hQaT
  have hsmall := original_fixedCore_movement_le_square h hshort hinner hnsyl g hb path hat hzt
  have hA : IsPGroup 2 (fixedCore R a) :=
    (Q_isPGroup R h.radical.isPGroup h.radical.twoCore_le a path.start_color).of_injective
      (inclusion (show fixedCore R a ≤ Q R a from inf_le_left)) (inclusion_injective _)
  have hquad := original_moving_quadratic_of_small_index h hinner path.end_color
    (fixedCore R a) (hAT.trans hTSz) hA hsmall
  have hcentral : Z R t ≤ centralizer (fixedCore R a : Set (FreeAmalgam R)) := by
    have hZt : Z R t = omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
    rw [hZt]
    exact fun x hx y hy => (mem_omegaCenter_iff.mp hx).2.2 y (hAT hy)
  have hUzT : U R z ≤ Q R t :=
    ((original_component_core_intersection h hshort path.end_color).ge.trans inf_le_right).trans
      (Q_le_adjacent_h R ht hzt)
  have heq : ⁅Z R z,fixedCore R a⁆ = ⁅U R z,fixedCore R a⁆ := by
    apply le_antisymm ?_ (commutator_mono (U_le_Z z) le_rfl)
    rw [commutator_comm (Z R z),commutator_comm (U R z)]
    apply commutator_le_moving_of_inner_mod_centralizer (fixedCore R a)
      (U R z) (Z R z) (hUzT.trans (original_fixedCore_normalized hat))
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt]
    exact sup_le_sup_left hcentral _
  simpa only [heq] using hquad

/-- The original marked source star satisfies the full fixed-core quadraticity
step of MS93 (3.7)(2), with no additional premise on the minimum radical. -/
theorem exists_source_star_fixedCore_quadratic
    (d : CharacteristicReduction K R) (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       let S := T.subgroupOf M
       ∃ hs : Input (K.subgroupOf M) S n F, ∃ gs : Geometry S,
         hs.quotientEquiv = (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv ∧
         S = R.subgroupOf M ∧
         (normalizer (S : Set M)).pCoreIn 2 = S ∧
         ((T.subgroupOf K).map (componentProjection h)) =
           (R.subgroupOf K).map (componentProjection h) ∧
         gs.b S = 2 ∧
         ∀ (a z t : Vertex S) (_path : CriticalPath S gs a z),
           Adjacent S a t → Adjacent S z t →
           (centralizer (fixedCore S a : Set (FreeAmalgam S))).relIndex (U S z) ≤ (2^n)^2 ∧
           ⁅⁅Z S z,fixedCore S a⁆,fixedCore S a⁆ = ⊥) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl,gs,hgs⟩ :=
    exists_source_star_intrinsic_distance_two h d g hb
  have hshort := (short_and_natural_of_distance_two h d g hb).1
  have hstarshort : IsShort (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype)) :=
    hshort.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm
  have hstar_nsyl : ¬ ∃ S' : Sylow 2 (Sp F), (S' : Subgroup (Sp F)) =
      ((((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)).subgroupOf
          (K.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))).map (componentProjection hs) := by
    intro he
    exact hnsyl ((original_sylow_iff_marked_sylow h).mp
      (hsyl.mp ((original_sylow_iff_marked_sylow hs).mpr he)))
  refine ⟨P,Y,hY,hn,hmin,hs,gs,hquot,hrest,hsat,hmark,hgs,?_⟩
  intro a z t path hat hzt
  exact ⟨original_fixedCore_movement_le_square hs hstarshort hinner hstar_nsyl gs hgs path hat hzt,
    original_fixedCore_quadratic hs hstarshort hinner hstar_nsyl gs hgs path hat hzt⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
