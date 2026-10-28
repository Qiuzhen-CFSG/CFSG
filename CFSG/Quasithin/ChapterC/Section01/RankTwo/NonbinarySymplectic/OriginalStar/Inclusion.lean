module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.StarDualCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CriticalRefinement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.StarQuotient
public import Theory.Representation.SymplecticFourOrthogonalCover.DualFixed

/-!
# The original star lies in the moving layer and full fixed core

The first star comparison and full-core displacement construct the actual
original star quotient with its complete fixed kernel. Compatible natural
coordinates give a dual cover, and the critical endpoint admits no preserved
orthogonal refinement. The star centralizes that endpoint, so dual-cover
fixedness puts its image in the natural submodule. Lifting through the exact
kernel gives Z-star-beta <= U-alpha D-alpha on the original graph.

No characteristic replacement, saturation or degree-two conclusion is used.
Source: MS93 (3.4), printed p.869.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
universe u w
variable {H : Type u} {F : Type w} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

theorem Input.original_critical_actor_no_refinement
    {E W : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (hEF : Nat.card E = Nat.card F)
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (j : Multiplicative W →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z) (β : Z R a →* L (K := E))
    (hβ : ∀ x : Z R a, ∀ w : W,
      j (Multiplicative.ofAdd (σ (β x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (hcard : Nat.card β.range = (Q R z).relIndex (Z R a)) :
    ¬ ∃ c : Natural (K := E), ∀ b : β.range, ∀ v,
      refinement c (binaryNatural b.val v) = refinement c v := by
  have hF : 2 < Nat.card E := by
    rw [hEF,h.field_card]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let A := β.range.map (commutator (Sp E)).subtype
  have hAcard : Nat.card A = Nat.card β.range :=
    (Nat.card_congr (β.range.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm
  have hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector E, x • (y • v-v)=y • v-v := by
    have hh := critical_embedded_natural_actor_quadratic path hb σ p hp j hj hjr β hβ
    rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩ v
    exact hh x hx y hy v
  have hnot : ¬ ∃ c : Vector E, ∀ b : A, ∀ v, refinement c (b.val • v)=refinement c v := by
    by_cases hsmall : (Q R z).relIndex (Z R a) < Nat.card F^2
    · have hi := h.original_small_critical_indices_eq_field path hb hsmall
      have hc : Nat.card β.range = Nat.card E := hcard.trans (hi.1.trans hEF.symm)
      have hCa : C R a = Q R a := MSCentralOrbit.C_eq_Q _
        (h.radical.isPGroup) (h.radical.twoCore_le)
        (h.omegaOrbit_centralizer) a path.start_color
      have hr := critical_root_coordinates_of_reciprocal_index_field path hb hCa hF
        σ p hp j hj hjr β hβ hc (hi.2.trans hEF.symm)
      exact no_refinement_of_displacement_one hF A (hAcard.trans hc) hr.1 hq
    · exact no_refinement_of_large_quadratic hF A
        (by rw [hAcard,hcard,hEF]; omega) hq
  rintro ⟨c,hc⟩
  apply hnot
  refine ⟨c,?_⟩
  rintro ⟨b,⟨b,hb,rfl⟩⟩ v
  exact hc ⟨b,hb⟩ v

open ChapterB.QuasisimpleSource MSCentralOrbit

/-- The full vertex marking supplies a refinement-free critical actor in the
same symplectic component that marks the original natural cover. -/
theorem Input.original_refinement_free_inner_actor
    {E J V : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (hEF : Nat.card E = Nat.card F)
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := E)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R)
    (hj : Function.Injective j) (hjr : j.range = U R z)
    (κ : stabilizer R z →* J)
    (hkQ : κ.ker.map (stabilizer R z).subtype = Q R z)
    (hconj : ∀ (g : stabilizer R z) (v : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
        (g : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam R)⁻¹) :
    ∃ β : Z R a →* L (K := E),
      (∀ (x : Z R a) (hx : (x : FreeAmalgam R) ∈ stabilizer R z),
        (e.groupEquiv.symm (β x) : J) = κ ⟨x,hx⟩) ∧
      ¬ ∃ c : Natural (K := E), ∀ b : β.range, ∀ v,
        refinement c (binaryNatural b.val v) = refinement c v := by
  have hAS : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAS)
  have hδcard : Nat.card δ.range = (Q R z).relIndex (Z R a) :=
    CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison.quotient_image_card _ _ _ hAS κ hkQ
  have hδ (x : Z R a) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam R)⁻¹ :=
    hconj (inclusion hAS x) v
  have hFl : 2 < Nat.card E := by
    rw [hEF,h.field_card]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hAut : Nat.card (E ≃+* E) < Nat.card δ.range := by
    rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card E = 2^n by rw [hEF,h.field_card]),hδcard]
    have hdeg : n < Nat.card F := by rw [h.field_card]; exact n.lt_two_pow_self
    exact hdeg.trans_le (h.original_critical_indices_ge_field path hb).1
  obtain ⟨β,hβcard,hβmark,hβact⟩ := critical_inner_model_actor_of_ringAut_card_lt
    path hb hFl s e hp hcent j hj hjr δ hδ hAut
  exact ⟨β,fun x hx => hβmark x,
    h.original_critical_actor_no_refinement hEF path hb
      (MovedSection.coverAction s e) (MovedSection.coverProjection s e) hp
      j hj hjr β hβact (hβcard.trans hδcard)⟩


/-- The star modulo its full component centralizer is an elementary module
at every positive critical distance, even when the whole star is nonabelian. -/
theorem Input.original_sourceStarQuotient_over
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    {J : Type*} [Group J] (κ : stabilizer R (alpha R) →* J)
    (hκ : Function.Surjective κ)
    (hκQ : κ.ker.map (stabilizer R (alpha R)).subtype =
      Q R (alpha R)) :
    ∃ s : SourceStarQuotient R Y J, s.quotient = κ := by
  let S := stabilizer R (alpha R)
  let A := sourceStarAlpha R Y
  let L₀ := Ltilde R (alpha R)
  let U₀ := U R (alpha R)
  let C₀ := A ⊓ centralizer (L₀ : Set (FreeAmalgam R))
  have hAS : A ≤ S := sourceStarAlpha_le_stabilizer _ _
  have hAQ := h.original_sourceStarAlpha_le_own_core geometry hb Y P hY hn
  have hLS : L₀ ≤ S := Ltilde_le_stabilizer _
  have hSL : S ≤ normalizer (L₀ : Set (FreeAmalgam R)) := by
    have ht := le_normalizer_map (H := pResidual 2 S) S.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at ht
    exact ht
  have hNC : normalizer (L₀ : Set (FreeAmalgam R)) ≤
      normalizer (centralizer (L₀ : Set (FreeAmalgam R)) : Set _) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
  have hSN : S ≤ normalizer (C₀ : Set (FreeAmalgam R)) :=
    (le_inf (sourceStarAlpha_normalized _ _)
      (hSL.trans hNC)).trans
      inf_normalizer_le_normalizer_inf
  have hAL : A ≤ normalizer (L₀ : Set (FreeAmalgam R)) :=
    hAS.trans hSL
  have hC : C₀ = A ⊓ fixedCore R (alpha R) := by
    ext x
    exact ⟨fun hx => ⟨hx.1,hAQ hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  let : (C₀.subgroupOf A).Normal :=
    normal_subgroupOf_of_le_normalizer (hAS.trans hSN)
  have hN : C₀.subgroupOf A = (centralizer (L₀ : Set (FreeAmalgam R))).subgroupOf A := by
    ext a
    exact ⟨fun ha => ha.2,fun ha => ⟨a.property,ha⟩⟩
  let : ((centralizer (L₀ : Set (FreeAmalgam R))).subgroupOf A).Normal :=
    hN ▸ inferInstance
  let : IsElementaryAbelian 2 U₀ := h.vertex_moving_elementary rfl
  let : IsElementaryAbelian 2 (A ⧸ (centralizer (L₀ : Set (FreeAmalgam R))).subgroupOf A) :=
    Subgroup.central_displacement_quotient_elementary A L₀ U₀
      (h.original_sourceStarAlpha_commutator_le_U geometry hb Y P hY hn)
      (commutator_eq_bot_iff_le_centralizer.mp
        ((commutator_mono (U_le_Z _) hAQ).trans_eq (Z_centralizes_Q _ _ rfl) |>.antisymm bot_le))
  let : IsElementaryAbelian 2 (A ⧸ C₀.subgroupOf A) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.quotientMulEquivOfEq hN).symm.toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq hN).symm.surjective
  obtain ⟨z,path,hfirst⟩ := exists_original_critical_path_through_beta geometry hb
  have hbound := h.original_sourceStarAlpha_core_displacement geometry hb
    path hfirst Y P hY hn
  obtain ⟨σ,c,hc⟩ := BinaryConjugationSection.exists_descended_actor S A C₀ hAS inf_le_left
    (sourceStarAlpha_normalized _ _) hSN κ hκ (by
      intro a ha x hx
      have haQ : (a : FreeAmalgam R) ∈ Q R (alpha R) :=
        hκQ ▸ mem_map_of_mem S.subtype ha
      have hm : ⁅(a : FreeAmalgam R),x⁆ ∈ ⁅A,Q R (alpha R)⁆ := by
        rw [commutator_comm]
        exact commutator_mem_commutator haQ hx
      refine ⟨?_,(hbound hm).2⟩
      rw [commutatorElement_def]
      exact A.mul_mem ((mem_normalizer_iff.mp
        (sourceStarAlpha_normalized R Y a.property) x).mp hx) (A.inv_mem hx))
  let : Group.IsPerfect K := (h.component).perfect
  let : Group.IsPerfect (Ltilde R (alpha R)) := by
    rw [Ltilde_alpha,h.residual_eq]
    exact Group.IsPerfect.map _
  have hfixed := BinaryConjugationSection.fixed_section_eq_bot S A L₀ hLS hAL κ σ c
  let : Finite S := finite_stabilizer _ _
  let : Finite A := Finite.of_injective (inclusion hAS) (inclusion_injective _)
  refine ⟨{
    Carrier := Additive (A ⧸ C₀.subgroupOf A)
    quotient := κ
    quotient_surjective := hκ
    quotient_kernel := hκQ
    action := σ
    sectionData := ?_
    fixed_eq_bot := hfixed },rfl⟩
  rw [←hC]
  exact c


/-- The actual star modulo the full fixed core is a dual cover of the natural
module over the original field degree. The natural inclusion has exactly the
image of the original moving subgroup. -/
theorem Input.original_sourceStarDualCover
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    ∃ E : ChapterB.QuasisimpleSource.BinaryField, E.degree = n ∧
    ∃ s : SourceStarQuotient R Y (H ⧸ pCore 2 H),
    ∃ γ : L (K := E.Carrier) →* (H ⧸ pCore 2 H),
      Function.Injective γ ∧
      γ.range = K.map (QuotientGroup.mk' (pCore 2 H)) ∧
      ((Ltilde R (alpha R)).subgroupOf
        (stabilizer R (alpha R))).map s.quotient = γ.range ∧
    ∃ i : (binaryNatural (K := E.Carrier)).IntertwiningMap (s.action.comp γ),
      Function.Injective i ∧ IsDualCover i.range ∧
      (∀ w, w ∈ i.toLinearMap.range ↔
        ∃ a : sourceStarAlpha R Y, (a : FreeAmalgam R) ∈
          U R (alpha R) ∧ (s.sectionData.coordinates a).toAdd = w) ∧
      ∀ (z : Vertex R) (_path : CriticalPath R geometry (alpha R) z),
        ∃ β : Z R z →* L (K := E.Carrier),
          (∀ (x : Z R z) (hx : (x : FreeAmalgam R) ∈
            stabilizer R (alpha R)), γ (β x) = s.quotient ⟨x,hx⟩) ∧
          ¬ ∃ c : Natural (K := E.Carrier), ∀ b : β.range, ∀ v,
            Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors.refinement c
              (binaryNatural b.val v) =
            Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors.refinement c v := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let C₀ := K.map q
  let : C₀.Normal := (h.component_image_structure).2.1
  let ρ₀ := NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.centralOmega_centralizer).symm)
  let s₀ := MovedSection.ofNormal ρ₀ C₀
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex (a := alpha R) rfl
  change ActionEquiv (s₀.action.comp C₀.subtype) (binaryNatural (K := E.Carrier)) at e
  change IsCover (MovedSection.coverProjection s₀ e) at he
  change Multiplicative s₀.space.toSubmodule →* FreeAmalgam R at j
  obtain ⟨s,hs⟩ := h.original_sourceStarQuotient_over geometry hb Y P hY hn κ hκ hκQ
  let γ : L (K := E.Carrier) →* (H ⧸ pCore 2 H) :=
    C₀.subtype.comp e.groupEquiv.symm.toMonoidHom
  have hγ : γ.range = C₀ := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.groupEquiv.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hγinj : Function.Injective γ := Subtype.val_injective.comp e.groupEquiv.symm.injective
  obtain ⟨i,hi,hdual,hrange⟩ := marked_star_dual_cover R Y s₀ e he j hjr s
    (by rw [hs]; exact hκL) (by intro g v; rw [hs]; exact hconj g v) hker
    (h.original_sourceStarAlpha_le_own_core geometry hb Y P hY hn)
    (h.original_sourceStarAlpha_commutator_le_U geometry hb Y P hY hn)
  refine ⟨E,hE,s,γ,hγinj,hγ,?_,i,hi,hdual,hrange,?_⟩
  · rw [hs,hγ]
    exact hκL
  · intro z path
    have hpos : 0 < geometry.b R := by omega
    have hedge := MSCentralOrbit.edgeCentralizerCondition R
      (h.radical.isPGroup) (h.radical.twoCore_le) (h.omegaOrbit_centralizer)
    let rev : CriticalPath R geometry z (alpha R) := {
      start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R geometry hedge (alpha R) rfl
        (by rwa [geometry.distance_constant (alpha R) rfl]) z path.end_color path.critical }
    obtain ⟨β,hβmark,hβno⟩ := h.original_refinement_free_inner_actor (ρ := ρ₀) (B := C₀)
      (show Nat.card E.Carrier = Nat.card F by rw [E.card_eq,hE,h.field_card]) rev hpos
      s₀ e he (h.component_image_structure).2.2.2.2 j hj hjr κ hκQ hconj
    refine ⟨β,?_,hβno⟩
    intro x hx
    rw [hs]
    exact hβmark x hx


/-- The second source star bound, for the original radical at
arbitrary nonbinary degree. The entire fixed core is retained. -/
theorem Input.original_starSpan_le_moving_fixed
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤
      normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    (starSpan R Y).map (embedS R) ≤
      U R (alpha R) ⊔ fixedCore R (alpha R) := by
  obtain ⟨E,hE,s,γ,hγ,hγC,hmap,i,hi,hdual,hrange,hcritical⟩ :=
    h.original_sourceStarDualCover geometry hb Y P hY hn
  obtain ⟨z,path,hfirst⟩ := exists_original_critical_path_through_beta geometry (by omega)
  obtain ⟨β,hβ,hno⟩ := hcritical z path
  have hc := h.original_starSpan_centralizes_endpoint geometry (by omega)
    path hfirst Y P hY hn
  have hBA : (starSpan R Y).map (embedS R) ≤ sourceStarAlpha R Y := by
    have hh := (sourceStarAlpha_le_iff R Y (sourceStarAlpha R Y)).mp
      le_rfl (1 : Mbar R)
    have he : (MulAut.conj (1 : FreeAmalgam R)).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change 1*x*1⁻¹=x
      simp
    simpa only [OneMemClass.coe_one,he,Subgroup.map_id] using hh
  have hZS : Z R z ≤ stabilizer R (alpha R) := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant _ rfl,
      geometry.distance_constant _ path.end_color]
  intro b hbB
  let bA : sourceStarAlpha R Y := ⟨b,hBA hbB⟩
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
    have hcomm := hc hbB x x.property
    exact (congrArg (fun t => t*(x : FreeAmalgam R)⁻¹) hcomm).trans
      (mul_inv_cancel_right b (x : FreeAmalgam R))
  have hmem := dualCover_fixed_le_natural_of_no_refinement i hi hdual β.range hno hfix
  obtain ⟨u,hu,he⟩ := (hrange _).mp hmem
  have hdiff : (u⁻¹*bA : sourceStarAlpha R Y) ∈ s.sectionData.coordinates.ker := by
    change s.sectionData.coordinates (u⁻¹*bA) = 1
    rw [map_mul,map_inv,show s.sectionData.coordinates u = s.sectionData.coordinates bA
      from Multiplicative.toAdd.injective he,inv_mul_cancel]
  rw [s.sectionData.kernel_eq] at hdiff
  have hd : ((u⁻¹*bA : sourceStarAlpha R Y) : FreeAmalgam R) ∈
      fixedCore R (alpha R) := hdiff.2
  have hmul := mul_mem (mem_sup_left hu) (mem_sup_right hd)
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_cancel_left] using hmul


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
