module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.Recognition
public import Theory.Representation.EssentialResidualQuotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.RadiusImage
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Displacement.Transfer
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Radius

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# Unconditional G₂ derived-radius containment

A projected elementary actor of order eight cannot move at most two
binary dimensions on a noncentral G₂ chief factor: the natural offender
costs exactly three. Essential quotient selection applies this obstruction
to arbitrary modules. The Frattini automorphism kernel then lifts it to
finite two-groups and their literal normal quotients.

For the actual radius, `RadiusImage` bounds its derived image at a critical
midpoint by two. The endpoint fixes the radius intersection modulo the
starting seed. Applying the small-index obstruction to that quotient proves
[V', Ltilde] ≤ Z. Residual-plus-edge generation now places V' in every edge
radius, hence in every distance-two kernel. Thus the whole radius image is
elementary of order at most eight, without assuming residual fixation.

These are the first derived-radius and radius-index steps of MS93 (3.8),
printed p.878. The later nonfixed-derived argument and unconditional whole-core
reconstruction remain with qt-e-ms-small-g2-reconstruction. In particular,
fixation modulo Z is not the full `FixedRadiusInput`.

The two `import all` declarations reuse the internal fixed-index and
join-normalization lemmas of the earlier binary radius argument. No private
name occurs in a public statement. Natural G₂ coordinates retain the ATLAS
attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour
open ChapterC BinaryMS.MS93

/-- Small displacement cannot see any noncentral chief factor of a G₂ actor. -/
theorem projected_g2_residual_fixed_of_small_displacement
    {S D V : Type*} [Group S] [Finite S] [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (q : S →* D) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (C : Subgroup D) [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hres : (pResidual 2 S).map q = C)
    (hc : Nat.card C = 6048) (hC : centralizer (C : Set D) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (ρ : Representation (ZMod 2) S V)
    (A : Subgroup S) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card (A.map q) = 8) (hcost : fixedCodim ρ A ≤ 2) :
    pResidual 2 S ≤ ρ.ker := by
  by_contra hn
  obtain ⟨W,_,_,hU,_,hfixed,_⟩ := EssentialResidualQuotient.exists_residual_quotient ρ
    (EssentialResidualQuotient.moved_ne_bot_of_not_le_ker ρ _ hn)
  let U := W.quotientImage (EssentialResidualQuotient.moved ρ (pResidual 2 S))
  let : IsIrreducible U.toRepresentation := hU
  let : Nontrivial U.toSubmodule := Subrepresentation.irreducible_module_nontrivial U.toRepresentation
  let σ := BinaryLinearThree.ResidualFFForms.irreducibleDescent q hq hp U.toRepresentation
  have he : σ.comp q = U.toRepresentation :=
    BinaryLinearThree.ResidualFFForms.irreducibleDescent_comp q hq hp U.toRepresentation
  let : IsIrreducible σ :=
    BinaryLinearThree.ResidualFFForms.irreducibleDescent_irreducible q hq hp U.toRepresentation
  have hnC : ¬ ∀ g ∈ C, ∀ v, σ g v = v := by
    intro hnC
    obtain ⟨u,hu⟩ := exists_ne (0 : U.toSubmodule)
    apply hu
    apply Subtype.ext
    have hu' : (u : V ⧸ W.toSubmodule) ∈ fixedSpace W.quotientRepresentation (pResidual 2 S) := by
      intro g
      have hg : q g ∈ C := hres ▸ mem_map_of_mem q g.property
      have hx := hnC (q g) hg u
      have he' := congrArg (fun τ => τ g u) he
      exact congrArg Subtype.val (he'.symm.trans hx)
    exact show (u : V ⧸ W.toSubmodule) ∈ (⊥ : Submodule (ZMod 2) _) from hfixed ▸ hu'
  have hcostU : fixedCodim σ (A.map q) = fixedCodim U.toRepresentation A := by
    rw [←he]
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  have huBound := fixedCodim_subrepresentation_le W.quotientRepresentation U A
  have hqBound := fixedCodim_quotient_add_subrepresentation_le ρ W A
  obtain ⟨hthree,_⟩ := irreducible_g2_offender_natural σ C hc hC hsq hnC (A.map q)
    (by let := hA; exact IsElementaryAbelian.map q) hcard (by omega)
  omega

/-- Frattini detection lifts the small-displacement obstruction to an entire
finite two-group acted on by the original stabilizer. -/
theorem projected_g2_pGroup_fixed_of_small_index
    {S D P : Type*} [Group S] [Finite S] [Group D] [Finite D]
    [Group P] [Finite P]
    (q : S →* D) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (C : Subgroup D) [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hres : (pResidual 2 S).map q = C)
    (hc : Nat.card C = 6048) (hC : centralizer (C : Set D) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (α : S →* MulAut P) (hP : IsPGroup 2 P)
    (A : Subgroup S) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card (A.map q) = 8)
    (B : Subgroup P) (hB : ∀ a ∈ A, ∀ b ∈ B, α a b = b)
    (hindex : B.index ≤ 4) : ∀ g ∈ pResidual 2 S, α g = 1 := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let f := QuotientGroup.mk' (frattini P)
  let β := (quotientAut (frattini P)).comp α
  let ρ : Representation (ZMod 2) S (Additive (P ⧸ frattini P)) := Offenders.linearize β
  let F : Subgroup (P ⧸ frattini P) := Subgroup.toAddSubgroup.symm (fixedSpace ρ A).toAddSubgroup
  have hBF : B ≤ F.comap f := by
    intro b hb a
    change Additive.ofMul (β a (f b)) = Additive.ofMul (f b)
    rw [show β a (f b) = f (α a b) from quotientAut_apply_mk (frattini P) (α a) b,
      hB a a.property b hb]
  have hcost : fixedCodim ρ A ≤ 2 := by
    have hidx : F.index ≤ B.index := by
      rw [← F.index_comap_of_surjective (QuotientGroup.mk'_surjective (frattini P))]
      exact index_antitone hBF
    rw [ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion.fixedSpace_subgroup_index] at hidx
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact hidx.trans hindex
  have hfixed := projected_g2_residual_fixed_of_small_displacement q hq hp C hres hc hC hsq
    ρ A hA hcard hcost
  have hk (g : pResidual 2 S) : α g ∈ (quotientAut (frattini P)).ker := by
    change β g = 1
    apply MulEquiv.ext
    intro v
    have hh := DFunLike.congr_fun (hfixed g.property) (Additive.ofMul v)
    exact congrArg Additive.toMul hh
  let γ : pResidual 2 S →* (quotientAut (frattini P)).ker :=
    (α.comp (pResidual 2 S).subtype).codRestrict _ hk
  have htriv := (isPPerfect_pResidual 2 (G := S)).hom_eq_one_of_isPGroup
    (isPGroup_quotientAut_frattini_kernel hP) γ
  intro g hg
  exact congrArg (fun f : pResidual 2 S →* (quotientAut (frattini P)).ker =>
    ((f ⟨g,hg⟩ : (quotientAut (frattini P)).ker) : MulAut P)) htriv

/-- A small fixed index modulo a normal subgroup forces the entire residual
commutator into that subgroup. -/
theorem projected_g2_commutator_le_of_small_index
    {S D : Type*} [Group S] [Finite S] [Group D] [Finite D]
    (q : S →* D) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (C : Subgroup D) [C.Normal] [IsSimpleGroup C] [IsQuasisimple C]
    (hres : (pResidual 2 S).map q = C)
    (hc : Nat.card C = 6048) (hC : centralizer (C : Set D) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple C)
    (P X : Subgroup S) [P.Normal] [X.Normal] (hP : IsPGroup 2 P)
    (A : Subgroup S) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card (A.map q) = 8)
    (B : Subgroup S) (hcomm : ⁅P ⊓ B,A⁆ ≤ X)
    (hindex : B.relIndex P ≤ 4) : ⁅P,pResidual 2 S⁆ ≤ X := by
  let f := QuotientGroup.mk' X
  let P' := P.map f
  let : P'.Normal := Normal.map inferInstance f (QuotientGroup.mk'_surjective X)
  let α : S →* MulAut P' := MulAut.conjNormal.comp f
  let B' := (B.subgroupOf P).map (f.subgroupMap P)
  have hB' : ∀ a ∈ A, ∀ b ∈ B', α a b = b := by
    rintro a ha b ⟨y,hy,rfl⟩
    apply Subtype.ext
    change f a * f y * (f a)⁻¹ = f y
    apply mul_inv_eq_iff_eq_mul.mpr
    have hh : ⁅a,(y : S)⁆ ∈ X := by
      have hcomm' : ⁅A,P ⊓ B⁆ ≤ X := by rwa [commutator_comm]
      exact hcomm' (commutator_mem_commutator ha ⟨y.property,hy⟩)
    have hz : ⁅f a,f (y : S)⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hh
    exact commutatorElement_eq_one_iff_mul_comm.mp hz
  have hidx : B'.index ≤ 4 := by
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (B.subgroupOf P).index_ne_zero_of_finite)
      ((B.subgroupOf P).index_map_dvd (f.subgroupMap_surjective P))).trans hindex
  have hfixed := projected_g2_pGroup_fixed_of_small_index q hq hp C hres hc hC hsq
    α (hP.map f) A hA hcard B' hB' hidx
  apply commutator_le.mpr
  intro x hx g hg
  have hh := congrArg (fun a : MulAut P' => (a (f.subgroupMap P ⟨x,hx⟩) : S ⧸ X))
    (hfixed g hg)
  change f g * f x * (f g)⁻¹ = f x at hh
  have hc' : ⁅f x,f g⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mul_inv_eq_iff_eq_mul.mp hh).symm
  apply (QuotientGroup.eq_one_iff _).mp
  change f ⁅x,g⁆ = 1
  rwa [map_commutatorElement]

open ChapterC BinaryMS.MS93 BinaryMS.MS93.NaturalStructure.Exclusion
open Comparison Comparison.CriticalImage
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)
local notation "H" => (L ⊔ R : Subgroup G)
variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))
include h e

/-- At a critical midpoint, the derived radius is residual-fixed modulo
its starting seed, without any prior derived-fixation hypothesis. -/
theorem radius_derived_residual_commutator_le_seed_at_critical
    (hb : (geometry h).b T = 4)
    (a z : Vertex T) (ha : color T a = false)
    (hc : CriticalPair T a z ((geometry h).exists_critical a ha))
    (c : Vertex T) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (hcz : (cosetGraph T).dist c z = 2) :
    ⁅⁅V T a,V T a⁆,Ltilde T a⁆ ≤ Z T a := by
  let S := stabilizer T a
  let := finite_stabilizer T a
  let P := (⁅V T a,V T a⁆).subgroupOf S
  let X := (Z T a).subgroupOf S
  let A := (Z T z).subgroupOf S
  let B := (Q T c).subgroupOf S
  have hVQ := (geometry h).V_le_Q (by omega) a ha
  have hDV : ⁅V T a,V T a⁆ ≤ V T a :=
    le_normalizer_iff_commutator_le_left.mp (V T a).le_normalizer
  have hDS : ⁅V T a,V T a⁆ ≤ S := hDV.trans (hVQ.trans (fun _ hx => hx.1))
  let : P.Normal := normal_subgroupOf_of_le_normalizer (by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (V_normalized a hg)])
  let : X.Normal := (geometry h).Z_normal a
  have hP : IsPGroup 2 P := ((radius_isPGroup h (by omega) a ha).to_le hDV).comap_subtype
  have hz := critical_endpoint_color T a ha _ hc
  have hrev := critical_reverse T (geometry h) (edgeCentralizer h e) a ha (by
    rw [(geometry h).distance_constant a ha]; exact (positive_even h e).1) z hz hc
  have hAS := Z_le_stabilizer_of_dist_le z ((geometry h).exists_critical z hz) hrev.1.le
  let := (geometry h).Z_elementary (by omega) z hz
  have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hAS
  obtain ⟨d⟩ := endpointModel_knownSimple h e ha
  have hAc : Nat.card (A.map d.actor) = 8 := critical_image_card_eight h e z a hz hrev d
  have hcomm : ⁅P ⊓ B,A⁆ ≤ X := by
    have hi := radius_intersection_seed h e (by omega) a z ha hc c hcColor hcz
    have hh : ⁅(P ⊓ B).map S.subtype,A.map S.subtype⁆ ≤ Z T a :=
      (commutator_mono (by
        rintro x ⟨y,hy,rfl⟩
        exact ⟨hDV hy.1,hy.2⟩) (by rintro x ⟨y,hy,rfl⟩; exact hy)).trans hi
    intro x hx
    exact hh (by rw [←map_commutator]; exact mem_map_of_mem S.subtype hx)
  have hidx : B.relIndex P ≤ 4 := by
    have hh : B.relIndex P = (Q T c).relIndex (⁅V T a,V T a⁆) := by
      change ((Q T c).comap S.subtype).relIndex P = _
      rw [relIndex_comap,map_subgroupOf_eq_of_le hDS]
    rw [hh]
    exact (radius_derived_index_le_two h e hb a c ha hcColor hac).trans (by decide)
  obtain ⟨i,hi,hir,_,_,hiQ⟩ :=
    RankTwo.Sp4Four.SourceComparison.vertex_coordinates_with_kernel T
      (edge_two_group h) (core_le_edge h) ha
  let j : H ≃* S := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hir)
  have hj (s : S) : i (j.symm s) = s.val := congrArg Subtype.val (j.apply_symm_apply s)
  let q₀ := QuotientGroup.mk' (pCore 2 H)
  let q := q₀.comp j.symm.toMonoidHom
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp j.symm.surjective
  have hqk : q.ker = (pCore 2 H).comap j.symm.toMonoidHom := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
  have hp : IsPGroup 2 q.ker := by
    rw [hqk]
    exact pCore_isPGroup.comap_of_injective j.symm.toMonoidHom j.symm.injective
  have hqQ : q.ker.map S.subtype = Q T a := by
    rw [hqk,←hiQ]
    apply le_antisymm
    · rintro _ ⟨s,hs,rfl⟩
      exact ⟨j.symm s,hs,hj s⟩
    · rintro _ ⟨s,hs,rfl⟩
      refine ⟨j s,?_,rfl⟩
      change j.symm (j s) ∈ pCore 2 H
      rwa [j.symm_apply_apply]
  have hk : q.ker = d.actor.ker :=
    (map_injective S.subtype_injective) (hqQ.trans d.actor_kernel.symm)
  have hcA : Nat.card (A.map q) = 8 := by
    rw [←relIndex_ker,hk,relIndex_ker]
    exact hAc
  let C := quotientComponent (L := L) (R := R)
  let := (quotientComponent_structure h e).1
  let := (quotientComponent_structure h e).2.1
  let := (quotientComponent_structure h e).2.2.1
  have hres : (pResidual 2 S).map q = C := by
    change (pResidual 2 S).map (q₀.comp j.symm.toMonoidHom) = C
    rw [←map_map,map_pResidual_of_surjective 2 j.symm.toMonoidHom j.symm.surjective,
      relative_residual h]
    rfl
  have hout := projected_g2_commutator_le_of_small_index q hq hp C hres
    (quotientComponent_card h e) (quotientComponent_structure h e).2.2.2
    (quotientComponent_sqtk h) P X hP A hA hcA B hcomm hidx
  have hm := map_mono (f := S.subtype) hout
  rw [map_commutator,map_subgroupOf_eq_of_le hDS,
    map_subgroupOf_eq_of_le (Z_le_stabilizer T a)] at hm
  exact hm

/-- The derived radius is residual-fixed modulo its seed at every vertex
of the G₂ orbit. -/
theorem radius_derived_residual_commutator_le_seed
    (hb : (geometry h).b T = 4) (a : Vertex T) (ha : color T a = false) :
    ⁅⁅V T a,V T a⁆,Ltilde T a⁆ ≤ Z T a := by
  obtain ⟨z,hcrit⟩ := criticalPair_exists T a ((geometry h).exists_critical a ha)
  have hd : (cosetGraph T).dist a z = 4 :=
    hcrit.1.trans (((geometry h).distance_constant a ha).trans hb)
  obtain ⟨t,hat,htz⟩ := exists_adjacent_dist_sub_one T a z (by omega)
  obtain ⟨c,htc,hcz⟩ := exists_adjacent_dist_sub_one T t z (by omega)
  have hcColor : color T c = false := by
    have ht := adjacent_color_ne T hat
    have hc := adjacent_color_ne T htc
    rw [ha] at ht
    cases hc' : color T c <;> cases ht' : color T t <;> simp_all
  have hat1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)
  have htc1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr htc)
  have h₁ := (cosetGraph_connected T).dist_triangle (u := a) (v := t) (w := c)
  have h₂ := (cosetGraph_connected T).dist_triangle (u := a) (v := c) (w := z)
  exact radius_derived_residual_commutator_le_seed_at_critical h e hb a z ha hcrit
    c hcColor (by omega) (by omega)

omit e in
/-- Edge generation needs only residual fixation modulo the starting seed. -/
theorem radius_derived_le_edge_of_fixed_modulo_seed
    (hb : 2 < (geometry h).b T)
    (a t : Vertex T) (ha : color T a = false) (hat : Adjacent T a t)
    (hfixed : ⁅⁅V T a,V T a⁆,Ltilde T a⁆ ≤ Z T a) :
    ⁅V T a,V T a⁆ ≤ V T t := by
  let N := Z T a ⊔ ⁅V T a,V T t⁆
  have htV := edge_radius_le_radius ha hat
  have hVQ := (geometry h).V_le_Q hb a ha
  have hVS : V T a ≤ stabilizer T a := hVQ.trans (fun _ hx => hx.1)
  have hQtS : Q T t ≤ stabilizer T a := CriticalCriterion.edge_le_stabilizer T ha hat
  have hn : stabilizer T a ≤ normalizer N := by
    rw [←local_generation_edge h ha hat]
    apply sup_le
    · exact normalizes_sup_of_commutator_le _ _ _
        ((Ltilde_le_stabilizer a).trans (Z_normalized T a))
        ((commutator_mono (commutator_mono le_rfl htV) le_rfl).trans hfixed)
    · intro x hx
      change x ∈ normalizer (Z T a ⊔ ⁅V T a,V T t⁆ : Subgroup (FreeAmalgam T))
      rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (Z_normalized T a (hQtS hx)),
        mem_normalizer_iff_map_conj_eq.mp (V_normalized a (hQtS hx)),
        mem_normalizer_iff_map_conj_eq.mp (V_normalized t hx.1)]
  have hbound (u : Vertex T) (hau : Adjacent T a u) : ⁅V T a,V T u⁆ ≤ N := by
    obtain ⟨g,hg,hgu⟩ := stabilizer_transitive_neighbors T a hat hau
    have he := mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer T a).inv_mem hg))
    change (Z T a ⊔ ⁅V T a,V T t⁆).map (MulAut.conj g⁻¹).toMonoidHom = N at he
    rw [Subgroup.map_sup,map_commutator,←Z_act,←V_act,←V_act,show act T g a = a from hg,hgu] at he
    exact (show ⁅V T a,V T u⁆ ≤ Z T a ⊔ ⁅V T a,V T u⁆ from le_sup_right).trans he.le
  have hDN : ⁅V T a,V T a⁆ ≤ N := by
    let I := {d : Vertex T // color T d = false ∧ (cosetGraph T).dist d a ≤ 2}
    have heq : V T a = ⨆ d : I, Z T d.val := by
      apply le_antisymm
      · apply radius_le_of_m_ball ha
        intro d hd hdist
        exact le_iSup_of_le (⟨d,hd,hdist⟩ : I) le_rfl
      · apply iSup_le
        intro d
        exact le_iSup_of_le d.val (le_iSup_of_le d.property.2 le_rfl)
    conv_lhs => lhs; rw [heq]
    apply commutator_iSup_le_of_relative_normal (stabilizer T a) (V T a) N _ hn
    · intro d
      have hZV : Z T d.val ≤ V T a :=
        le_iSup_of_le d.val (le_iSup_of_le d.property.2 le_rfl)
      exact hZV.trans hVS
    · intro d
      rw [commutator_comm]
      by_cases hda : d.val = a
      · have hZa : Z T a ≤ V T t := le_iSup_of_le a (le_iSup_of_le
          ((SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)).le.trans
            (by decide : 1 ≤ 2)) le_rfl)
        rw [hda]
        exact (commutator_mono le_rfl hZa).trans le_sup_right
      · have htwo : (cosetGraph T).dist a d.val = 2 := by
          have hne : (cosetGraph T).dist a d.val ≠ 0 := by
            intro hz
            exact hda ((cosetGraph_connected T).dist_eq_zero_iff.mp hz).symm
          have heven : Even ((cosetGraph T).dist a d.val) := by
            obtain ⟨w,hw⟩ := (cosetGraph_connected T).exists_walk_length_eq_dist a d.val
            rw [←hw,walk_even_iff_color_eq,ha,d.property.1]
          have hdist : (cosetGraph T).dist a d.val ≤ 2 := by
            simpa only [SimpleGraph.dist_comm] using d.property.2
          rw [Nat.even_iff] at heven
          omega
        obtain ⟨u,hau,hdu⟩ := exists_common_neighbor_of_dist_two T a d.val htwo
        have hdVu : Z T d.val ≤ V T u := le_iSup_of_le d.val (le_iSup_of_le
          ((SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hdu)).le.trans
            (by decide : 1 ≤ 2)) le_rfl)
        exact (commutator_mono le_rfl hdVu).trans (hbound u hau)
  apply hDN.trans
  apply sup_le
  · exact le_iSup_of_le a (le_iSup_of_le
      ((SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj T _ _).mpr hat)).le.trans
        (by decide : 1 ≤ 2)) le_rfl)
  apply le_normalizer_iff_commutator_le_right.mp
  have ht : color T t = true := by
    have hne := adjacent_color_ne T hat
    cases hc : color T t <;> simp_all
  exact (hVQ.trans (Q_le_adjacent_h T ht hat)).trans
    ((show Q T t ≤ stabilizer T t from fun _ hx => hx.1).trans (V_normalized t))


/-- The whole derived radius lies in every incident edge radius. -/
theorem radius_derived_le_edge
    (hb : (geometry h).b T = 4)
    (a t : Vertex T) (ha : color T a = false) (hat : Adjacent T a t) :
    ⁅V T a,V T a⁆ ≤ V T t :=
  radius_derived_le_edge_of_fixed_modulo_seed h (by omega) a t ha hat
    (radius_derived_residual_commutator_le_seed h e hb a ha)

/-- The unconditional midpoint-kernel containment from MS93 (3.8), p.878. -/
theorem radius_derived_le_midpoint
    (hb : (geometry h).b T = 4)
    (a c : Vertex T) (ha : color T a = false) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) : ⁅V T a,V T a⁆ ≤ Q T c := by
  obtain ⟨t,hat,hct⟩ := exists_common_neighbor_of_dist_two T a c hac
  exact (radius_derived_le_edge h e hb a t ha hat).trans
    ((edge_radius_le_radius hcColor hct).trans ((geometry h).V_le_Q (by omega) c hcColor))

/-- The whole radius has elementary image at a distance-two vertex. -/
theorem radius_image_elementary_at_distance_four
    (hb : (geometry h).b T = 4)
    (a c : Vertex T) (ha : color T a = false) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) (d : EndpointModel T c) :
    IsElementaryAbelian 2 (image d (V T a)) :=
  radius_image_elementary h (by omega) a c ha hac
    (radius_derived_le_midpoint h e hb a c ha hcColor hac) d

/-- The actual radius index is at most eight, without residual-fixation data. -/
theorem radius_index_le_eight
    (hb : (geometry h).b T = 4)
    (a c : Vertex T) (ha : color T a = false) (hcColor : color T c = false)
    (hac : (cosetGraph T).dist a c = 2) : (Q T c).relIndex (V T a) ≤ 8 := by
  obtain ⟨d⟩ := endpointModel_knownSimple h e hcColor
  exact radius_index_le_eight_of_derived_le h (by omega) a c ha hac
    (radius_derived_le_midpoint h e hb a c ha hcColor hac) d

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour
