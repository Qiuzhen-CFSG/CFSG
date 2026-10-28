module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.PositiveStabilizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.BinaryPositive
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Orthogonal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.RankOneExclusion
public import Theory.SpecificGroups.BinaryLinear.SylowNormalizerCover

/-!
# Excluding every original binary-three natural cover

The binary containing action identifies the literal component head with
SL₄(2) or SL₅(2), hence makes its Sylow two-subgroup self-normalizing.
Conjugate the component back by the original exchanger and intersect with
N_G(L). Its Sylow lies in the original half-Sylow, and this intersection
fixes the original nonkernel vector. The opposite point stabilizer supplies
a cubic; the prime-to-three residual identity places it in that intersection.
The A₄ stabilizer obstruction in PositiveStabilizer is now a contradiction.

The prior A₇ exclusion and zero-kernel natural-three endgame therefore close
every natural cover. The original context consequently has local Thompson
fixedness and zero full fixed layer. At cubic component order it also has
full-module Thompson fixedness. General quiet preparation and the retained
four-natural row remain with qt-d-10-nona5-point-constrained.
Source: Aschbacher--Smith10.2.9, printed pp.751--752.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02 ChapterB.InternalThompsonAction
open scoped IsMulCommutative MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The exact original binary containing head makes every intrinsic Sylow
self-normalizing, including the two-core kernel. -/
theorem Context.component_sylow_self_normalizing_of_binary_actor (c : Context D t v I)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        SL(d,ZMod 2)) (S : Sylow 2 I) : normalizer (S : Set I) = S := by
  let E := (c.binaryActorQuotient hd e).trans (BinaryLinear.OuterCyclic.slEquivLinear d)
  let f := E.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hf : Function.Surjective f := E.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ E.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  rcases hd with rfl | rfl
  · exact BinaryLinear.SylowNormalizerCover.normalizer_sylow_eq_of_two_kernel f hf hk S
  · exact BinaryLinear.SylowNormalizerCover.normalizer_sylow_eq_of_two_kernel f hf hk S

/-- Positive natural covers exclude either binary containing degree directly
on the original point and opposite component, without a full-orbit premise. -/
theorem Context.no_positive_binaryThree_of_binary_actor (c : Context D t v I)
    (hmodel : Selection.BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : letI := c.reduced.normal
      ((I.subgroupOf (pointJoin T v I)).map (actionMk (internalModule D v I))) ≃*
        SL(d,ZMod 2)) : False := by
  let W := ⁅D.fullModule,L⁆
  let B := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let f := MulAut.conj t
  obtain ⟨w,hw,hwv⟩ := c.escaping.v_mem
  change f w = v at hwv
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem)
  have hv0 : v ∉ centralizer (localOrbit T L : Set G) :=
    (Selection.escaping_point_stabilizes D c.escaping.half_unique
      (Selection.BinaryThree.fixed_layer_centralizes_half_sylow D hmodel
        c.escaping.t_mem c.escaping.t_not_normalizes c.escaping.crossed)
      c.escaping.t_mem c.escaping.t_not_normalizes c.escaping.crossed
      c.escaping.v_mem c.escaping.v_ne
      (fun h => c.escaping.escapes (c.escaping.le_centralizer.trans h))).1
  have hwn : w ∉ centralizer (L : Set G) := by
    intro h
    have hk : v ∈ (sourceMovedFixed D).map f.toMonoidHom := ⟨w,⟨hw,h⟩,hwv⟩
    have hf := Selection.BinaryThree.fixed_layer_eq_moved_kernels D
      c.escaping.t_mem c.escaping.t_not_normalizes c.escaping.crossed
    exact hv0 (hf.ge ((show (sourceMovedFixed D).map f.toMonoidHom ≤
      sourceMovedFixed D ⊔ (sourceMovedFixed D).map f.toMonoidHom from le_sup_right) hk)).2
  have hBW : B ≤ normalizer (W : Set G) :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right).trans
      (source_moved_normalizer_local_containment D)
  have hTB : (T : Subgroup G) ≤ normalizer (B : Set G) := by
    have hi : (B.subgroupOf (T : Subgroup G)).index = 2 := by
      have he : B.subgroupOf (T : Subgroup G) =
          (normalizer (L : Set G)).subgroupOf (T : Subgroup G) := by
        ext x
        exact ⟨fun h => h.2,fun h => ⟨x.property,h⟩⟩
      rw [he]
      exact source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn
    let : (B.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hi
    exact (normal_subgroupOf_iff_le_normalizer (show B ≤ (T : Subgroup G) from inf_le_left)).mp
      inferInstance
  let J := I.map f.symm.toMonoidHom
  let H := J ⊓ normalizer (L : Set G)
  have hHJ : H ≤ J := inf_le_left
  have hHL : H ≤ normalizer (L : Set G) := inf_le_right
  have hHW : H ≤ normalizer (W : Set G) :=
    (le_inf (hHL.trans c.escaping.component_normalizer) hHL).trans
      (source_moved_normalizer_local_containment D)
  have hJfix : J ≤ centralizer ({w} : Set G) := by
    rintro _ ⟨z,hz,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply f.injective
    change f (f.symm z * w) = f (w * f.symm z)
    simp only [map_mul,f.apply_symm_apply,hwv]
    exact mem_centralizer_singleton_iff.mp (c.escaping.le_centralizer hz)
  let K := I.subgroupOf (pointJoin T v I)
  let a : K ≃* I := subgroupOfEquivOfLe le_sup_left
  let b : I ≃* J := I.equivMapOfInjective f.symm.toMonoidHom f.symm.injective
  have af := c.actionFacts_of_binaryThreeNatural hmodel
  obtain ⟨_,R,hR,_⟩ := af.small_local
  let RI := R.mapSurjective (f := a.toMonoidHom) a.surjective
  let RJ := RI.mapSurjective (f := b.toMonoidHom) b.surjective
  have hRI : (RI : Subgroup I) = (T : Subgroup G).subgroupOf I := by
    change (R : Subgroup K).map a.toMonoidHom = _
    rw [hR]
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz
    · intro hx
      exact ⟨a.symm x,hx,a.apply_symm_apply x⟩
  have hRJH : (RJ : Subgroup J) ≤ H.subgroupOf J := by
    rintro _ ⟨z,hz,rfl⟩
    have hzT : (z : G) ∈ (T : Subgroup G) := by
      change z ∈ (T : Subgroup G).subgroupOf I
      rwa [←hRI]
    have hzS : (z : G) ∈ pointSylow T v := ⟨hzT,c.escaping.le_centralizer z.property⟩
    have hzB : (z : G) ∈ B := ⟨hzT,c.escaping.sylow_normalizes hzS⟩
    have hfB : f.symm (z : G) ∈ B := by
      simpa only [f,MulAut.conj_symm_apply,inv_inv] using
        (mem_normalizer_iff.mp (hTB ((T : Subgroup G).inv_mem c.escaping.t_mem))
          (z : G)).mp hzB
    exact ⟨(b z).property,hfB.2⟩
  have hRIn := c.component_sylow_self_normalizing_of_binary_actor hd e RI
  change normalizer ((RI : Subgroup I) : Set I) = (RI : Subgroup I) at hRIn
  have hRJn : normalizer ((RJ : Subgroup J) : Set J) = (RJ : Subgroup J) := by
    change normalizer ((RI : Subgroup I).map b.toMonoidHom : Set J) =
      (RI : Subgroup I).map b.toMonoidHom
    rw [←map_equiv_normalizer_eq,hRIn]
  let Q := RJ.subtype hRJH
  have hQn : normalizer ((Q : Subgroup (H.subgroupOf J)) : Set (H.subgroupOf J)) =
      (Q : Subgroup (H.subgroupOf J)) := by
    change normalizer ((RJ : Subgroup J).subgroupOf (H.subgroupOf J) : Set (H.subgroupOf J)) =
      (RJ : Subgroup J).subgroupOf (H.subgroupOf J)
    rw [←subgroupOf_normalizer_eq hRJH,hRJn]
  let j : H.subgroupOf J ≃* H := subgroupOfEquivOfLe hHJ
  let S := Q.mapSurjective (f := j.toMonoidHom) j.surjective
  have hSn : normalizer (S : Set H) = S := by
    change normalizer ((Q : Subgroup (H.subgroupOf J)).map j.toMonoidHom : Set H) =
      (Q : Subgroup (H.subgroupOf J)).map j.toMonoidHom
    rw [←map_equiv_normalizer_eq,hQn]
  let C := L ⊓ centralizer ({w} : Set G)
  have hC3 : 3 ∣ Nat.card C := by
    let : MulAction L G := MulAction.compHom G
      (ConjAct.toConjAct.toMonoidHom.comp L.subtype)
    have he : C.subgroupOf L = MulAction.stabilizer L w := by
      ext l
      change ((l : G) ∈ L ∧ (l : G) ∈ centralizer ({w} : Set G)) ↔
        (l : G)*w*(l : G)⁻¹ = w
      simp only [l.property,true_and,mem_centralizer_singleton_iff,mul_inv_eq_iff_eq_mul]
    have hi : (C.subgroupOf L).index = 14 := by
      rw [he,MulAction.index_stabilizer]
      exact Selection.BinaryThree.moved_orbit_card_of_positive_kernel D hmodel hne hw hwn
    have hcard := (C.subgroupOf L).index_mul_card
    rw [hi,Nat.card_congr (subgroupOfEquivOfLe (show C ≤ L from inf_le_left)).toEquiv]
      at hcard
    obtain ⟨eL,_⟩ := hmodel
    have hL : Nat.card L = 168 * Nat.card (pCore 2 L) := by
      rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L),Nat.card_congr eL.toEquiv,
        Matrix.PSL3Two.card_SL]
    have hC : Nat.card C = 12 * Nat.card (pCore 2 L) := by omega
    rw [hC]
    exact dvd_mul_of_dvd_left (by decide) _
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hC3
  have hy3 : orderOf (y : G) = 3 := (Subgroup.orderOf_coe y).trans hy
  have hyI : f (y : G) ∈ I := by
    have hyv : f (y : G) ∈ centralizer ({v} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      simpa only [map_mul,hwv] using congrArg f (mem_centralizer_singleton_iff.mp y.property.2)
    rw [←c.component_eq_point_residual_of_binary_actor hd e]
    apply mem_map_of_mem (centralizer ({v} : Set G)).subtype (x := ⟨f (y : G),hyv⟩)
    apply mem_primeToResidual_of_pow (n := 1)
    apply Subtype.ext
    change (f (y : G))^(3^1) = 1
    rw [pow_one,←map_pow,←hy3,pow_orderOf_eq_one,map_one]
  have hyH : (y : G) ∈ H :=
    ⟨⟨f (y : G),hyI,f.symm_apply_apply _⟩,L.le_normalizer y.property.1⟩
  exact no_positive_cover_stabilizer_cubic hmodel hne H hHL hHW S hSn hw hwn
    (hHJ.trans hJfix) hyH y.property.1 hy3

/-- Every original natural cover has zero fixed kernel in the constrained
context. Both binary containing degrees and the A₇ actor are discharged. -/
theorem Context.binaryThreeNatural_fixed_eq_bot (c : Context D t v I)
    (hmodel : Selection.BinaryThreeNatural D) : sourceMovedFixed D = ⊥ := by
  by_contra hne
  obtain ⟨_,_,d,hd,⟨e⟩⟩ := c.binary_source_action_of_binaryThreeNatural hmodel
  exact c.no_positive_binaryThree_of_binary_actor hmodel hne hd e

/-- No original natural binary-three cover survives, including its positive
fixed kernel and without an extra preparation or containing-action premise. -/
theorem Context.no_binaryThreeNatural (c : Context D t v I)
    (hmodel : Selection.BinaryThreeNatural D) : False := by
  have hz := c.binaryThreeNatural_fixed_eq_bot hmodel
  obtain ⟨e,⟨s⟩⟩ := hmodel
  exact c.no_natural_three e (hz ▸ s)

/-- The whole local Thompson-moving branch is impossible on the original
context: both natural-cover families are now excluded. -/
theorem Context.local_thompson_fixed (c : Context D t v I) :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G) := by
  by_contra hJ
  rcases c.natural_of_local_thompson_moves hJ with hr | hb
  · exact c.no_rankOneNatural hr
  · exact c.no_binaryThreeNatural hb

/-- The original full module has no L₀-fixed vectors in the constrained
context. The positive-layer source branch is discharged by local movement. -/
theorem Context.full_fixed_eq_bot (c : Context D t v I) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
  by_contra hfixed
  exact Selection.ModuleChoice.local_thompson_moves_of_full_fixed_ne_bot
    D c.many hfixed c.local_thompson_fixed

/-- Cubic component order now gives Thompson fixedness on the original
full module, without any assumption about the containing module. -/
theorem Context.full_thompson_fixed_of_three (c : Context D t v I)
    (hd : 3 ∣ Nat.card (L ⧸ pCore 2 L)) :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.fullModule : Set G) :=
  Selection.ModuleChoice.full_thompson_centralizes_of_local_three D
    (fun hn => c.escaping.t_not_normalizes (hn c.escaping.t_mem)) hd c.local_thompson_fixed

end CFSG.Quasithin.Chapter10.PointControl.Constrained
