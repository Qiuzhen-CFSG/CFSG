module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Parabolic.FourStarActor
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.MovedNormalizerAction
public import Theory.Representation.SL5ExteriorSquare.MarkedRecognition
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorMoved
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.LargeComponentPlacement
public import Theory.Representation.BinaryNaturalFullAction

/-!
# Selecting the natural-plus-dual moved module in the degree-four star branch

The genuine C.2.7 moved section and the binary B.5 catalogue give the actual
SL5(2) module. The original outer actor excludes the irreducible exterior
square, whose linear normalizer induces only inner automorphisms. It also
excludes a natural or repeated-natural module: a nonzero coordinate block
of an intertwiner reduces that case to the full binary natural action.
The remaining natural-plus-dual module has a fixed supplement by the proved
first-cohomology vanishing. No splitting or compatibility is assumed.

`FourStarFixed` applies this module to the literal line-hyperplane parabolic.
Source: Aschbacher--Smith 12.1.1, B.5.1 and B.2.14, printed pp.788--789.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
open Subgroup Representation Representation.BinaryOffender

private theorem inner_of_self_normalizing_image
    {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) A X) (hf : Function.Injective ρ.asGroupHom)
    (hn : normalizer (ρ.asGroupHom.range : Set (Module.End (ZMod 2) X)ˣ) = ρ.asGroupHom.range)
    (α : MulAut A) (b : X ≃ₗ[ZMod 2] X)
    (hb : ∀ g v, b (ρ g v) = ρ (α g) (b v)) : α ∈ MulAut.innerSubgroup A := by
  let c := LinearMap.GeneralLinearGroup.ofLinearEquiv b
  have hc (g : A) : c * ρ.asGroupHom g * c⁻¹ = ρ.asGroupHom (α g) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change b (ρ g (b.symm v)) = ρ (α g) v
    rw [hb,b.apply_symm_apply]
  have hcn : c ∈ normalizer (ρ.asGroupHom.range : Set (Module.End (ZMod 2) X)ˣ) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    ext x
    constructor
    · rintro ⟨_,⟨g,rfl⟩,rfl⟩
      exact ⟨α g,(hc g).symm⟩
    · rintro ⟨g,rfl⟩
      refine ⟨ρ.asGroupHom (α.symm g),⟨_,rfl⟩,?_⟩
      change c * ρ.asGroupHom (α.symm g) * c⁻¹ = ρ.asGroupHom g
      rw [hc,α.apply_symm_apply]
  rw [hn] at hcn
  obtain ⟨g,hg⟩ := hcn
  refine ⟨g,?_⟩
  apply MulEquiv.ext
  intro x
  apply hf
  rw [MulAut.conj_apply,map_mul,map_mul,map_inv,hg]
  exact hc x

/-- Every linear intertwiner of an irreducible ten-dimensional SL5(2)
module induces an inner component automorphism. -/
private theorem five_ten_intertwiner_inner
    {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) A X) [IsIrreducible ρ]
    (e : A ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hd : Module.finrank (ZMod 2) X = 10)
    (α : MulAut A) (b : X ≃ₗ[ZMod 2] X)
    (hb : ∀ g v, b (ρ g v) = ρ (α g) (b v)) : α ∈ MulAut.innerSubgroup A := by
  obtain ⟨a,f,_,hf⟩ := Representation.SL5ExteriorSquare.square_coordinates_of_finrank_ten ρ e hd
  let β := MulAut.congr a α
  let c := f.symm.trans (b.trans f)
  have hc (g : Representation.SL5TenDimensional.Group) (v) :
      c (Representation.SL5TenDimensional.exteriorAction 2 g v) =
        Representation.SL5TenDimensional.exteriorAction 2 (β g) (c v) := by
    obtain ⟨x,rfl⟩ := a.surjective g
    obtain ⟨w,rfl⟩ := f.surjective v
    change f (b (f.symm (Representation.SL5TenDimensional.exteriorAction 2 (a x) (f w)))) = _
    rw [←hf,f.symm_apply_apply,hb,hf]
    change Representation.SL5TenDimensional.exteriorAction 2 (a (α x)) (f (b w)) =
      Representation.SL5TenDimensional.exteriorAction 2 (a (α (a.symm (a x))))
        (f (b (f.symm (f w))))
    rw [a.symm_apply_apply,f.symm_apply_apply]
  have hin := inner_of_self_normalizing_image
    (Representation.SL5TenDimensional.exteriorAction 2)
    (Representation.SL5TenDimensional.ExteriorNormalizer.exteriorAction_injective 0)
    Representation.SL5TenDimensional.ExteriorNormalizer.normalizer_two β c hc
  obtain ⟨g,hg⟩ := hin
  refine ⟨a.symm g,?_⟩
  apply (MulAut.congr a).injective
  rw [MulAut.congr_conj,a.apply_symm_apply]
  exact hg
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original outer actor excludes the exterior moved module, including
any central attachment in the source section. -/
private theorem doubleNatural_four_adapted_C27_not_exterior
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        let J := offenderSubgroup (starRepresentation K Q)
        ∀ (_hCJ : starImage K Q K ≤ J)
          (s : MovedSection ((starRepresentation K Q).comp J.subtype)
            ((starImage K Q K).subgroupOf J))
          (_e : ((starImage K Q K).subgroupOf J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)),
          IsIrreducible (s.space.toRepresentation.comp ((starImage K Q K).subgroupOf J).subtype) →
          Module.finrank (ZMod 2) s.space.toSubmodule = 10 → False := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hKn hRK hi J hCJ s e hir hd
  let C := (starImage K Q K).subgroupOf J
  let j := subgroupOfEquivOfLe hCJ
  let eL := (j.symm.trans e).trans (BinaryLinear.OuterCyclic.slEquivLinear 5)
  obtain ⟨a,hK,hQ,_,ha⟩ := D.doubleNatural_four_adapted_C27_outer_actor h B S w hw K hKn hRK hi eL
  let β : MulAut C := j.trans ((starComponentAut K Q a hK hQ).trans j.symm)
  let b := starVectorAut K Q a hK hQ
  have hb (l : C) (v : Additive (starV K Q)) :
      b (((starRepresentation K Q).comp J.subtype) l v) =
        ((starRepresentation K Q).comp J.subtype) (β l) (b v) := by
    have hh := starNormalizerAut_intertwines K Q a hK hQ l.val.val v
    have he := starComponentAut_coe K Q a hK hQ (j l)
    change (starComponentAut K Q a hK hQ (j l) : StarQuotient K Q) =
      starNormalizerAut K Q a hK hQ l.val.val at he
    change b (starRepresentation K Q l.val.val v) =
      starRepresentation K Q (starComponentAut K Q a hK hQ (j l)) (b v)
    rw [he]
    exact hh
  let c := s.twistedSpaceEquiv β b hb
  let σ := s.space.toRepresentation.comp C.subtype
  let : IsIrreducible σ := hir
  have hin := Nonsingular.five_ten_intertwiner_inner σ e hd β c
    (s.twistedSpaceEquiv_intertwines β b hb)
  obtain ⟨g,hg⟩ := hin
  apply ha
  refine ⟨j g,?_⟩
  apply MulEquiv.ext
  intro x
  have hh := congrArg (fun f : MulAut C => j (f (j.symm x))) hg
  change j (g * j.symm x * g⁻¹) = j (j.symm
    (starComponentAut K Q a hK hQ (j (j.symm x)))) at hh
  simpa only [MulAut.conj_apply,map_mul,map_inv,j.apply_symm_apply] using hh

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem natural_fixed_supplement
    {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) A X) {C : Subgroup A}
    (s : MovedSection ρ C) (hC : C = ⊤)
    (hn : IsLinearNatural (s.space.toRepresentation.comp C.subtype) BinaryField.two 5) :
    s.space.toSubmodule ⊔ ρ.invariants = ⊤ := by
  subst C
  let := H1_linearNatural_subsingleton (by decide : 4 ≤ 5)
  let := hn.some.ofTop.H1_subsingleton
  exact s.fixed_supplement_of_H1_subsingleton ρ

/-- The actual degree-four star module has a fixed supplement and only
natural, natural-plus-dual or repeated-natural moved action. -/
private theorem doubleNatural_four_adapted_C27_natural_moved
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        let J := offenderSubgroup (starRepresentation K Q)
        ∃ s : MovedSection ((starRepresentation K Q).comp J.subtype)
            ((starImage K Q K).subgroupOf J),
          s.space.toSubmodule ⊔ Representation.invariants ((starRepresentation K Q).comp J.subtype) = ⊤ ∧
          (IsLinearNatural (s.space.toRepresentation.comp
              ((starImage K Q K).subgroupOf J).subtype) BinaryField.two 5 ∨
            IsNaturalPlusDual (s.space.toRepresentation.comp
              ((starImage K Q K).subgroupOf J).subtype) 5 ∨
            ∃ r, 0 < r ∧ r ≤ 4 ∧ IsRepeatedLinearNatural
              (s.space.toRepresentation.comp ((starImage K Q K).subgroupOf J).subtype)
                BinaryField.two 5 r) := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hKn hRK hi J
  let : (K.subgroupOf (B.pointCentralizer w)).Normal := hKn
  obtain ⟨hCJ,⟨c⟩⟩ := star_moved_section_conclusion hi
  obtain ⟨e₀⟩ := D.doubleNatural_four_adapted_C27_star_linearFive h B S w hw K hKn hRK hi
  let e := (subgroupOfEquivOfLe hCJ).trans e₀
  have hlarge : 40320 < Nat.card (starImage K Q K) := by
    rw [Nat.card_congr e₀.toEquiv]
    rw [Nat.card_congr (BinaryLinear.OuterCyclic.slEquivLinear 5).toEquiv,
      ←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear 5).toEquiv,
      Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hJC : J = starImage K Q K := star_offender_subgroup_eq_component_of_large_order hi hlarge
  have hCtop : (starImage K Q K).subgroupOf J = ⊤ := subgroupOf_eq_top.mpr hJC.le
  have hm := BinaryActor.movedCase (Or.inr rfl)
    (BinaryActor.actionCase _ (Or.inr rfl) e c.clause_one)
  cases hm with
  | natural a =>
    exact ⟨c.sectionData,natural_fixed_supplement _ c.sectionData hCtop ⟨a⟩,Or.inl ⟨a⟩⟩
  | naturalDual hn =>
    exact ⟨c.sectionData,c.sectionData.fixed_supplement_of_naturalDual _
      (by decide : 4 ≤ 5) hCtop hn,Or.inr (Or.inl hn)⟩
  | repeatedNatural r hp hb hn =>
    have hc := ExtensionConsequences.repeated_binary_isCompl c.sectionData
      (by decide : 4 ≤ 5) hCtop hn
    exact ⟨c.sectionData,codisjoint_iff.mp hc.codisjoint,Or.inr (Or.inr ⟨r,hp,hb,hn⟩)⟩
  | orthogonal hd _ _ _ => omega
  | exterior _ mark hir hd =>
    exact (D.doubleNatural_four_adapted_C27_not_exterior h B S w hw K hKn hRK hi
      hCJ c.sectionData mark hir hd).elim
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular
open Subgroup Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open scoped MatrixGroups

set_option backward.isDefEq.respectTransparency false in
private theorem natural_intertwiner_inner
    (α : MulAut SL(5,ZMod 2))
    (b : (Fin 5 → ZMod 2) ≃ₗ[ZMod 2] (Fin 5 → ZMod 2))
    (hb : ∀ g v, b (linearNatural BinaryField.two 5 g v) =
      linearNatural BinaryField.two 5 (α g) (b v)) :
    α ∈ MulAut.innerSubgroup SL(5,ZMod 2) := by
  obtain ⟨g,hg⟩ := specialLinearNatural_binary_full 5 b.toAddEquiv.toMultiplicative
  have hb' (v) : b v = linearNatural BinaryField.two 5 g v :=
    (hg (Multiplicative.ofAdd v)).symm
  refine ⟨g,?_⟩
  apply MulEquiv.ext
  intro x
  apply specialLinearNatural_injective 5
  apply LinearMap.ext
  intro v
  have hh := hb x (linearNatural BinaryField.two 5 g⁻¹ v)
  rw [hb',hb'] at hh
  change linearNatural BinaryField.two 5 (g*x*g⁻¹) v =
    linearNatural BinaryField.two 5 (α x) v
  simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
    Module.End.one_apply,mul_assoc] using hh

set_option backward.isDefEq.respectTransparency false in
private theorem repeated_intertwiner_inner {r : ℕ} (hr : 0 < r)
    (α : MulAut SL(5,ZMod 2))
    (b : (Fin r → Fin 5 → ZMod 2) ≃ₗ[ZMod 2] (Fin r → Fin 5 → ZMod 2))
    (hb : ∀ g v, b (repeated (linearNatural BinaryField.two 5) r g v) =
      repeated (linearNatural BinaryField.two 5) r (α g) (b v)) :
    α ∈ MulAut.innerSubgroup SL(5,ZMod 2) := by
  classical
  let σ := linearNatural BinaryField.two 5
  let k : Fin r := ⟨0,hr⟩
  let j : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin r → Fin 5 → ZMod 2) := LinearMap.single (ZMod 2) (fun _ : Fin r => Fin 5 → ZMod 2) k
  have hj (g : SL(5,ZMod 2)) (v) : repeated σ r g (j v) = j (σ g v) := by
    funext i
    by_cases hi : i = k
    · subst i
      simp [j,repeated]
    · simp [j,repeated,Pi.single_eq_of_ne hi]
  let f (i : Fin r) : σ.IntertwiningMap (σ.comp α.toMonoidHom) := {
    toLinearMap := (LinearMap.proj i).comp (b.toLinearMap.comp j)
    isIntertwining' := fun g => by
      apply LinearMap.ext
      intro v
      change b (j (σ g v)) i = σ (α g) (b (j v) i)
      rw [←hj]
      exact congrFun (hb g (j v)) i }
  have hf : ∃ i, f i ≠ 0 := by
    by_contra! hn
    have hzero (v : Fin 5 → ZMod 2) : b (j v) = 0 := by
      funext i
      exact congrArg (fun t : σ.IntertwiningMap (σ.comp α.toMonoidHom) => t v) (hn i)
    have he : j (Pi.single 0 (1 : ZMod 2)) = 0 := b.map_eq_zero_iff.mp (hzero _)
    have hh := congrArg (fun v : Fin r → Fin 5 → ZMod 2 => v k 0) he
    simp [j] at hh
  obtain ⟨i,hi⟩ := hf
  let : IsIrreducible σ := ExtensionConsequences.linearNatural_irreducible BinaryField.two (by decide)
  have hfi := (IsIrreducible.injective_or_eq_zero (f i)).resolve_right hi
  have hfb : Function.Bijective (f i).toLinearMap :=
    ⟨hfi,LinearMap.surjective_of_injective hfi⟩
  let c := LinearEquiv.ofBijective (f i).toLinearMap hfb
  exact natural_intertwiner_inner α c (fun g v => LinearMap.congr_fun ((f i).isIntertwining' g) v)

set_option backward.isDefEq.respectTransparency false in
/-- In a natural or homogeneous repeated-natural binary five-space, a
linear normalizer induces only inner automorphisms of the component. -/
private theorem five_natural_intertwiner_inner
    {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) A X)
    (hn : IsLinearNatural ρ BinaryField.two 5 ∨
      ∃ r, 0 < r ∧ IsRepeatedLinearNatural ρ BinaryField.two 5 r)
    (α : MulAut A) (b : X ≃ₗ[ZMod 2] X)
    (hb : ∀ g v, b (ρ g v) = ρ (α g) (b v)) : α ∈ MulAut.innerSubgroup A := by
  have transport {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y]
      (σ : Representation (ZMod 2) SL(5,ZMod 2) Y)
      (e : ActionEquiv ρ σ)
      (h : ∀ (β : MulAut SL(5,ZMod 2)) (c : Y ≃ₗ[ZMod 2] Y),
        (∀ g v, c (σ g v) = σ (β g) (c v)) → β ∈ MulAut.innerSubgroup SL(5,ZMod 2)) :
      α ∈ MulAut.innerSubgroup A := by
    let β := e.groupEquiv.symm.trans (α.trans e.groupEquiv)
    let c := e.linearEquiv.symm.trans (b.trans e.linearEquiv)
    have hh := h β c (e.conjugate_intertwiner α b hb)
    obtain ⟨g,hg⟩ := hh
    refine ⟨e.groupEquiv.symm g,?_⟩
    apply (MulAut.congr e.groupEquiv).injective
    rw [MulAut.congr_conj,e.groupEquiv.apply_symm_apply]
    exact hg
  rcases hn with hn | ⟨r,hr,hn⟩
  · obtain ⟨e⟩ := hn
    exact transport (linearNatural BinaryField.two 5) e natural_intertwiner_inner
  · obtain ⟨e⟩ := hn
    exact transport (repeated (linearNatural BinaryField.two 5) r) e (repeated_intertwiner_inner hr)
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Nonsingular

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource ChapterC.C27Source Chapter1
open RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The source outer action selects the actual natural-plus-dual moved module,
and cohomology supplies its fixed supplement. -/
theorem doubleNatural_four_adapted_C27_naturalDual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ (S : B.SourceModel) w, B.AdaptedPoint S w →
      let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
      ∀ K : Subgroup G, (K.subgroupOf (B.pointCentralizer w)).Normal →
        B.pointResidual w ≤ K →
        Input KnownSimple.IsKnownSimple (B.pointCentralizer w) Q (B.localPointCentralizer w) K →
        let J := offenderSubgroup (starRepresentation K Q)
        ∃ s : MovedSection ((starRepresentation K Q).comp J.subtype)
            ((starImage K Q K).subgroupOf J),
          s.space.toSubmodule ⊔ Representation.invariants
            ((starRepresentation K Q).comp J.subtype) = ⊤ ∧
          IsNaturalPlusDual (s.space.toRepresentation.comp
            ((starImage K Q K).subgroupOf J).subtype) 5 := by
  let := D.doubledOrbit_elementary h
  intro S w hw Q K hKn hRK hi J
  obtain ⟨s,hs,hm⟩ := D.doubleNatural_four_adapted_C27_natural_moved h B S w hw K hKn hRK hi
  have hnot (hn : IsLinearNatural (s.space.toRepresentation.comp
        ((starImage K Q K).subgroupOf J).subtype) BinaryField.two 5 ∨
      ∃ r, 0 < r ∧ IsRepeatedLinearNatural (s.space.toRepresentation.comp
        ((starImage K Q K).subgroupOf J).subtype) BinaryField.two 5 r) : False := by
    let : (K.subgroupOf (B.pointCentralizer w)).Normal := hKn
    have hCJ := (star_offender_fitting hi).1
    let C := (starImage K Q K).subgroupOf J
    let j := subgroupOfEquivOfLe hCJ
    obtain ⟨e₀⟩ := D.doubleNatural_four_adapted_C27_star_linearFive h B S w hw K hKn hRK hi
    let eL := e₀.trans (BinaryLinear.OuterCyclic.slEquivLinear 5)
    obtain ⟨a,hK,hQ,_,ha⟩ := D.doubleNatural_four_adapted_C27_outer_actor h B S w hw K hKn hRK hi eL
    let β : MulAut C := j.trans ((starComponentAut K Q a hK hQ).trans j.symm)
    let b := starVectorAut K Q a hK hQ
    have hb (l : C) (v : Additive (starV K Q)) :
        b (((starRepresentation K Q).comp J.subtype) l v) =
          ((starRepresentation K Q).comp J.subtype) (β l) (b v) := by
      have hh := starNormalizerAut_intertwines K Q a hK hQ l.val.val v
      have he := starComponentAut_coe K Q a hK hQ (j l)
      change (starComponentAut K Q a hK hQ (j l) : StarQuotient K Q) =
        starNormalizerAut K Q a hK hQ l.val.val at he
      change b (starRepresentation K Q l.val.val v) =
        starRepresentation K Q (starComponentAut K Q a hK hQ (j l)) (b v)
      rw [he]
      exact hh
    let c := s.twistedSpaceEquiv β b hb
    have hin := Nonsingular.five_natural_intertwiner_inner
      (s.space.toRepresentation.comp C.subtype) hn β c
      (s.twistedSpaceEquiv_intertwines β b hb)
    obtain ⟨g,hg⟩ := hin
    apply ha
    refine ⟨j g,?_⟩
    apply MulEquiv.ext
    intro x
    have hh := congrArg (fun f : MulAut C => j (f (j.symm x))) hg
    change j (g * j.symm x * g⁻¹) = j (j.symm
      (starComponentAut K Q a hK hQ (j (j.symm x)))) at hh
    simpa only [MulAut.conj_apply,map_mul,map_inv,j.apply_symm_apply] using hh
  rcases hm with hn | hn | ⟨r,hp,_,hn⟩
  · exact (hnot (Or.inl hn)).elim
  · exact ⟨s,hs,hn⟩
  · exact (hnot (Or.inr ⟨r,hp,hn⟩)).elim
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
