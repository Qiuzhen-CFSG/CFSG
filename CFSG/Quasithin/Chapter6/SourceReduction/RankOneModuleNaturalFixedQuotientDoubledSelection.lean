module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientDoubledExclusion
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ProperDouble
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.NormalType
public import Mathlib.RepresentationTheory.Semisimple

/-!
# Selecting the Sylow-invariant natural copy in the doubled module

The A.1.42 odd-copy theorem selects a copy fixed by the original two-group
inside a doubled simple normal-subgroup action. The complement only needs
to be invariant under the normal subgroup. Both copies retain the original
natural actor marking.

Source: Aschbacher–Smith, A.1.42 and 6.1.4, printed pp.32 and 664–665.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open scoped MonoidAlgebra IsMulCommutative

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem proper_double_copy
    {D X Y : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {τ : Representation (ZMod 2) D X} {σ : Representation (ZMod 2) D Y}
    [σ.IsIrreducible] (e : τ.Equiv (σ.prod σ))
    (U : Subrepresentation τ) (hne : U ≠ ⊥) (hproper : U ≠ ⊤) :
    Nonempty (U.toRepresentation.Equiv σ) := by
  let i : U.toRepresentation.IntertwiningMap (σ.prod σ) :=
    (e.toLinearMap.comp U.toSubmodule.subtype).intertwiningMap_of_isIntertwiningMap _ _
      (by intro g v; exact LinearMap.congr_fun (e.isIntertwining' g) v.val)
  have hi : Function.Injective i := e.injective.comp Subtype.val_injective
  have hn : i ≠ 0 := by
    intro hz
    apply hne
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    have he := hi (show i ⟨v,hv⟩ = i 0 by rw [hz]; rfl)
    exact Subtype.ext_iff.mp he
  have hp : ¬ Function.Surjective i := by
    intro hs
    apply hproper
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    obtain ⟨w,hw⟩ := hs (e v)
    exact e.injective hw ▸ w.property
  exact Representation.equiv_of_injective_map_to_proper_double i hi hn hp

private theorem double_not_irreducible
    {D X Y : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [Nontrivial Y]
    {τ : Representation (ZMod 2) D X} {σ : Representation (ZMod 2) D Y}
    (e : τ.Equiv (σ.prod σ)) : ¬ τ.IsIrreducible := by
  intro hi
  let := hi
  let f := (IntertwiningMap.fst (ZMod 2) σ σ).comp e.toIntertwiningMap
  obtain ⟨y,hy⟩ := exists_ne (0 : Y)
  have hf : f ≠ 0 := by
    intro hz
    have hh := congrArg (fun p : τ.IntertwiningMap σ => p (e.symm (y,0))) hz
    exact hy (by simpa [f] using hh)
  have hfi := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hx : e.symm (0,y) = 0 := hfi (by simp [f])
  have he := congrArg (fun x => (e x).2) hx
  exact hy (by simpa using he)

private theorem double_semisimple
    {D X Y : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y]
    {τ : Representation (ZMod 2) D X} {σ : Representation (ZMod 2) D Y}
    [σ.IsIrreducible] (e : τ.Equiv (σ.prod σ)) : IsSemisimpleRepresentation τ := by
  let p := (IntertwiningMap.fst (ZMod 2) σ σ).comp e.toIntertwiningMap
  let q := (IntertwiningMap.snd (ZMod 2) σ σ).comp e.toIntertwiningMap
  let j : τ.asModule →ₗ[(ZMod 2)[D]] (Fin 2 → σ.asModule) :=
    LinearMap.pi (fun i => if i = 0 then IntertwiningMap.equivLinearMapAsModule _ _ p
      else IntertwiningMap.equivLinearMapAsModule _ _ q)
  have hj : Function.Injective j := by
    intro v w he
    apply e.injective
    apply Prod.ext
    · have hh := congrArg (fun z : Fin 2 → σ.asModule => σ.asModuleEquiv (z 0)) he
      change (e v).1 = (e w).1 at hh
      exact hh
    · have hh := congrArg (fun z : Fin 2 → σ.asModule => σ.asModuleEquiv (z 1)) he
      change (e v).2 = (e w).2 at hh
      exact hh
  exact (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
    (IsSemisimpleModule.of_injective j hj)

private theorem double_fixed_copy_and_complement
    {D X Y : Type*} [Group D] [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [Nontrivial Y]
    (ρ : Representation (ZMod 2) D X) (N : Subgroup D) [N.Normal]
    (σ : Representation (ZMod 2) N Y) [σ.IsIrreducible]
    (e : Representation.Equiv (ρ.comp N.subtype) (σ.prod σ))
    (P : Subgroup D) (hP : IsPGroup 2 P) :
    ∃ U W : Subrepresentation (ρ.comp N.subtype),
      Nonempty (U.toRepresentation.Equiv σ) ∧ Nonempty (W.toRepresentation.Equiv σ) ∧
      U ⊓ W = ⊥ ∧ U ⊔ W = ⊤ ∧
      ∀ p : P, U.toSubmodule.map (ρ p) = U.toSubmodule := by
  let τ : Representation (ZMod 2) N X := ρ.comp N.subtype
  let : IsSemisimpleRepresentation τ := double_semisimple e
  let : IsSemisimpleModule (ZMod 2)[N] τ.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp inferInstance
  let : Nontrivial X := e.symm.injective.nontrivial
  let : Nontrivial τ.asModule := τ.asModuleEquiv.toEquiv.nontrivial
  have hred : ¬ τ.IsIrreducible := double_not_irreducible e
  have hproper (S : Subrepresentation τ) (hs : S.toRepresentation.IsIrreducible) : S ≠ ⊤ := by
    intro ht
    exact hred (isSimpleOrder_iff_isAtom_top.mpr
      (ht ▸ (Subrepresentation.irreducible_iff_isAtom S).mp hs))
  obtain ⟨A,hA⟩ := IsSemisimpleModule.exists_simple_submodule (ZMod 2)[N] τ.asModule
  let S := Subrepresentation.ofSubmodule' A
  have hs : S.toRepresentation.IsIrreducible := by
    rw [Subrepresentation.irreducible_iff_isAtom]
    exact Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff S |>.mp
      (isSimpleModule_iff_isAtom.mp hA)
  have copy (C : Subrepresentation τ) (hc : C.toRepresentation.IsIrreducible) :
      Nonempty (C.toRepresentation.Equiv σ) :=
    proper_double_copy e C ((Subrepresentation.irreducible_iff_isAtom C).mp hc).ne_bot
      (hproper C hc)
  obtain ⟨U,_,hu,hfix⟩ := Homogeneous.fixed_simple_copy ρ N P hP S hs (by
    intro p
    let C := (Homogeneous.normalTypeAction ρ N).conjugate p S
    obtain ⟨s⟩ := copy S hs
    obtain ⟨c⟩ := copy C ((Homogeneous.normalTypeAction ρ N).conjugate_irreducible S hs p)
    let a := s.trans c.symm
    exact (Homogeneous.sameModule_iff_repEquiv S C).mpr ⟨⟨a.toLinearEquiv,a.isIntertwining'⟩⟩)
  obtain ⟨W,hW⟩ := exists_isCompl U
  have hUn := ((Subrepresentation.irreducible_iff_isAtom U).mp hu).ne_bot
  have hWn : W ≠ ⊥ := by
    intro hz
    apply hproper U hu
    simpa only [hz,sup_bot_eq] using hW.sup_eq_top
  have hWp : W ≠ ⊤ := by
    intro ht
    apply hUn
    simpa only [ht,inf_top_eq] using hW.inf_eq_bot
  exact ⟨U,W,copy U hu,proper_double_copy e W hWn hWp,
    hW.inf_eq_bot,hW.sup_eq_top,hfix⟩

private def ambientSubspace {G : Type*} [Group G] (B : Subgroup G)
    [IsElementaryAbelian 2 B] (U : Submodule (ZMod 2) (Additive B)) : Subgroup G :=
  U.toAddSubgroup.toSubgroup'.map B.subtype

private def ambientSubspaceEquiv {G : Type*} [Group G] (B : Subgroup G)
    [IsElementaryAbelian 2 B] (U : Submodule (ZMod 2) (Additive B)) :
    Multiplicative U ≃* ambientSubspace B U := by
  let f : Multiplicative U →* ambientSubspace B U := {
    toFun v := ⟨v.toAdd.val.toMul,⟨v.toAdd.val.toMul,v.toAdd.property,rfl⟩⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  exact MulEquiv.ofBijective f ⟨by
    intro x y he
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun u : ambientSubspace B U => (u : G)) he, by
    intro u
    obtain ⟨b,hb,he⟩ := u.property
    refine ⟨Multiplicative.ofAdd ⟨Additive.ofMul b,hb⟩,?_⟩
    exact Subtype.ext he⟩

private theorem ambientSubspace_sup {G : Type*} [Group G] (B : Subgroup G)
    [IsElementaryAbelian 2 B] (U W : Submodule (ZMod 2) (Additive B))
    (h : U ⊔ W = ⊤) : ambientSubspace B U ⊔ ambientSubspace B W = B := by
  apply le_antisymm (sup_le (map_subtype_le _) (map_subtype_le _))
  intro x hx
  have hv : Additive.ofMul (⟨x,hx⟩ : B) ∈ U ⊔ W := h.symm ▸ Submodule.mem_top
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hv
  have he := congrArg (fun v : Additive B => (v.toMul : G)) hab
  change (a.toMul : G) * (b.toMul : G) = x at he
  rw [←he]
  exact mul_mem (mem_sup_left (show (a.toMul : G) ∈ ambientSubspace B U from ⟨a.toMul,ha,rfl⟩))
    (mem_sup_right (show (b.toMul : G) ∈ ambientSubspace B W from ⟨b.toMul,hb,rfl⟩))

private theorem ambientSubspace_inf {G : Type*} [Group G] (B : Subgroup G)
    [IsElementaryAbelian 2 B] (U W : Submodule (ZMod 2) (Additive B))
    (h : U ⊓ W = ⊥) : ambientSubspace B U ⊓ ambientSubspace B W = ⊥ := by
  apply bot_unique
  rintro x ⟨⟨a,ha,he⟩,⟨b,hb,hf⟩⟩
  have hab : a = b := B.subtype_injective (he.trans hf.symm)
  have hz : Additive.ofMul a ∈ U ⊓ W := ⟨ha,hab.symm ▸ hb⟩
  rw [h] at hz
  have ha1 : a = 1 := congrArg Additive.toMul hz
  exact mem_bot.mpr (he.symm.trans (congrArg (fun v : B => (v : G)) ha1))

open ChapterB.QuasisimpleSource

/-- Two natural copies with the original quotient marking have an actual
Sylow-invariant first summand and an L-invariant natural complement. -/
theorem original_doubled_natural_summands
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (F : BinaryField) (hF : F.degree = n)
    (hmodel : IsConjugationModel L (layer L V) (repeated (linearNatural F 2) 2)) :
    ∃ B₁ B₂ : Subgroup G, IsNaturalModule L B₁ n ∧ IsNaturalModule L B₂ n ∧
      layer L V = B₁ ⊔ B₂ ∧ B₁ ⊓ B₂ = ⊥ ∧
      (T : Subgroup G) ≤ normalizer (B₁ : Set G) := by
  classical
  let B := layer L V
  let := h.layer_elementary
  let H := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf H
  let P := (T : Subgroup G).subgroupOf H
  have hHB : H ≤ normalizer (B : Set G) :=
    sup_le hmodel.normalizes h.sylow_normalizes_layer
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer h.sylow_normalizes_L)
  let a : H →* ChapterE.Automizer B :=
    B.normalizerMonoidHom.rangeRestrict.comp (inclusion hHB)
  let ρ : Representation (ZMod 2) H (Additive B) :=
    (ChapterE.automizerRepresentation B).comp a
  obtain ⟨e,f,hf⟩ := hmodel
  let bN : N ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let q : N →* Matrix.SpecialLinearGroup (Fin 2) F.Carrier :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp bN.toMonoidHom)
  let σ : Representation (ZMod 2) N (Fin 2 → F.Carrier) := (linearNatural F 2).comp q
  have hq : Function.Surjective q := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp bN.surjective)
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff q hq (linearNatural F 2)).mpr
      (ExtensionConsequences.linearNatural_irreducible F (by decide))
  let E₀ : Additive B ≃ₗ[ZMod 2] (Fin 2 → Fin 2 → F.Carrier) :=
    LinearEquiv.ofBijective (f.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) f.bijective
  have hact (l : N) (v : Additive B) :
      E₀ (ρ l v) = repeated (linearNatural F 2) 2 (q l) (E₀ v) := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    change (f.symm (f (B.normalizerMonoidHom ⟨(l : H),hHB l.val.property⟩ v.toMul)) : G) = _
    rw [f.symm_apply_apply]
    exact (hf (bN l) v.toMul).symm
  let E : Representation.Equiv (ρ.comp N.subtype) (σ.prod σ) := .mk
    (E₀.trans (LinearEquiv.finTwoArrow (ZMod 2) (Fin 2 → F.Carrier))) (by
      intro l
      ext v i
      · exact congrFun (congrFun (hact l v) 0) i
      · exact congrFun (congrFun (hact l v) 1) i)
  obtain ⟨U,W,⟨u⟩,⟨w⟩,hinf,hsup,hfix⟩ :=
    double_fixed_copy_and_complement ρ N σ E P T.isPGroup'.comap_subtype
  let B₁ := ambientSubspace B U.toSubmodule
  let B₂ := ambientSubspace B W.toSubmodule
  have natural (S : Subrepresentation (ρ.comp N.subtype))
      (c : S.toRepresentation.Equiv σ) : IsNaturalModule L (ambientSubspace B S.toSubmodule) n := by
    let b := ambientSubspaceEquiv B S.toSubmodule
    let s := b.symm.trans c.toLinearEquiv.toAddEquiv.toMultiplicative
    refine ⟨F.Carrier,inferInstance,inferInstance,inferInstance,
      F.card_eq.trans (congrArg (2 ^ ·) hF),e,s,?_⟩
    intro l v
    let v' := (b.symm v).toAdd
    have hv : (v'.val.toMul : G) = (v : G) :=
      congrArg Subtype.val (b.apply_symm_apply v)
    have hc := LinearMap.congr_fun (c.isIntertwining' (bN.symm l)) v'
    change c (S.toRepresentation (bN.symm l) v') =
      Representation.specialLinearNatural 2
        (e (QuotientGroup.mk' (pCore 2 L) l)) (c v') at hc
    change (b (Multiplicative.ofAdd (c.symm
      (Representation.specialLinearNatural 2
        (e (QuotientGroup.mk' (pCore 2 L) l)) (c v')))) : G) = _
    rw [←hc,c.symm_apply_apply]
    change (l : G) * (v'.val.toMul : G) * (l : G)⁻¹ = _
    rw [hv]
  refine ⟨B₁,B₂,natural U u,natural W w,?_,?_,?_⟩
  · exact (ambientSubspace_sup B U.toSubmodule W.toSubmodule
      (congrArg Subrepresentation.toSubmodule hsup)).symm
  · exact ambientSubspace_inf B U.toSubmodule W.toSubmodule
      (congrArg Subrepresentation.toSubmodule hinf)
  · apply le_normalizer_iff.mpr
    intro t ht x hx
    obtain ⟨v,hv,rfl⟩ := hx
    let p : P := ⟨⟨t,mem_sup_right ht⟩,ht⟩
    have hm : ρ (p : H) (Additive.ofMul v) ∈ U.toSubmodule := by
      rw [←hfix p]
      exact ⟨Additive.ofMul v,hv,rfl⟩
    exact ⟨(ρ (p : H) (Additive.ofMul v)).toMul,hm,rfl⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
