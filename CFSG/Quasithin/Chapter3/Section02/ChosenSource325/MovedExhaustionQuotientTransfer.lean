module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizer
public import Theory.Representation.CubicClifford.Extension
public import Theory.Representation.BinaryOffender.PermutedSupports
public import Mathlib.LinearAlgebra.Projection

/-!
# Transferring a quotient offender to the exchanged local pair

Two nonisomorphic simple component summands exchanged by the ambient actor
make their sum irreducible. If the component quotient of the actor is a
two-group, its action on the nonzero space of component intertwiners fixes
a nonzero map. Schur's lemma makes that map injective. Thus a repeated
component summand in another module embeds the entire local pair there.

The original unchanged-component marking also descends to its actual image
on the same elementary group. The Chapter12 application constructs this
repeated copy in U/W from the escaping normalizer conjugate and transfers
the specified quotient offender back to W. No inner-action or quotient
faithfulness assumption is used in constructing the embedding.

Source: Aschbacher--Smith D.3.9(1), printed pp.199--200, used by D.3.13
and 3.2.5, pp.202 and580; refs/quasithin.pdf. The binary multiplicity and
centralizer exclusions and final Source325 assembly remain with qt-baumann-fsu.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H E F : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

/-- A nonzero component intertwiner extends to a nonzero ambient intertwiner
across a two-group quotient in characteristic two. -/
private theorem nonzero_intertwiner_of_two_quotient
    [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) F]
    (K : Subgroup H) [K.Normal] (hQ : IsPGroup 2 (H ⧸ K))
    (τ : Representation (ZMod 2) H E) (ρ : Representation (ZMod 2) H F)
    (f : Representation.IntertwiningMap (τ.comp K.subtype) (ρ.comp K.subtype)) (hf : f ≠ 0) :
    ∃ i : τ.IntertwiningMap ρ, i ≠ 0 := by
  let D := CubicClifford.homSpace K τ ρ
  have hfm : f.toLinearMap ∈ D := by
    intro k
    ext x
    change ρ k (f.toLinearMap (τ (k : H)⁻¹ x)) = f.toLinearMap x
    have he := LinearMap.congr_fun (f.isIntertwining' k) (τ (k : H)⁻¹ x)
    simpa only [MonoidHom.comp_apply,LinearMap.comp_apply,Subgroup.subtype_apply,Subgroup.coe_inv,← Module.End.mul_apply,
      ← map_mul,mul_inv_cancel,map_one,Module.End.one_apply] using he.symm
  have hn : (⊤ : Submodule (ZMod 2) D) ≠ ⊥ := by
    intro hz
    have he : (⟨f.toLinearMap,hfm⟩ : D) = 0 := (show (⟨f.toLinearMap,hfm⟩ : D) ∈ (⊥ : Submodule (ZMod 2) D) from hz ▸ Submodule.mem_top)
    exact hf (IntertwiningMap.toLinearMap_injective _ _ (congrArg Subtype.val he))
  let η := CubicClifford.homQuotientRepresentation K τ ρ
  obtain ⟨u,_,hu,hfix⟩ := PermutedSupports.exists_nonzero_fixed η ⊤
    (hQ.to_subgroup ⊤) ⊤ hn (by intro g hg v; simp)
  let i : τ.IntertwiningMap ρ := ⟨u.val,fun h => by
    ext x
    have he := congrArg Subtype.val (hfix ⟨QuotientGroup.mk' K h,mem_top _⟩)
    have hh := LinearMap.congr_fun he (τ h x)
    change ρ h (u.val (τ h⁻¹ (τ h x))) = u.val (τ h x) at hh
    simpa only [LinearMap.comp_apply,← Module.End.mul_apply,← map_mul,
      inv_mul_cancel,map_one,Module.End.one_apply] using hh.symm⟩
  exact ⟨i,fun hz => hu (Subtype.ext (congrArg IntertwiningMap.toLinearMap hz))⟩

/-- Projection onto an invariant direct summand, with the original actor. -/
private def pairProjection (τ : Representation (ZMod 2) H E)
    (I J : Subrepresentation τ) (hc : IsCompl I.toSubmodule J.toSubmodule) :
    τ.IntertwiningMap I.toRepresentation :=
  (I.toSubmodule.projectionOnto J.toSubmodule hc).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g v
    obtain ⟨⟨x,y⟩,rfl⟩ := (I.toSubmodule.prodEquivOfIsCompl J.toSubmodule hc).surjective v
    change I.toSubmodule.projectionOnto J.toSubmodule hc (τ g (x.val+y.val)) = _
    rw [map_add,map_add,Submodule.projectionOnto_apply_of_mem_left hc (I.apply_mem_toSubmodule g x.property),
      Submodule.projectionOnto_apply_of_mem_right hc (J.apply_mem_toSubmodule g y.property),add_zero]
    change _ = I.toRepresentation g (I.toSubmodule.projectionOnto J.toSubmodule hc (x.val+y.val))
    rw [map_add,Submodule.projectionOnto_apply_left,Submodule.projectionOnto_apply_right,add_zero]
    rfl)

private theorem pairProjection_apply_left (τ : Representation (ZMod 2) H E)
    (I J : Subrepresentation τ) (hc : IsCompl I.toSubmodule J.toSubmodule) (v : I.toSubmodule) :
    pairProjection τ I J hc v.val = v := Submodule.projectionOnto_apply_left hc v

/-- Distinct simple summands exchanged by an ambient element give an
irreducible ambient action. -/
theorem irreducible_of_exchanged_pair (ρ : Representation (ZMod 2) H E)
    (K : Subgroup H) (I J : Subrepresentation (ρ.comp K.subtype))
    (hi : IsIrreducible I.toRepresentation) (hj : IsIrreducible J.toRepresentation)
    (hne : ¬ Nonempty (I.toRepresentation.Equiv J.toRepresentation))
    (hspan : I.toSubmodule ⊔ J.toSubmodule = ⊤)
    (t : H) (ht : I.toSubmodule.map (ρ t) = J.toSubmodule) :
    IsIrreducible ρ := by
  let := hi
  let := hj
  let : Nontrivial I.toSubmodule := Subrepresentation.irreducible_module_nontrivial I.toRepresentation
  let : Nontrivial E := I.toSubmodule.subtype_injective.nontrivial
  have hd : Disjoint I.toSubmodule J.toSubmodule := by
    have hh := ((Subrepresentation.irreducible_iff_isAtom I).mp hi).disjoint_of_ne
      ((Subrepresentation.irreducible_iff_isAtom J).mp hj) (fun he => hne ⟨he ▸ Representation.Equiv.refl _⟩)
    exact disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hh.eq_bot)
  have hc : IsCompl I.toSubmodule J.toSubmodule := ⟨hd, codisjoint_iff.mpr hspan⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro C hC
  let Ck : Subrepresentation (ρ.comp K.subtype) :=
    ⟨C.toSubmodule,fun k v hv => C.apply_mem_toSubmodule k hv⟩
  have hor : I ≤ Ck ∨ J ≤ Ck := by
    by_contra! hh
    have hCI : Disjoint C.toSubmodule I.toSubmodule := by
      have hh' : I ⊓ Ck = ⊥ := ((Subrepresentation.irreducible_iff_isAtom I).mp hi).2 _
        (lt_of_le_of_ne inf_le_left (fun he => hh.1 (he.symm.le.trans inf_le_right)))
      exact (disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hh')).symm
    have hCJ : Disjoint C.toSubmodule J.toSubmodule := by
      have hh' : J ⊓ Ck = ⊥ := ((Subrepresentation.irreducible_iff_isAtom J).mp hj).2 _
        (lt_of_le_of_ne inf_le_left (fun he => hh.2 (he.symm.le.trans inf_le_right)))
      exact (disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hh')).symm
    let p := pairProjection (ρ.comp K.subtype) I J hc
    let q := pairProjection (ρ.comp K.subtype) J I hc.symm
    let c : Ck.toRepresentation.IntertwiningMap (ρ.comp K.subtype) :=
      C.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)
    have hinj (A B : Subrepresentation (ρ.comp K.subtype))
        (hAB : IsCompl A.toSubmodule B.toSubmodule) (hCB : Disjoint C.toSubmodule B.toSubmodule) :
        Function.Injective ((pairProjection (ρ.comp K.subtype) A B hAB).comp c) := by
      apply (injective_iff_map_eq_zero _).mpr
      intro v hv
      apply Subtype.ext
      exact (Submodule.disjoint_def.mp hCB) v.val v.property
        ((Submodule.projectionOnto_apply_eq_zero_iff hAB).mp hv)
    let : Nontrivial C.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
      (fun he => hC (Subrepresentation.toSubmodule_injective he))
    have hp : p.comp c ≠ 0 := fun hz =>
      not_subsingleton C.toSubmodule ⟨fun x y => hinj I J hc hCJ (by rw [hz]; rfl)⟩
    have hq : q.comp c ≠ 0 := fun hz =>
      not_subsingleton C.toSubmodule ⟨fun x y => hinj J I hc.symm hCI (by rw [hz]; rfl)⟩
    let ep := (p.comp c).ofBijective ⟨hinj I J hc hCJ,
      (IsIrreducible.surjective_or_eq_zero _).resolve_right hp⟩
    let eq := (q.comp c).ofBijective ⟨hinj J I hc.symm hCI,
      (IsIrreducible.surjective_or_eq_zero _).resolve_right hq⟩
    exact hne ⟨ep.symm.trans eq⟩
  have hIC : I.toSubmodule ≤ C.toSubmodule := by
    rcases hor with hiC | hjC
    · exact hiC
    · intro v hv
      have he := C.apply_mem_toSubmodule t⁻¹ (hjC (ht ▸ Submodule.mem_map_of_mem (f := ρ t) hv))
      simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using he
  have hJC : J.toSubmodule ≤ C.toSubmodule := by
    rw [←ht]
    rintro _ ⟨v,hv,rfl⟩
    exact C.apply_mem_toSubmodule t (hIC hv)
  apply Subrepresentation.toSubmodule_injective
  exact top_unique (hspan ▸ sup_le hIC hJC)

/-- A simple extending module embeds whenever a component summand has a
nonzero map into the target. The component projection supplies the Hom-space. -/
theorem embedding_of_two_quotient_of_summand
    [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) F]
    (K : Subgroup H) [K.Normal] (hQ : IsPGroup 2 (H ⧸ K))
    (τ : Representation (ZMod 2) H E) (ρ : Representation (ZMod 2) H F)
    [IsIrreducible τ] (I J : Subrepresentation (τ.comp K.subtype))
    (hc : IsCompl I.toSubmodule J.toSubmodule) [Nontrivial I.toSubmodule]
    (f : I.toRepresentation.IntertwiningMap (ρ.comp K.subtype)) (hf : Function.Injective f) :
    ∃ i : τ.IntertwiningMap ρ, Function.Injective i := by
  let p := pairProjection (τ.comp K.subtype) I J hc
  have hn : f.comp p ≠ 0 := by
    intro hz
    have heq : f = 0 := by
      apply IntertwiningMap.ext
      apply LinearMap.ext
      intro v
      have hv := congrArg (fun q : Representation.IntertwiningMap (τ.comp K.subtype)
        (ρ.comp K.subtype) => q v.val) hz
      change f (p v.val) = 0 at hv
      rw [pairProjection_apply_left] at hv
      exact hv
    exact not_subsingleton I.toSubmodule ⟨fun x y => hf (by rw [heq]; rfl)⟩
  obtain ⟨i,hi⟩ := nonzero_intertwiner_of_two_quotient K hQ τ ρ (f.comp p) hn
  exact ⟨i,(IsIrreducible.injective_or_eq_zero i).resolve_right hi⟩

section InternalCopies
variable {G : Type*} [Group G] {M L U V V' : Subgroup G}
  [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 V']

/-- The original unchanged-component marking descends to its faithful image
on the same ambient elementary group. -/
theorem same_internalImageSubrepresentation (hn : M ≤ normalizer (U : Set G))
    (hVU : V ≤ U) (hV'U : V' ≤ U)
    (hLV : L ≤ normalizer (V : Set G)) (hLV' : L ≤ normalizer (V' : Set G))
    (hs : SameConjugationModule L V V') :
    SameModule (σ := (ChapterD.UniqueFactor.imageRepresentation M U hn).comp
      ((L.subgroupOf M).map (internalHom M U hn)).subtype)
      (internalImageSubrepresentation hn hLV) (internalImageSubrepresentation hn hLV') := by
  obtain ⟨e,he⟩ := same_internalSubrepresentation hn hVU hV'U hLV hLV' hs
  refine ⟨e,?_⟩
  intro k v
  obtain ⟨l,rfl⟩ := (internalHom M U hn).subgroupMap_surjective (L.subgroupOf M) k
  exact he l v
end InternalCopies

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
