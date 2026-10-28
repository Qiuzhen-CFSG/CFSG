module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionIsotypic
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderFaithful
public import Theory.Representation.BinaryOffender.PermutedSupports

/-!
# Component centralizers in the full chosen-seed action

A two-group commuting with an irreducible constituent fixes it pointwise:
a nonzero fixed vector exists, and its fixed space is component invariant.
Commuting with an action image also preserves the entire isotypic component,
even if the original component action has a kernel. Normality propagates
pointwise fixation from a seed to its Sylow orbit.

The internal constructions retain the literal image of L on the larger
normalizer orbit U. Its quasisimplicity follows from the original L/O₂(L)
and trivial O₂ of the full faithful image; no central quotient is substituted
for an SL₃ central cover. The actual application is
`SeedAlternativesMovedExhaustionCentralizer`, identifying the kernels on V
and W with the component centralizer in preparation for D.3.19.
The centralizer exclusions and source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith, D.3.13--19, printed pp.202--204.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) H W)

/-- A two-group commuting with an irreducible constituent fixes it pointwise. -/
theorem centralizing_twoGroup_fixes_irreducible
    (K B : Subgroup H) (S : Subrepresentation (ρ.comp K.subtype))
    (hi : IsIrreducible S.toRepresentation) (hB : IsPGroup 2 B)
    (hc : B ≤ centralizer (K : Set H))
    (hs : B ≤ subspaceStabilizer ρ S.toSubmodule) :
    S.toSubmodule ≤ fixedSpace ρ B := by
  let F : Subrepresentation (ρ.comp K.subtype) := {
    toSubmodule := S.toSubmodule ⊓ fixedSpace ρ B
    apply_mem_toSubmodule := by
      rintro k v ⟨hv,hfix⟩
      refine ⟨S.apply_mem_toSubmodule k hv,?_⟩
      intro b
      change ρ b.val (ρ k.val v) = ρ k.val v
      rw [←Module.End.mul_apply,←map_mul,←hc b.property k.val k.property,
        map_mul,Module.End.mul_apply]
      exact congrArg (ρ k.val) (hfix b) }
  have hSn : S.toSubmodule ≠ ⊥ := by
    intro he
    exact ((Subrepresentation.irreducible_iff_isAtom S).mp hi).1
      (Subrepresentation.toSubmodule_injective he)
  obtain ⟨v,hv,hv0,hfix⟩ := PermutedSupports.exists_nonzero_fixed ρ B hB
    S.toSubmodule hSn hs
  have hFn : F ≠ ⊥ := by
    intro he
    have hh : v ∈ F := ⟨hv,hfix⟩
    rw [he] at hh
    exact hv0 hh
  have he : F = S := by
    by_contra hn
    exact hFn (((Subrepresentation.irreducible_iff_isAtom S).mp hi).2 F
      (lt_of_le_of_ne (fun _ h => h.1) hn))
  intro v hv
  have hh : v ∈ F := he.symm ▸ hv
  exact hh.2

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open Representation.BinaryOffender.Homogeneous
variable {H P W : Type*} [Group H] [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W)

/-- Commuting with the image of N preserves its entire simple type, even
when the original action of N has a kernel. -/
theorem typePart_map_eq_of_image_centralizer
    (f : P →* H) (N : Subgroup P) [N.Normal]
    (S : Subrepresentation ((ρ.comp f).comp N.subtype))
    (a : P) (hc : f a ∈ centralizer (N.map f : Set H)) :
    (typePart S).toSubmodule.map (ρ (f a)) = (typePart S).toSubmodule := by
  let c := normalTypeAction (ρ.comp f) N
  let R := c.conjugate a S
  have hm : S.toSubmodule.map (ρ (f a)) = R.toSubmodule :=
    (conjugateSubrepresentationOrderIso_toSubmodule (ρ.comp f) N a S).symm
  let e : S.toSubmodule ≃ₗ[ZMod 2] R.toSubmodule :=
    (S.toSubmodule.equivMapOfInjective (ρ (f a)) (apply_bijective ρ (f a)).injective).trans
      (LinearEquiv.ofEq _ _ hm)
  have he : SameModule S R := by
    refine ⟨e,?_⟩
    intro n v
    apply Subtype.ext
    change ρ (f a) (ρ (f n.val) v.val) = ρ (f n.val) (ρ (f a) v.val)
    rw [←Module.End.mul_apply,←map_mul ρ,←Module.End.mul_apply,←map_mul ρ,
      hc (f n.val) (mem_map_of_mem f n.property)]
  have hh : c.conjugate a (typePart S) = typePart S := by
    rw [conjugate_typePart]
    exact (typePart_eq_of_same he).symm
  exact (conjugateSubrepresentationOrderIso_toSubmodule (ρ.comp f) N a (typePart S)).symm.trans
    (congrArg Subrepresentation.toSubmodule hh)

/-- Normality of C inside the full actor propagates fixed vectors from a
seed to its S-orbit, using the same subgroup S intersect C throughout. -/
theorem orbitSpan_fixed_of_normal_intersection
    (S C : Subgroup H) [C.Normal] (I : Submodule (ZMod 2) W)
    (hf : I ≤ fixedSpace ρ (S ⊓ C)) :
    orbitSpan ρ S I ≤ fixedSpace ρ (S ⊓ C) := by
  apply iSup_le
  rintro s _ ⟨v,hv,rfl⟩ b
  have hb : s.val⁻¹ * b.val * s.val ∈ S ⊓ C := by
    constructor
    · exact S.mul_mem (S.mul_mem (S.inv_mem s.property) b.property.1) s.property
    · change s.val⁻¹ * b.val * s.val ∈ C
      simpa only [inv_inv] using (inferInstance : C.Normal).conj_mem b.val b.property.2 s.val⁻¹
  calc
    ρ b.val (ρ s.val v) = ρ s.val (ρ (s.val⁻¹ * b.val * s.val) v) := by
      simp only [←Module.End.mul_apply,←map_mul,←mul_assoc,mul_inv_cancel,one_mul]
    _ = ρ s.val v := congrArg (ρ s.val) (hf hv ⟨_,hb⟩)
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterD
variable {G : Type*} [Group G] {M L U V : Subgroup G} [IsElementaryAbelian 2 U]

/-- The original seed represented under the image of L on U. -/
@[expose] def internalImageSubrepresentation (hn : M ≤ normalizer (U : Set G))
    (hLV : L ≤ normalizer (V : Set G)) :
    Subrepresentation ((UniqueFactor.imageRepresentation M U hn).comp
      ((L.subgroupOf M).map (internalHom M U hn)).subtype) where
  toSubmodule := internalSection U V
  apply_mem_toSubmodule := by
    intro k v hv
    obtain ⟨l,hl,he⟩ := k.property
    change UniqueFactor.imageRepresentation M U hn k.val v ∈ internalSection U V
    rw [←he]
    exact (mem_normalizer_iff.mp (hLV hl) v.toMul.val).mp hv

/-- Passing to the actual component image preserves seed irreducibility. -/
theorem internalImageSubrepresentation_irreducible
    (hn : M ≤ normalizer (U : Set G)) (hLV : L ≤ normalizer (V : Set G))
    (hi : IsIrreducible (internalSubrepresentation hn hLV).toRepresentation) :
    IsIrreducible (internalImageSubrepresentation hn hLV).toRepresentation := by
  exact (irreducible_comp_surjective_iff ((internalHom M U hn).subgroupMap (L.subgroupOf M))
    ((internalHom M U hn).subgroupMap_surjective (L.subgroupOf M))
    (internalImageSubrepresentation hn hLV).toRepresentation).mp hi

/-- The original subgroup orbit embeds in the orbit span under the literal
image of R. This works inside an arbitrary larger elementary module U. -/
theorem internalSection_componentOrbit_le_orbitSpan
    (hn : M ≤ normalizer (U : Set G)) (R : Subgroup G)
    (hRM : R ≤ M) (hVU : V ≤ U) :
    internalSection U (componentOrbit V R) ≤
      Homogeneous.orbitSpan (UniqueFactor.imageRepresentation M U hn)
        ((R.subgroupOf M).map (internalHom M U hn)) (internalSection U V) := by
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let S := (R.subgroupOf M).map f
  let I := Homogeneous.orbitSpan ρ S (internalSection U V)
  let J : Subgroup G := I.toAddSubgroup.toSubgroup'.map U.subtype
  have hWJ : componentOrbit V R ≤ J := by
    refine iSup_le fun r => ?_
    rintro _ ⟨v,hv,rfl⟩
    let r' : M := ⟨r.val,hRM r.property⟩
    let s : S := ⟨f r',⟨r',r.property,rfl⟩⟩
    let w : Additive U := ρ s.val (Additive.ofMul ⟨v,hVU hv⟩)
    have hw : w ∈ I := (le_iSup (fun s : S =>
      (internalSection U V).map (ρ s.val)) s) ⟨_,hv,rfl⟩
    exact ⟨w.toMul,hw,rfl⟩
  intro v hv
  obtain ⟨w,hw,he⟩ := hWJ hv
  exact (show Additive.ofMul w = v from congrArg Additive.ofMul (Subtype.ext he)) ▸ hw
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {P H : Type*} [Group P] [Group H]

/-- A normal subgroup with quasisimple two-core quotient has quasisimple
nontrivial image in a group with trivial two-core. -/
theorem quasisimple_image_of_twoCore_eq_bot
    (f : P →* H) (hf : Function.Surjective f) (N : Subgroup P) [N.Normal]
    (hq : IsQuasisimple (N ⧸ pCore 2 N))
    (hn : N.map f ≠ ⊥) (hcore : pCore 2 H = ⊥) : IsQuasisimple (N.map f) := by
  let : Nontrivial (N.map f) := (Subgroup.nontrivial_iff_ne_bot _).mpr hn
  let := hq
  let g := f.subgroupMap N
  have hk : pCore 2 N ≤ g.ker := by
    have hnorm : ((pCore 2 N).map N.subtype).Normal := inferInstance
    have hm : (((pCore 2 N).map N.subtype).map f) ≤ pCore 2 H :=
      le_sSup ⟨Normal.map hnorm f hf,(pCore_isPGroup.map N.subtype).map f⟩
    intro n hn
    apply Subtype.ext
    exact hcore.le (hm (mem_map_of_mem f (mem_map_of_mem N.subtype hn)))
  let q := QuotientGroup.lift (pCore 2 N) g hk
  exact IsQuasisimple.of_surjective q
    (QuotientGroup.lift_surjective_of_surjective (pCore 2 N) g
      (f.subgroupMap_surjective N) hk)
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
