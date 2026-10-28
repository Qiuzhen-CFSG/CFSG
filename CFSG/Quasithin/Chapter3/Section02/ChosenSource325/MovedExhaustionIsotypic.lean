module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCubic
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionDisjoint
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.NormalType

/-!
# Full isotypic components of the chosen normalizer orbit

Sum all copies of each simple L-module type, rather than choosing a single
copy. Distinct types give disjoint full isotypic components; when two types
span the orbit they are complementary, and normalizer conjugation permutes
them. The internal-subgroup transport uses the original conjugation action
on U and identifies its simple subrepresentations with the actual L-invariant
subgroups. In particular, it does not assert homogeneity of the chosen seed
inside the larger normalizer orbit.

The actual application is `SeedAlternativesMovedExhaustionIsotypic`.
This supplies the decomposition used before D.3.12. The cubic stabilization
and centralizer exclusions remain with the source325 assembly owner.
Source: Aschbacher--Smith D.3.10, paragraph after D.3.11, printed p.201.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped MonoidAlgebra IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {E W P : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) E W} [Group P]

/-- The full sum of copies of the specified module type. -/
def typePart (S : Subrepresentation σ) : Subrepresentation σ :=
  ⨆ B : {B : Subrepresentation σ // SameModule S B}, B.val

/-- A copy is contained in its full type component. -/
theorem le_typePart (S : Subrepresentation σ) : S ≤ typePart S :=
  le_iSup (fun B : {B : Subrepresentation σ // SameModule S B} => B.val)
    ⟨S,SameModule.refl S⟩

/-- Isomorphic marked copies define the same full component. -/
theorem typePart_eq_of_same {S T : Subrepresentation σ} (h : SameModule S T) :
    typePart S = typePart T := by
  apply le_antisymm
  · exact iSup_le fun B => le_iSup_of_le ⟨B.val,h.symm.trans B.property⟩ le_rfl
  · exact iSup_le fun B => le_iSup_of_le ⟨B.val,h.trans B.property⟩ le_rfl

/-- This sum is the ordinary monoid-algebra isotypic component. -/
theorem typePart_asSubmodule (S : Subrepresentation σ) :
    (typePart S).asSubmodule = isotypicComponent (ZMod 2)[E] σ.asModule S.asSubmodule := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)
  change e (⨆ B : {B : Subrepresentation σ // SameModule S B}, B.val) = _
  rw [e.map_iSup]
  apply le_antisymm
  · exact iSup_le fun B => le_sSup ((sameModule_iff_linearEquiv _ _).mp B.property.symm)
  · apply sSup_le
    intro B hB
    have hsame : SameModule S (e.symm B) := by
      apply (sameModule_iff_linearEquiv _ _).mpr
      change Nonempty (S.asSubmodule ≃ₗ[(ZMod 2)[E]] e (e.symm B))
      rw [e.apply_symm_apply]
      exact hB.map LinearEquiv.symm
    exact le_iSup_of_le ⟨e.symm B,hsame⟩ (e.apply_symm_apply B).ge

/-- Distinct simple types have disjoint full components, even with multiplicities. -/
theorem typePart_disjoint {S T : Subrepresentation σ}
    (hS : IsIrreducible S.toRepresentation) (hT : IsIrreducible T.toRepresentation)
    (hne : ¬ SameModule S T) : Disjoint (typePart S) (typePart T) := by
  let := simple_asSubmodule S hS
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)
  apply disjoint_iff.mpr
  apply e.injective
  rw [e.map_inf,e.map_bot]
  apply disjoint_iff.mp
  change Disjoint (typePart S).asSubmodule (typePart T).asSubmodule
  have hleft : (typePart S).asSubmodule ≤
      isotypicComponent (ZMod 2)[E] σ.asModule S.asSubmodule := by
    change e (⨆ B : {B : Subrepresentation σ // SameModule S B}, B.val) ≤ _
    rw [e.map_iSup]
    exact iSup_le fun B => le_sSup ((sameModule_iff_linearEquiv _ _).mp B.property.symm)
  have hright : (typePart T).asSubmodule =
      ⨆ B : {B : Subrepresentation σ // SameModule T B}, B.val.asSubmodule := e.map_iSup _
  rw [hright]
  apply (component_disjoint_sum S.asSubmodule
    (fun B : {B : Subrepresentation σ // SameModule T B} => B.val.asSubmodule)
    (fun B => simple_asSubmodule B.val (B.property.irreducible hT)) ?_).mono_left hleft
  intro B he
  exact hne (((sameModule_iff_linearEquiv _ _).mpr he).trans B.property.symm)

/-- Conjugation carries the entire type component to the twisted type component. -/
theorem conjugate_typePart (c : TypeAction σ P) (S : Subrepresentation σ) (g : P) :
    c.conjugate g (typePart S) = typePart (c.conjugate g S) := by
  change c.conjugate g (⨆ B : {B : Subrepresentation σ // SameModule S B}, B.val) = _
  rw [(c.conjugate g).map_iSup]
  apply le_antisymm
  · exact iSup_le fun B => le_iSup_of_le
      ⟨c.conjugate g B.val,(c.same g S B.val).mp B.property⟩ le_rfl
  · refine iSup_le fun B => ?_
    have he : SameModule S (c.conjugate g⁻¹ B.val) := by
      have hh := (c.same g⁻¹ _ _).mp B.property
      rwa [c.inv_conjugate] at hh
    exact le_iSup_of_le ⟨c.conjugate g⁻¹ B.val,he⟩ (by rw [c.conjugate_inv])

/-- Two simple types spanning the orbit give complementary full components. -/
theorem two_typeParts_complement (c : TypeAction σ P) (S : Subrepresentation σ)
    (hS : IsIrreducible S.toRepresentation) (t : P)
    (hne : ¬ SameModule S (c.conjugate t S))
    (htypes : ∀ g : P, SameModule S (c.conjugate g S) ∨
      SameModule (c.conjugate t S) (c.conjugate g S))
    (hspan : c.span S = ⊤) :
    IsCompl (typePart S) (typePart (c.conjugate t S)) := by
  refine ⟨typePart_disjoint hS (c.conjugate_irreducible S hS t) hne,?_⟩
  apply codisjoint_iff.mpr
  apply top_unique
  rw [←hspan]
  refine iSup_le fun g => ?_
  rcases htypes g with he | he
  · exact (le_typePart _).trans ((typePart_eq_of_same he).symm.le.trans le_sup_left)
  · exact (le_typePart _).trans ((typePart_eq_of_same he).symm.le.trans le_sup_right)

/-- The full actor permutes the two complete type components. -/
theorem two_typeParts_permuted (c : TypeAction σ P) (S : Subrepresentation σ)
    (t : P)
    (htypes : ∀ g : P, SameModule S (c.conjugate g S) ∨
      SameModule (c.conjugate t S) (c.conjugate g S)) (g : P) :
    c.conjugate g (typePart S) = typePart S ∨
      c.conjugate g (typePart S) = typePart (c.conjugate t S) := by
  rw [conjugate_typePart]
  exact (htypes g).imp (fun h => (typePart_eq_of_same h).symm)
    (fun h => (typePart_eq_of_same h).symm)
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterD
variable {G : Type*} [Group G] {M L U V V' : Subgroup G}
  [IsElementaryAbelian 2 U]

/-- The original conjugation representation, factored through its faithful image. -/
abbrev internalAction (hn : M ≤ normalizer (U : Set G)) :
    Representation (ZMod 2) M (Additive U) :=
  (UniqueFactor.imageRepresentation M U hn).comp (internalHom M U hn)

/-- An L-invariant ambient subgroup as a subrepresentation inside U. -/
def internalSubrepresentation (hn : M ≤ normalizer (U : Set G))
    (hLV : L ≤ normalizer (V : Set G)) :
    Subrepresentation ((internalAction hn).comp (L.subgroupOf M).subtype) where
  toSubmodule := internalSection U V
  apply_mem_toSubmodule l v hv :=
    (mem_normalizer_iff.mp (hLV l.property) v.toMul.val).mp hv

/-- Coordinates retain the original elements of the ambient subgroup. -/
def internalSectionEquiv [IsElementaryAbelian 2 V] (hVU : V ≤ U) : internalSection U V ≃ₗ[ZMod 2] Additive V :=
  { toFun v := Additive.ofMul ⟨v.val.toMul.val,v.property⟩
    invFun v := ⟨Additive.ofMul ⟨v.toMul.val,hVU v.toMul.property⟩,v.toMul.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' := by
      intro c v
      exact ZMod.map_smul
        (show internalSection U V →+ Additive V from
          { toFun v := Additive.ofMul ⟨v.val.toMul.val,v.property⟩
            map_zero' := rfl
            map_add' _ _ := rfl }) c v }

/-- An unchanged-L group intertwiner gives the internal module intertwiner. -/
theorem same_internalSubrepresentation [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 V'] (hn : M ≤ normalizer (U : Set G))
    (hVU : V ≤ U) (hV'U : V' ≤ U)
    (hLV : L ≤ normalizer (V : Set G)) (hLV' : L ≤ normalizer (V' : Set G))
    (hs : SameConjugationModule L V V') :
    SameModule (internalSubrepresentation hn hLV) (internalSubrepresentation hn hLV') := by
  obtain ⟨f,hf⟩ := hs
  let a : Additive V ≃ₗ[ZMod 2] Additive V' :=
    { f.toAdditive with map_smul' := ZMod.map_smul f.toAdditive }
  let e := (internalSectionEquiv hVU).trans (a.trans (internalSectionEquiv hV'U).symm)
  refine ⟨e,?_⟩
  intro l v
  apply (internalSectionEquiv hV'U).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hf ⟨l.val.val,l.property⟩ (internalSectionEquiv hVU v).toMul
    (internalSectionEquiv hVU ((internalSubrepresentation hn hLV).toRepresentation l v)).toMul rfl

/-- Internal module comparison recovers the literal unchanged-L comparison. -/
theorem sameConjugationModule_of_internal [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 V'] (hn : M ≤ normalizer (U : Set G))
    (hLM : L ≤ M) (hVU : V ≤ U) (hV'U : V' ≤ U)
    (hLV : L ≤ normalizer (V : Set G)) (hLV' : L ≤ normalizer (V' : Set G))
    (hs : SameModule (internalSubrepresentation hn hLV) (internalSubrepresentation hn hLV')) :
    SameConjugationModule L V V' := by
  obtain ⟨e,he⟩ := hs
  let f := ((internalSectionEquiv hVU).symm.trans
    (e.trans (internalSectionEquiv hV'U))).toAddEquiv.toMultiplicative
  refine ⟨f,?_⟩
  intro l v w hw
  let l' : L.subgroupOf M := ⟨⟨l.val,hLM l.property⟩,l.property⟩
  let v' := (internalSectionEquiv hVU).symm (Additive.ofMul v)
  have hact : (internalSubrepresentation hn hLV).toRepresentation l' v' =
      (internalSectionEquiv hVU).symm (Additive.ofMul w) := by
    apply Subtype.ext
    apply Additive.toMul.injective
    exact Subtype.ext hw.symm
  have hh := he l' v'
  rw [hact] at hh
  exact congrArg (fun z : internalSection U V' => z.val.toMul.val) hh

/-- Minimal nontrivial L-invariant subgroups are the simple internal modules. -/
theorem internalSubrepresentation_irreducible
    (hn : M ≤ normalizer (U : Set G)) (hLM : L ≤ M)
    (hVU : V ≤ U) (hLV : L ≤ normalizer (V : Set G)) (hV : V ≠ ⊥)
    (hmin : ∀ J : Subgroup G, J ≤ V → L ≤ normalizer (J : Set G) → J = ⊥ ∨ J = V) :
    IsIrreducible (internalSubrepresentation hn hLV).toRepresentation := by
  apply (Subrepresentation.irreducible_iff_isAtom _).mpr
  constructor
  · intro hz
    apply hV
    apply bot_unique
    intro v hv
    have hm : Additive.ofMul (⟨v,hVU hv⟩ : U) ∈
        internalSubrepresentation hn hLV := hv
    rw [hz] at hm
    exact congrArg Subtype.val (Additive.toMul.injective hm)
  · intro B hB
    let J : Subgroup G := B.toSubmodule.toAddSubgroup.toSubgroup'.map U.subtype
    have hJV : J ≤ V := by
      rintro _ ⟨v,hv,rfl⟩
      exact hB.le hv
    have hLJ : L ≤ normalizer (J : Set G) := by
      intro l hl
      apply mem_normalizer_iff.mpr
      intro v
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact ⟨(UniqueFactor.actionHom M U hn ⟨l,hLM hl⟩) w,
          B.apply_mem_toSubmodule ⟨⟨l,hLM hl⟩,hl⟩ hw,rfl⟩
      · intro hv
        have hh : l⁻¹ * (l * v * l⁻¹) * l ∈ J := by
          obtain ⟨w,hw,he⟩ := hv
          refine ⟨(UniqueFactor.actionHom M U hn ⟨l⁻¹,hLM (L.inv_mem hl)⟩) w,
            B.apply_mem_toSubmodule ⟨⟨l⁻¹,hLM (L.inv_mem hl)⟩,L.inv_mem hl⟩ hw,?_⟩
          change l⁻¹ * w.val * (l⁻¹)⁻¹ = _
          change w.val = l * v * l⁻¹ at he
          rw [he,inv_inv]
        convert hh using 1
        group
    rcases hmin J hJV hLJ with hz | he
    · apply Subrepresentation.toSubmodule_injective
      apply bot_unique
      intro v hv
      have hh : v.toMul.val ∈ J := ⟨v.toMul,hv,rfl⟩
      rw [hz] at hh
      exact Additive.toMul.injective (Subtype.ext hh)
    · exact (hB.ne (Subrepresentation.toSubmodule_injective (le_antisymm hB.le (by
        intro v hv
        have hh : v.toMul.val ∈ J := he.symm ▸ hv
        obtain ⟨w,hw,heq⟩ := hh
        exact (show Additive.ofMul w = v from congrArg Additive.ofMul (Subtype.ext heq)) ▸ hw)))).elim
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterD Theory.GroupTheory
variable {G : Type*} [Group G] {M L U V : Subgroup G} [IsElementaryAbelian 2 U]

/-- Normalizer conjugation preserves L-invariance of the original subgroup. -/
theorem normalizes_conjugate (hLV : L ≤ normalizer (V : Set G))
    (g : normalizer (L : Set G)) :
    L ≤ normalizer (V.map (MulAut.conj g.val).toMonoidHom : Set G) := by
  rw [← map_equiv_normalizer_eq V (MulAut.conj g.val)]
  exact (mem_normalizer_iff_map_conj_eq.mp g.property).ge.trans (map_mono hLV)

/-- The image under the action operator is the literal conjugate subgroup. -/
theorem internalSection_map_action (hn : M ≤ normalizer (U : Set G))
    (hVU : V ≤ U) (g : M) :
    (internalSection U V).map (internalAction hn g) =
      internalSection U (V.map (MulAut.conj g.val).toMonoidHom) := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.toMul.val,hw,rfl⟩
  · rintro ⟨w,hw,he⟩
    exact ⟨Additive.ofMul ⟨w,hVU hw⟩,hw,Additive.toMul.injective (Subtype.ext he)⟩

/-- The type action agrees with the actual ambient conjugation map. -/
theorem internal_conjugate_subrepresentation
    (hn : M ≤ normalizer (U : Set G)) (hML : M ≤ normalizer (L : Set G))
    (hVU : V ≤ U) (hLV : L ≤ normalizer (V : Set G)) (g : M) :
    let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hML
    (normalTypeAction (internalAction hn) (L.subgroupOf M)).conjugate g
      (internalSubrepresentation hn hLV) =
    internalSubrepresentation hn (normalizes_conjugate hLV ⟨g.val,hML g.property⟩) := by
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hML
  apply Subrepresentation.toSubmodule_injective
  change (conjugateSubrepresentationOrderIso (internalAction hn) (L.subgroupOf M) g
    (internalSubrepresentation hn hLV)).toSubmodule = _
  rw [conjugateSubrepresentationOrderIso_toSubmodule]
  exact internalSection_map_action hn hVU g

/-- The internal orbit span is the whole original full normalizer orbit. -/
theorem internal_typeAction_span_eq_top
    (hn : M ≤ normalizer (U : Set G)) (hML : M ≤ normalizer (L : Set G))
    (hVU : V ≤ U) (hLV : L ≤ normalizer (V : Set G))
    (hU : U = componentOrbit V M) :
    let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hML
    (normalTypeAction (internalAction hn) (L.subgroupOf M)).span
      (internalSubrepresentation hn hLV) = ⊤ := by
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hML
  let c := normalTypeAction (internalAction hn) (L.subgroupOf M)
  let S := internalSubrepresentation hn hLV
  let J : Subgroup G := (c.span S).toSubmodule.toAddSubgroup.toSubgroup'.map U.subtype
  have hUJ : U ≤ J := by
    rw [hU]
    refine iSup_le fun g => ?_
    rintro x ⟨v,hv,rfl⟩
    let w : Additive U := internalAction hn g (Additive.ofMul ⟨v,hVU hv⟩)
    have hw : w ∈ (c.conjugate g S).toSubmodule := by
      rw [show (c.conjugate g S).toSubmodule =
        (internalSection U V).map (internalAction hn g) from
        conjugateSubrepresentationOrderIso_toSubmodule (internalAction hn) (L.subgroupOf M) g S]
      exact ⟨Additive.ofMul ⟨v,hVU hv⟩,hv,rfl⟩
    exact ⟨w.toMul,(le_iSup (fun g => c.conjugate g S) g) hw,rfl⟩
  apply top_unique
  intro v _
  obtain ⟨w,hw,he⟩ := hUJ v.toMul.property
  exact (show Additive.ofMul w = v from congrArg Additive.ofMul (Subtype.ext he)) ▸ hw
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
