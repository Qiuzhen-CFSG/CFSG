module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport

/-!
# The actual short moved layer inside a normal binary module

Conjugation identifies linear displacement spaces with ambient group
commutators. The short-group normal-layer dichotomy proves that U(L) is
an Irr⁺ member in any containing normal elementary abelian module V.
When L is a block, subnormal core action gives [V,L]=U(L). Every Irr⁺
section selected inside V is therefore this same U(L), by the antichain
property. This retains the module required by C.1.28 when applying B.4.

Source: Aschbacher--Smith C.1.27--28, printed pp.133--134.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
variable {G Q : Type*} [Group G] [Group Q]
variable (V : Subgroup G) [IsElementaryAbelian 2 V]
variable (q : G →* Q) (hq : Function.Surjective q) (hk : q.ker = centralizer (V : Set G))

noncomputable def space (U : Subgroup G) : Submodule (ZMod 2) (Additive V) :=
  NormalElementaryQuotient.subspace V (U.subgroupOf V)

def ambient (S : Submodule (ZMod 2) (Additive V)) : Subgroup G :=
  S.toAddSubgroup.toSubgroup'.map V.subtype

theorem mem_ambient (S : Submodule (ZMod 2) (Additive V)) (v : Additive V) :
    (v.toMul : G) ∈ ambient V S ↔ v ∈ S := by
  constructor
  · rintro ⟨w, hw, he⟩
    have hh : w = v.toMul := Subtype.ext he
    subst w
    exact hw
  · intro hv
    exact ⟨v.toMul, hv, rfl⟩

theorem ambient_injective : Function.Injective (ambient V) := by
  intro S T he
  ext v
  rw [← mem_ambient V S, ← mem_ambient V T, he]

theorem ambient_space (U : Subgroup G) (hu : U ≤ V) : ambient V (space V U) = U := by
  change (U.subgroupOf V).map V.subtype = U
  exact map_subgroupOf_eq_of_le hu

theorem space_ambient (S : Submodule (ZMod 2) (Additive V)) : space V (ambient V S) = S := by
  ext v
  exact mem_ambient V S v

theorem ambient_mono {S T : Submodule (ZMod 2) (Additive V)} (h : S ≤ T) :
    ambient V S ≤ ambient V T := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

variable [V.Normal]

theorem ambient_commutator (S : Submodule (ZMod 2) (Additive V)) (L : Subgroup G) :
    ambient V (subspaceCommutator (NormalElementaryQuotient.representation V q hq hk)
      S (L.map q)) = ⁅ambient V S, L⁆ := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  apply le_antisymm
  · have hS : subspaceCommutator ρ S (L.map q) ≤ space V ⁅ambient V S, L⁆ := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x, ⟨l, hl, rfl⟩, v, hv, rfl⟩
      change ((ρ (q l) v - v).toMul : G) ∈ ⁅ambient V S, L⁆
      change ((ρ (q l) v).toMul : G) / (v.toMul : G) ∈ _
      rw [NormalElementaryQuotient.representation_apply, div_eq_mul_inv]
      rw [commutator_comm]
      exact commutator_mem_commutator hl ((mem_ambient V S v).mpr hv)
    exact (ambient_mono V hS).trans (ambient_space V _
      ((commutator_mono (show ambient V S ≤ V from map_subtype_le _) le_rfl).trans
        (commutator_le_left V L))).le
  · rw [commutator_comm]
    apply commutator_le.mpr
    rintro l hl _ ⟨v, hv, rfl⟩
    have hm : ρ (q l) (Additive.ofMul v) - Additive.ofMul v ∈
        subspaceCommutator ρ S (L.map q) :=
      Submodule.subset_span ⟨q l, mem_map_of_mem q hl, Additive.ofMul v, hv, rfl⟩
    have ha := (mem_ambient V _ _).mpr hm
    change ((ρ (q l) (Additive.ofMul v)).toMul : G) / v ∈ _ at ha
    rw [NormalElementaryQuotient.representation_apply, div_eq_mul_inv] at ha
    exact ha

theorem space_stable (L U : Subgroup G) (hLU : L ≤ normalizer U) :
    L.map q ≤ subspaceStabilizer (NormalElementaryQuotient.representation V q hq hk)
      (space V U) := by
  apply le_subspaceStabilizer
  rintro _ ⟨l, hl, rfl⟩ v hv
  change ((NormalElementaryQuotient.representation V q hq hk (q l) v).toMul : G) ∈ U
  rw [NormalElementaryQuotient.representation_apply]
  exact (mem_normalizer_iff.mp (hLU hl) _).mp hv

theorem ambient_normalized (L : Subgroup G) (S : Submodule (ZMod 2) (Additive V))
    (hs : L.map q ≤ subspaceStabilizer (NormalElementaryQuotient.representation V q hq hk) S) :
    L ≤ normalizer (ambient V S) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  rw [commutator_comm, ← ambient_commutator V q hq hk]
  exact ambient_mono V (subspaceCommutator_le_of_invariant _ hs)


/-- The actual short commutator layer is an Irr⁺ member in the original module. -/
theorem blockSpace_irrPlus (L : Subgroup G) (hL : IsShort L)
    (hU : (blockU L).map L.subtype ≤ V) :
    IsIrrPlus (NormalElementaryQuotient.representation V q hq hk) (L.map q)
      (space V ((blockU L).map L.subtype)) := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  let U := (blockU L).map L.subtype
  have hLU : L ≤ normalizer U := by
    have hh := (blockU L).le_normalizer_map L.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
  have hcomm : ⁅U,L⁆ = U := by
    have hh := congrArg (map L.subtype) (ExceptionalRestrictions.short_commutator hL)
    simpa only [map_commutator, ← MonoidHom.range_eq_map, range_subtype] using hh
  apply isIrrPlus_of_minimal ρ (space_stable V q hq hk L U hLU)
  · apply ambient_injective V
    rw [ambient_commutator V q hq hk, ambient_space V U hU, hcomm]
  · intro hfix
    have hc : blockU L ≤ center L := by
      intro u hu
      rw [mem_center_iff]
      intro l
      have hv : Additive.ofMul (⟨(u : G), hU (mem_map_of_mem L.subtype hu)⟩ : V) ∈
          space V U := mem_map_of_mem L.subtype hu
      have hf := (NormalElementaryQuotient.mem_fixedSpace_image V q hq hk L _).mp (hfix hv)
      exact Subtype.ext (hf l l.property)
    exact hL.irreducible.1.not_ge (le_inf le_rfl hc)
  · intro S hs hSW
    have hSU : ambient V S ≤ U :=
      (ambient_mono V hSW).trans (ambient_space V U hU).le
    have hSL : ambient V S ≤ L := hSU.trans (map_subtype_le _)
    let N := (ambient V S).subgroupOf L
    let : N.Normal := normal_subgroupOf_of_le_normalizer (ambient_normalized V q hq hk L S hs)
    have hNU : N ≤ blockU L := by
      intro x hx
      obtain ⟨y,hy,he⟩ := hSU hx
      exact (Subtype.ext he : y = x) ▸ hy
    rcases short_normal_layer_dichotomy hL N hNU with hcen | he
    · right
      intro v hv
      apply (NormalElementaryQuotient.mem_fixedSpace_image V q hq hk L v).mpr
      intro l hl
      let x : L := ⟨v.toMul,hSL ((mem_ambient V S v).mpr hv)⟩
      exact congrArg Subtype.val (mem_center_iff.mp
        (hcen (show x ∈ N from (mem_ambient V S v).mpr hv)) ⟨l,hl⟩)
    · left
      apply ambient_injective V
      rw [ambient_space V U hU]
      have hh := congrArg (map L.subtype) he
      rw [map_subgroupOf_eq_of_le hSL] at hh
      exact hh

variable [Finite G]

/-- A subnormal block supported in V accounts for the entire L-displacement of V. -/
theorem blockSpace_eq_moved (L : Subgroup G) (hL : IsBlock L)
    (hU : (blockU L).map L.subtype ≤ V) :
    subspaceCommutator (NormalElementaryQuotient.representation V q hq hk) ⊤ (L.map q) =
      space V ((blockU L).map L.subtype) := by
  have hcomm : ⁅V,L⁆ = (blockU L).map L.subtype := by
    apply le_antisymm
    · exact commutator_le_core_commutator_of_isSubnormal L V hL.subnormal
        hL.short.twoPerfect (IsElementaryAbelian.isPGroup 2 V) le_normalizer_of_normal
    · have hh := congrArg (map L.subtype) (ExceptionalRestrictions.short_commutator hL.short)
      have he : ⁅(blockU L).map L.subtype,L⁆ = (blockU L).map L.subtype := by
        simpa only [map_commutator, ← MonoidHom.range_eq_map, range_subtype] using hh
      exact he.ge.trans (commutator_mono hU le_rfl)
  apply ambient_injective V
  rw [ambient_commutator V q hq hk, ambient_space V _ hU]
  have ht : ambient V (⊤ : Submodule (ZMod 2) (Additive V)) = V := by
    have he : space V V = ⊤ := by
      ext v
      exact iff_of_true v.toMul.property (Submodule.mem_top)
    exact he ▸ ambient_space V V le_rfl
  rw [ht, hcomm]

/-- B.1.11's section inside V is the literal U(L), not a replacement module. -/
theorem irrPlus_eq_blockSpace (L : Subgroup G) (hL : IsBlock L)
    (hU : (blockU L).map L.subtype ≤ V)
    {I : Submodule (ZMod 2) (Additive V)}
    (hI : IsIrrPlus (NormalElementaryQuotient.representation V q hq hk) (L.map q) I) :
    I = space V ((blockU L).map L.subtype) := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  apply hI.eq_of_le ρ (blockSpace_irrPlus V q hq hk L hL.short hU)
  calc
    I = subspaceCommutator ρ I (L.map q) := hI.choose_spec.1.symm
    _ ≤ subspaceCommutator ρ ⊤ (L.map q) := subspaceCommutator_mono_left ρ le_top _
    _ = _ := blockSpace_eq_moved V q hq hk L hL hU

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
