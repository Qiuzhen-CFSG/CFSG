module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.NaturalSubmodule
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Natural
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.Representation.SpecialLinearThreeTransitivity
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic

/-!
# The original SL₃ block and its literal module

The equality [O₂(L),L]=V identifies U(L) with the chosen V. The proved
natural coordinates retain the original L/O₂(L) projection and conjugation.
Nonzero-vector transitivity proves irreducibility; faithfulness makes O₂(L)
self-centralizing. These establish every short-group clause and the full
SL₃ block model, including its center and actual module quotient.

The commutator premise is discharged from the original V_K in
Block/Source.lean. No core equality O₂(L)=V or exceptional-cover exclusion
is used. The transport follows the same literal block construction as
Closure/Linear/Block/Core.lean, with its independent collapse hypotheses
replaced by the common-core commutator theorem.
Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774 and C.1.7.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.OriginalBlock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
  (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

omit [Finite G] in
theorem blockU_map (hcomm : ⁅L.pCoreIn 2,L⁆ = V) :
    (ChapterC.blockU L).map L.subtype = V := by
  rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  exact hcomm

noncomputable def blockEquiv
    (hcomm : ⁅L.pCoreIn 2,L⁆ = V) : ChapterC.blockU L ≃* V :=
  ((ChapterC.blockU L).equivMapOfInjective L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr (blockU_map hcomm))

omit [Finite G] in
theorem blockEquiv_val
    (hcomm : ⁅L.pCoreIn 2,L⁆ = V) (v : ChapterC.blockU L) :
    (blockEquiv hcomm v : G) = (v.val : G) := rfl

include D S a in
theorem blockFixed_eq_bot
    (hcomm : ⁅L.pCoreIn 2,L⁆ = V) : ChapterC.blockFixed L = ⊥ := by
  apply bot_unique
  intro v hv
  have hz : (v.val : G) ∈ centralizer (L : Set G) := by
    intro l hl
    exact congrArg Subtype.val ((mem_center_iff.mp hv) ⟨l, hl⟩)
  have hvV : (v.val : G) ∈ V :=
    (blockU_map hcomm).le (mem_map_of_mem _ v.property)
  have he : (v.val : G) = 1 := mem_bot.mp ((Preliminary.sl3_centralizer_eq_bot D S a).le ⟨hvV, hz⟩)
  exact mem_bot.mpr (Subtype.ext (Subtype.ext he))

noncomputable def blockModuleEquiv
    (hcomm : ⁅L.pCoreIn 2,L⁆ = V) :
    ChapterC.BlockModule L ≃* Multiplicative (Fin 3 → S.field.Carrier) :=
  (((QuotientGroup.quotientMulEquivOfEq (blockFixed_eq_bot D S a hcomm)).trans
    QuotientGroup.quotientBot).trans (blockEquiv hcomm)).trans (SL3.naturalEquiv D S a)


theorem natural_conjugation (l : L) (v : V) :
    (SL3.naturalEquiv D S a (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd =
      (a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)).val *ᵥ
        (SL3.naturalEquiv D S a v).toAdd :=
  SL3.naturalEquiv_conjugation D S a l v

include D S a in
/-- Nonzero-vector transitivity proves irreducibility on the original seed. -/
theorem seed_irreducible (A : Subgroup G) (hAV : A ≤ V)
    (hLA : L ≤ normalizer (A : Set G)) : A = ⊥ ∨ A = V := by
  by_cases hA : A = ⊥
  · exact Or.inl hA
  right
  apply le_antisymm hAV
  obtain ⟨v₀, ha1⟩ := ne_bot_iff_exists_ne_one.mp hA
  have ha := v₀.property
  have ha1 : (v₀ : G) ≠ 1 := fun he => ha1 (Subtype.ext he)
  have hca : (SL3.naturalEquiv D S a ⟨v₀, hAV ha⟩).toAdd ≠ 0 := by
    intro he
    have hh : (⟨v₀, hAV ha⟩ : V) = 1 := (SL3.naturalEquiv D S a).injective
      (he.trans (SL3.naturalEquiv D S a).map_one.symm)
    exact ha1 (congrArg Subtype.val hh)
  intro v hv
  by_cases hv1 : v = 1
  · simp [hv1]
  have hcv : (SL3.naturalEquiv D S a ⟨v, hv⟩).toAdd ≠ 0 := by
    intro he
    have hh : (⟨v, hv⟩ : V) = 1 := (SL3.naturalEquiv D S a).injective
      (he.trans (SL3.naturalEquiv D S a).map_one.symm)
    exact hv1 (congrArg Subtype.val hh)
  obtain ⟨u, hu⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hca hcv
  obtain ⟨l, hl⟩ := (a.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)) u
  change a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = u at hl
  have he := (natural_conjugation D S a l ⟨v₀, hAV ha⟩).trans
    (by simpa only [hl] using hu)
  have he' : (l : G) * v₀ * (l : G)⁻¹ = v :=
    congrArg Subtype.val ((SL3.naturalEquiv D S a).injective he)
  exact he' ▸ (mem_normalizer_iff.mp (hLA l.property) v₀).mp ha

include D S a in
theorem component_fitting : generalizedFitting L = pCore 2 L := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  intro l hl
  have he : a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [map_one]
    ext w : 1
    obtain ⟨v,rfl⟩ := (SL3.naturalEquiv D S a).surjective (Multiplicative.ofAdd w)
    change (a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)).val *ᵥ
      (SL3.naturalEquiv D S a v).toAdd = (SL3.naturalEquiv D S a v).toAdd
    rw [←natural_conjugation D S a l v]
    congr 2
    apply Subtype.ext
    have hv : (⟨v,D.le_component v.property⟩ : L) ∈ pCore 2 L := by
      obtain ⟨z,hz,he⟩ := D.le_componentCore v.property
      exact (Subtype.ext he : z = ⟨v,D.le_component v.property⟩) ▸ hz
    have hh := congrArg Subtype.val (hl _ hv)
    change (v : G) * (l : G) = (l : G) * (v : G) at hh
    change (l : G) * (v : G) * (l : G)⁻¹ = (v : G)
    rw [←hh,mul_inv_cancel_right]
  exact (QuotientGroup.eq_one_iff l).mp
    (a.groupEquiv.injective (he.trans a.groupEquiv.map_one.symm))

include D S a in
theorem component_short
    (hcomm : ⁅L.pCoreIn 2,L⁆ = V) : ChapterC.IsShort L := by
  have hmap := blockU_map hcomm
  have hcent : ChapterC.blockU L ⊓ center L = ⊥ := by
    rw [← ChapterC.blockFixed_map, blockFixed_eq_bot D S a hcomm, Subgroup.map_bot]
  have hne : ChapterC.blockU L ≠ ⊥ := by
    intro he
    rw [he, Subgroup.map_bot] at hmap
    exact D.ne_bot hmap.symm
  refine ⟨inferInstance, S.source.maximal_faithful.2.1.2.1,
    component_fitting D S a, ?_, ?_, Or.inl S.source.quasisimple, ?_⟩
  · let := D.elementary
    exact IsElementaryAbelian.of_surjective (blockEquiv hcomm).symm.toMonoidHom
      (blockEquiv hcomm).symm.surjective
  · intro v hv w hw
    have hvV : (v : G) ∈ V := hmap.le (mem_map_of_mem L.subtype hv)
    have hcore : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
      pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component)
    exact Subtype.ext ((D.core_centralizes (hcore (mem_map_of_mem L.subtype hw)) _ hvV).symm)
  · refine ⟨by rw [hcent]; exact bot_lt_iff_ne_bot.mpr hne, ?_⟩
    intro N hN _ hNU
    let := hN
    have hn : L ≤ normalizer (N.map L.subtype : Set G) := by
      calc
        L = (normalizer (N : Set L)).map L.subtype := by
          rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
        _ ≤ _ := N.le_normalizer_map L.subtype
    rcases seed_irreducible D S a (N.map L.subtype) ((map_mono hNU).trans_eq hmap) hn with h | h
    · left
      rw [hcent]
      exact map_injective L.subtype_injective (h.trans (Subgroup.map_bot L.subtype).symm)
    · right
      exact map_injective L.subtype_injective (h.trans hmap.symm)

def naturalAction : Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier →*
    MulAut (Multiplicative (Fin 3 → S.field.Carrier)) where
  toFun g := (Matrix.SpecialLinearGroup.toLin' g).toAddEquiv.toMultiplicative
  map_one' := by
    ext v : 1
    change Matrix.SpecialLinearGroup.toLin' 1 (Multiplicative.toAdd v) = Multiplicative.toAdd v
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v : 1
    change Matrix.SpecialLinearGroup.toLin' (g * h) (Multiplicative.toAdd v) =
      Matrix.SpecialLinearGroup.toLin' g (Matrix.SpecialLinearGroup.toLin' h (Multiplicative.toAdd v))
    rw [map_mul]
    rfl

noncomputable def blockModel
    (hcomm : ⁅L.pCoreIn 2,L⁆ = V) : ChapterC.BlockModuleModel L (naturalAction D S) where
  quotientIso := a.groupEquiv
  moduleIso := blockModuleEquiv D S a hcomm
  intertwining l v := by
    change SL3.naturalEquiv D S a (blockEquiv hcomm (ChapterC.blockConjugate L l v)) =
      naturalAction D S (a.groupEquiv (QuotientGroup.mk' (pCore 2 L) l))
        (SL3.naturalEquiv D S a (blockEquiv hcomm v))
    exact natural_conjugation D S a l (blockEquiv hcomm v)

include a in
theorem component_sl3_block
    (hcomm : ⁅L.pCoreIn 2,L⁆ = V) :
    ChapterC.IsSL3EvenBlock L S.field.degree :=
  ⟨Nat.le_of_lt S.nonbinary, component_short D S a hcomm,
    S.field.Carrier, inferInstance, inferInstance, S.field.card_eq,
    naturalAction D S, ⟨blockModel D S a hcomm⟩, fun _ _ => rfl⟩


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.OriginalBlock
