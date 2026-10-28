module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixScalarResidualContainment
public import Theory.GroupTheory.CharacteristicTwoCubicResidual

/-!
# The actual cubic complement of the original scalar residual

The original residual X has central cubic image in K/O₂(K). Its full
kernel is a two-group. The scalar core bound places the commutator of
this kernel with X in U; two-perfectness identifies that kernel with U.
Schur--Zassenhaus then supplies an actual subgroup of order three in X.

Source: the first paragraph of Aschbacher--Smith12.7.20, printed p.846.
Here U is the source's original six-dimensional V; the pair denominator
(W∩Wᵍ)U is never substituted for that chosen module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The entire original scalar kernel is U, and X is its split extension
by an actual subgroup of order three, with all groups in the original G. -/
theorem original_tripleSix_central_closure_scalar_splitting
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let X := tripleSixScalarResidual K
    X ⊓ K.pCoreIn 2 = U ∧
      ∃ Y : Subgroup G, Y ≤ X ∧ Nat.card Y = 3 ∧ X = U ⊔ Y ∧ Disjoint U Y := by
  let X := tripleSixScalarResidual K
  let M := K ⊔ (T : Subgroup G)
  have hXK : X ≤ K := map_subtype_le _
  have hUX : U ≤ X := (original_tripleSix_scalar_residual_contains_module
    h structural D a z hz hzT hnot houter).1
  let q := a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let f : X →* center HexEvenAutomorphisms := (q.comp (inclusion hXK)).codRestrict _ (by
    intro x
    rw [←tripleSixScalarResidual_image D a]
    exact ⟨inclusion hXK x,x.property,rfl⟩)
  have hf : Function.Surjective f := by
    intro c
    have hc : c.val ∈ (X.subgroupOf K).map q := by
      rw [tripleSixScalarResidual_image D a]
      exact c.property
    obtain ⟨k,hk,he⟩ := hc
    exact ⟨⟨k.val,hk⟩,Subtype.ext he⟩
  have hmem (x : X) : x ∈ f.ker ↔ x.val ∈ K.pCoreIn 2 := by
    constructor
    · intro hx
      have he : q (inclusion hXK x)=1 := congrArg Subtype.val hx
      have hk : inclusion hXK x ∈ pCore 2 K := by
        apply (QuotientGroup.eq_one_iff _).mp
        exact a.groupEquiv.injective (he.trans a.groupEquiv.map_one.symm)
      exact mem_map_of_mem K.subtype hk
    · rintro ⟨k,hk,he⟩
      have hk' : inclusion hXK x ∈ pCore 2 K :=
        (show k=inclusion hXK x from Subtype.ext he) ▸ hk
      apply Subtype.ext
      change a.groupEquiv (QuotientGroup.mk' (pCore 2 K) (inclusion hXK x))=1
      have hqone : QuotientGroup.mk' (pCore 2 K) (inclusion hXK x)=1 :=
        (QuotientGroup.eq_one_iff _).mpr hk'
      exact (congrArg a.groupEquiv hqone).trans a.groupEquiv.map_one
  have hkp : IsPGroup 2 f.ker :=
    ((isPGroup_pCoreIn 2 K).comap_of_injective X.subtype X.subtype_injective).to_le
      (fun x hx => (hmem x).mp hx)
  let V := U.subgroupOf X
  let : V.Normal := normal_subgroupOf_of_le_normalizer (hXK.trans D.normalizes)
  have hVk : V ≤ f.ker := fun x hx => (hmem x).mpr (D.le_componentCore hx)
  have hXp : IsPPerfect 2 X := by
    let Z := centralPreimage (pCore 2 K)
    let R := (pResidual 2 Z).map Z.subtype
    exact (isPPerfect_embedded_pResidual_of_finite 2 Z).of_surjective
      (R.equivMapOfInjective K.subtype K.subtype_injective).toMonoidHom
      (R.equivMapOfInjective K.subtype K.subtype_injective).surjective
  have hKQ : K.pCoreIn 2 ≤ M.pCoreIn 2 := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le K.le_normalizer D.sylow_normalizes_component)
  have hbound := original_tripleSix_central_closure_scalar_core
    h structural D a z hz hzT hnot houter
  have hkc : ⁅f.ker,(⊤ : Subgroup X)⁆ ≤ V := by
    have hkQ : f.ker.map X.subtype ≤ M.pCoreIn 2 := by
      rintro _ ⟨x,hx,rfl⟩
      exact hKQ ((hmem x).mp hx)
    have hh := (commutator_mono hkQ (show X ≤ X from le_rfl)).trans hbound
    have hm : (⁅f.ker,(⊤ : Subgroup X)⁆).map X.subtype ≤ U := by
      rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
      exact hh
    exact fun x hx => hm (mem_map_of_mem X.subtype hx)
  have he : f.ker=V := f.ker_eq_of_pPerfect_of_coprime_abelian_image hXp V hVk hkp hkc
    (fun x y => (IsMulCommutative.is_comm (M := center HexEvenAutomorphisms)).comm _ _)
    (by decide : Nat.Coprime 2 3) (fun x => by
      have hh := pow_card_eq_one' (x := f x)
      rwa [Hexacode.even_center_card] at hh)
  have hkernel : X ⊓ K.pCoreIn 2=U := by
    apply le_antisymm
    · intro x hx
      have hxV : (⟨x,hx.1⟩ : X) ∈ V := he ▸ (hmem (⟨x,hx.1⟩ : X)).mpr hx.2
      exact hxV
    · exact le_inf hUX D.le_componentCore
  have hindex : V.index=3 := by
    rw [←he,index_ker,MonoidHom.range_eq_top_of_surjective f hf,card_top]
    exact Hexacode.even_center_card
  have hcop : Nat.Coprime (Nat.card V) V.index := by
    rw [hindex]
    obtain ⟨n,hn⟩ := (D.elementary.isPGroup.comap_subtype : IsPGroup 2 V).exists_card_eq
    change Nat.card V=2^n at hn
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  obtain ⟨Y0,hY0⟩ := exists_right_complement'_of_coprime hcop
  let Y := Y0.map X.subtype
  have hYcard : Nat.card Y=3 := by
    rw [card_map_of_injective X.subtype_injective,←hY0.symm.index_eq_card,hindex]
  have hXY : X=U ⊔ Y := by
    have hh := congrArg (map X.subtype) hY0.sup_eq_top
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hUX,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm
  have hd : Disjoint U Y := by
    apply disjoint_def.mpr
    rintro x hx ⟨y,hy,rfl⟩
    exact congrArg Subtype.val (disjoint_def.mp hY0.disjoint hx hy)
  exact ⟨hkernel,Y,map_subtype_le _,hYcard,hXY,hd⟩

end CFSG.Quasithin.Chapter12.Section07
