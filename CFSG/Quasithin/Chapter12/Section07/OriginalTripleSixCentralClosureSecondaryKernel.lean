module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureScalarFixedModule
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterModel
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixActionKernel

/-!
# The original secondary action keeps the whole scalar kernel

The actual KT action surjects onto the full hexacode actor with kernel
O₂(KT). Its coordinate action on six letters has kernel X O₂(KT), with
the literal scalar residual X retained. This entire kernel centralizes
the constructed secondary module. The statement supplies descent data;
it does not assert that the secondary action is faithful or natural.

Source: the module V_Y in Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Keep the exact original six-space marking, both full action kernels,
and the secondary module on which the scalar kernel acts trivially. -/
theorem original_tripleSix_central_closure_secondary_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let M := K ⊔ (T : Subgroup G)
    let X := tripleSixScalarResidual K
    let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
    let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
    ∃ (hMU : M ≤ normalizer (U : Set G)) (f : Automizer U →* HexAutomorphisms),
      Function.Bijective f ∧
      (∀ k : K, f (U.normalizerMonoidHom.rangeRestrict ⟨k,D.normalizes k.property⟩) =
        (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
      (∀ (b : Automizer U) (u : U),
        (tripleSixPointCoordinates D a (b.val u)).toAdd =
          Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd) ∧
      (let π := f.comp (U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU))
       Function.Surjective π ∧ π.ker = pCore 2 M ∧
       (hexCoordinateSixHom.comp π).ker = (X.subgroupOf M) ⊔ pCore 2 M ∧
       (hexCoordinateSixHom.comp π).ker ≤ centralizer (V.subgroupOf M : Set M)) := by
  let M := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  let C := M.pCoreIn 2 ⊓ centralizer (X : Set G)
  let V := conjugateSpanBy (C ⊓ omegaCenterIn (T : Subgroup G)) K
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  have hMU : M ≤ normalizer (U : Set G) :=
    sup_le D.normalizes ((structural K h).2.2 U D).1
  obtain ⟨hWT,f,hf,hfk,hK,hchart,_⟩ :=
    original_tripleSix_central_closure_outer_model h structural D a z hz hzT hnot houter
  let α := U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMU)
  let π := f.comp α
  have hmap (J : Subgroup G) (hJ : J ≤ M) :
      (J.subgroupOf M).map π = (inducedAutomizer U J).map f := by
    apply le_antisymm
    · rintro _ ⟨m,hm,rfl⟩
      exact ⟨α m,⟨⟨m,hMU m.property⟩,hm,rfl⟩,rfl⟩
    · rintro _ ⟨_,⟨m,hm,rfl⟩,rfl⟩
      exact ⟨⟨m,hJ hm⟩,hm,rfl⟩
  have hE : hexSign.ker ≤ π.range := by
    rw [←hK,←hmap K le_sup_left]
    exact map_le_range _ _
  have hodd : ¬ π.range ≤ hexSign.ker := by
    intro he
    apply houter
    apply (map_le_map_iff_of_injective hf.1).mp
    rw [hK,←hmap W (hWT.trans le_sup_right)]
    exact (map_le_range _ _).trans he
  have hsurj : Function.Surjective π := by
    apply MonoidHom.range_eq_top.mp
    have htwo : hexSign.ker.index = 2 := by
      rw [index_ker,MonoidHom.range_eq_top.mpr hexSign_surjective,card_top]
      simp [Nat.card_eq_fintype_card]
    have hd : π.range.index ∣ 2 := htwo ▸ index_dvd_of_le hE
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo'
    · exact index_eq_one.mp hone
    · have hi := relIndex_mul_index hE
      rw [htwo,htwo'] at hi
      have hone : hexSign.ker.relIndex π.range = 1 := by omega
      exact (hodd (relIndex_eq_one.mp hone)).elim
  have hk : π.ker = pCore 2 M := by
    apply le_antisymm
    · intro m hm
      have hα : α m = 1 := hf.1 (hm.trans (map_one f).symm)
      have hn : (⟨m,hMU m.property⟩ : normalizer (U : Set G)) ∈ U.normalizerMonoidHom.ker :=
        congrArg Subtype.val hα
      rw [normalizerMonoidHom_ker] at hn
      have hc := (original_tripleSix_action_kernel h structural D a).1 ⟨m.property,hn⟩
      change m ∈ ((pCore 2 M).map M.subtype).comap M.subtype at hc
      rwa [comap_map_eq_self_of_injective M.subtype_injective] at hc
    · intro m hm
      have hn : (⟨m,hMU m.property⟩ : normalizer (U : Set G)) ∈ U.normalizerMonoidHom.ker := by
        rw [normalizerMonoidHom_ker]
        exact D.core_centralizes (mem_map_of_mem M.subtype hm)
      have hα : α m = 1 := Subtype.ext hn
      change f (α m) = 1
      rw [hα,map_one]
  have hXK : X ≤ K := map_subtype_le _
  have hXM : X ≤ M := hXK.trans le_sup_left
  have hXi : (X.subgroupOf M).map π = (center HexEvenAutomorphisms).map hexSign.ker.subtype := by
    rw [←tripleSixScalarResidual_image D a,Subgroup.map_map]
    apply le_antisymm
    · rintro _ ⟨m,hm,rfl⟩
      refine ⟨⟨m,hXK hm⟩,hm,?_⟩
      exact (hfk ⟨m,hXK hm⟩).symm
    · rintro _ ⟨k,hkX,rfl⟩
      refine ⟨⟨k,hXM hkX⟩,hkX,?_⟩
      exact hfk k
  have hXimage : (X.subgroupOf M).map π = zpowers hexZ := by
    rw [hXi,←Hexacode.even_kernel_eq_center,hexEvenCoordinate_kernel,MonoidHom.map_zpowers]
    rfl
  have hqk : (hexCoordinateSixHom.comp π).ker = (X.subgroupOf M) ⊔ pCore 2 M := by
    change hexCoordinateSixHom.ker.comap π = _
    rw [hexCoordinateSix_kernel,←hXimage,Subgroup.comap_map_eq,hk]
  have hv := original_tripleSix_central_closure_scalar_fixed_module
    h structural D a z hz hzT hnot houter
  have hVX : V ≤ centralizer (X : Set G) := hv.2.2.1.trans inf_le_right
  have hr : IsPReduced 2 (V.subgroupOf M) := hv.2.2.2.2.1
  have hqcentral : (hexCoordinateSixHom.comp π).ker ≤ centralizer (V.subgroupOf M : Set M) := by
    rw [hqk]
    refine sup_le ?_ (le_centralizer_iff.mp hr.le_centralizer_pCore)
    intro x hx v hv
    apply Subtype.ext
    exact (le_centralizer_iff.mp hVX hx) v hv
  exact ⟨hMU,f,hf,hfk,hchart,hsurj,hk,hqk,hqcentral⟩

end CFSG.Quasithin.Chapter12.Section07
