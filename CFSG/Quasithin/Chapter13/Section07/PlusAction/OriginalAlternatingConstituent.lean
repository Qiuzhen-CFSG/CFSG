module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalAlternatingFive
public import CFSG.Quasithin.Chapter12.Section02.ChosenModule.InsideReducedWitness
public import CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource.Classification
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient

/-!
# Original alternating constituents in reduced overgroups

A reduced normal subgroup fully moved by a normal component lies in that
component. Restricting it to KT and applying A.4.11 and the original homogeneous
selection produces a ChosenModule inside the same subgroup. The original
alternating mark then embeds in the literal centralizer-quotient action: its
actor map is the quotient lift of inclusion, and its vector map is inclusion
of the original marked constituent. No arbitrary actor isomorphism replaces
that compatibility.

The source consumer is the centralized A5 branch of 13.7.4(1).
Source: Aschbacher--Smith A.4.11, A.1.42, 13.3.2(3), and 13.7.4(1),
printed pp.31--32,60--61,885,937--938.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

private theorem central_two_chief_of_quasisimple
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q] : HasCentralPChiefFactors 2 Q := by
  let e : (Q ⧸ (⊥ : Subgroup Q)) ≃* Q := QuotientGroup.quotientBot
  let : IsQuasisimple (Q ⧸ (⊥ : Subgroup Q)) := IsQuasisimple.of_mulEquiv e.symm
  exact hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
    (⊥ : Subgroup Q) (by simp) inferInstance

/-- Restrict a fully moved normal reduced module to KT without losing its chosen constituent. -/
theorem chosen_inside_reduced_overgroup
    {K X : Subgroup G} [Group.IsPerfect K] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hKX : K ≤ X) (hTX : (T : Subgroup G) ≤ X)
    (hn : X ≤ normalizer (K : Set G)) (hpK : IsPPerfect 2 K)
    (U : Subgroup X) (hU : IsPReduced 2 U) (hne : U ≠ ⊥)
    (hm : ⁅U,K.subgroupOf X⁆ = U) :
    ∃ A : Subgroup G, Nonempty (ChosenModule T K A) ∧ A ≤ U.map X.subtype := by
  let Y := K ⊔ (T : Subgroup G)
  let KX := K.subgroupOf X
  let KY := K.subgroupOf Y
  let B := U.map X.subtype
  have hYX : Y ≤ X := sup_le hKX hTX
  let := hU.normal
  let := hU.elementary
  let : KX.Normal := normal_subgroupOf_of_le_normalizer hn
  have hBK : B ≤ K := by
    change U.map X.subtype ≤ K
    rw [←hm,map_commutator,map_subgroupOf_eq_of_le hKX]
    exact le_normalizer_iff_commutator_le_right.mp ((map_subtype_le U).trans hn)
  have hBY : B ≤ Y := hBK.trans le_sup_left
  have hXB : X ≤ normalizer (B : Set G) := by
    have hh := U.le_normalizer_map X.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,X.range_subtype] using hh
  let D := B.subgroupOf Y
  let : D.Normal := normal_subgroupOf_of_le_normalizer (hYX.trans hXB)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map X.subtype
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hBY
  let : KY.Normal := normal_subgroupOf_of_le_normalizer (hYX.trans hn)
  have hDB : D.map Y.subtype = B := map_subgroupOf_eq_of_le hBY
  have hKY : KY.map Y.subtype = K := map_subgroupOf_eq_of_le le_sup_left
  have hBX : B ≠ ⊥ := by
    exact fun he => hne ((map_eq_bot_iff_of_injective _ X.subtype_injective).mp he)
  have hmB : ⁅B,K⁆ = B := by
    have hh := congrArg (map X.subtype) hm
    simpa only [map_commutator,map_subgroupOf_eq_of_le hKX] using hh
  have hmD : ⁅D,KY⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (map Y.subtype) he
    rw [map_commutator,hDB,hKY,Subgroup.map_bot,hmB] at hh
    exact hBX hh
  let e : KY ≃* K := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect KY := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hp : IsPPerfect 2 KY := hpK.of_surjective e.symm.toMonoidHom e.symm.surjective
  let eQ := QuotientGroup.congr (pCore 2 KY) (pCore 2 K) e (pCore_map_iso 2 e)
  let : IsQuasisimple (KY ⧸ pCore 2 KY) := IsQuasisimple.of_mulEquiv eQ.symm
  have hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 KY) :=
    (hasCentralPChiefFactorsAbove_iff_quotient _).mpr central_two_chief_of_quasisimple
  have hcoreX : KX.pCoreIn 2 ≤ centralizer (U : Set X) := by
    have hnormal : (KX.pCoreIn 2).Normal := ConjAct.normal_of_characteristic_of_normal
    have hle : KX.pCoreIn 2 ≤ pCore 2 X := le_sSup ⟨hnormal,isPGroup_pCoreIn 2 KX⟩
    exact hle.trans (le_centralizer_iff.mp hU.le_centralizer_pCore)
  have hcoreB : K.pCoreIn 2 ≤ centralizer (B : Set G) := by
    have he : (KX.pCoreIn 2).map X.subtype = K.pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 KX X.subtype X.subtype_injective,
        map_subgroupOf_eq_of_le hKX]
    rw [←he]
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    exact congrArg Subtype.val (hcoreX ha b hb)
  have hkill : (pCore 2 KY).map KY.subtype ≤ centralizer (D : Set Y) := by
    intro a ha v hv
    apply Subtype.ext
    have ha' := mem_map_of_mem Y.subtype ha
    change (a : G) ∈ (KY.pCoreIn 2).map Y.subtype at ha'
    rw [map_pCoreIn_of_injective 2 KY Y.subtype Y.subtype_injective,hKY] at ha'
    exact hcoreB ha' v hv
  obtain ⟨R,hRD,hR,hmR⟩ := ChapterA.Section04.exists_reduced_witness_of_moved KY D
    (inferInstance : KY.Normal).isSubnormal hp hchief hmD hkill
  obtain ⟨A,hA,hAR⟩ := exists_chosen_le_reduced_witness (hTX.trans hn) R hR hmR
  exact ⟨A,hA,hAR.trans ((map_mono hRD).trans_eq hDB)⟩


open ChapterB.QuasisimpleSource
omit [Finite G] in
/-- The original alternating constituent embeds equivariantly in the same reduced quotient action. -/
theorem alternating_constituent_quotient_injection
    {K X : Subgroup G} (hKX : K ≤ X) (hn : X ≤ normalizer (K : Set G))
    (U : Subgroup X) (hU : IsPReduced 2 U) (hne : U ≠ ⊥)
    (hm : ⁅U,K.subgroupOf X⁆ = U) {A : Subgroup G} (hAU : A ≤ U.map X.subtype)
    (model : Chapter6.Source.IsConjugationModel K A Chapter6.Source.a5Module) :
    letI := hU.normal
    letI := hU.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set X))
    let C := (K.subgroupOf X).map q
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ∃ f : alternatingGroup (Fin 5) →* C, Function.Injective f ∧
      ∃ i : BinaryPermutation.natural (Fin 5) →+ Additive U, Function.Injective i ∧
        ∀ a v, i (alternatingNatural 5 a v) = ρ (f a) (i v) := by
  let := hU.normal
  let := hU.elementary
  let KX := K.subgroupOf X
  let : KX.Normal := normal_subgroupOf_of_le_normalizer hn
  let q := QuotientGroup.mk' (centralizer (U : Set X))
  let C := KX.map q
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let eK : KX ≃* K := subgroupOfEquivOfLe hKX
  let f₀ : K →* C := (q.subgroupMap KX).comp eK.symm.toMonoidHom
  have hcoreX : KX.pCoreIn 2 ≤ centralizer (U : Set X) := by
    have hnormal : (KX.pCoreIn 2).Normal := ConjAct.normal_of_characteristic_of_normal
    have hle : KX.pCoreIn 2 ≤ pCore 2 X := le_sSup ⟨hnormal,isPGroup_pCoreIn 2 KX⟩
    exact hle.trans (le_centralizer_iff.mp hU.le_centralizer_pCore)
  have hkill : pCore 2 K ≤ f₀.ker := by
    intro k hk
    have hk' : eK.symm k ∈ pCore 2 KX := by
      have hh := mem_map_of_mem eK.symm.toMonoidHom hk
      rwa [pCore_map_iso] at hh
    apply Subtype.ext
    change q (eK.symm k) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hcoreX (mem_map_of_mem KX.subtype hk'))
  let φ : (K ⧸ pCore 2 K) →* C := QuotientGroup.lift (pCore 2 K) f₀ hkill
  obtain ⟨a,b,hmodel⟩ := model
  let : IsSimpleGroup (K ⧸ pCore 2 K) := a.isSimpleGroup
  have hφ : Function.Injective φ := by
    apply φ.ker_eq_bot_iff.mp
    rcases φ.normal_ker.eq_bot_or_eq_top with hb | ht
    · exact hb
    · have he : φ = 1 := φ.ker_eq_top_iff.mp ht
      have hzero : KX ≤ centralizer (U : Set X) := by
        intro k hk
        have hh : φ (QuotientGroup.mk' (pCore 2 K) (eK ⟨k,hk⟩)) = 1 := by rw [he];rfl
        have hh' := congrArg Subtype.val hh
        change q k = 1 at hh'
        exact (QuotientGroup.eq_one_iff _).mp hh'
      apply False.elim
      apply hne
      rw [←hm,commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hzero
  let f := φ.comp a.symm.toMonoidHom
  have hAX : A ≤ X := hAU.trans (map_subtype_le U)
  have hmem (v : A) : (⟨v,hAX v.property⟩ : X) ∈ U := by
    obtain ⟨w,hw,he⟩ := hAU v.property
    exact (Subtype.ext he : w = ⟨v,hAX v.property⟩) ▸ hw
  let i : BinaryPermutation.natural (Fin 5) →+ Additive U := {
    toFun := fun v => Additive.ofMul ⟨⟨b.symm (Multiplicative.ofAdd v),
      hAX (b.symm (Multiplicative.ofAdd v)).property⟩,
      hmem (b.symm (Multiplicative.ofAdd v))⟩
    map_zero' := by
      apply Subtype.ext
      apply Subtype.ext
      change (b.symm 1 : G) = 1
      exact congrArg Subtype.val b.symm.map_one
    map_add' v w := by
      apply Subtype.ext
      apply Subtype.ext
      change (b.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : G) =
        (b.symm (Multiplicative.ofAdd v) : G) * (b.symm (Multiplicative.ofAdd w) : G)
      exact congrArg Subtype.val (map_mul b.symm (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  have hi : Function.Injective i := by
    intro v w hv
    have hb : b.symm (Multiplicative.ofAdd v) = b.symm (Multiplicative.ofAdd w) := by
      apply Subtype.ext
      exact congrArg (fun x : Additive U => ((x.toMul : X) : G)) hv
    exact b.symm.injective hb
  refine ⟨f,hφ.comp a.symm.injective,i,hi,?_⟩
  intro x v
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (a.symm x)
  have hx : a (QuotientGroup.mk' (pCore 2 K) g) = x := by rw [hg]; exact a.apply_symm_apply x
  have hq : (f x : X ⧸ centralizer (U : Set X)) = q (eK.symm g) := by
    change (φ (a.symm x) : X ⧸ centralizer (U : Set X)) = _
    rw [←hg]
    rfl
  change i (alternatingNatural 5 x v) = ρ (f x : X ⧸ centralizer (U : Set X)) (i v)
  rw [hq]
  apply Subtype.ext
  apply Subtype.ext
  have hh := hmodel g (b.symm (Multiplicative.ofAdd v))
  rw [hx,MulEquiv.apply_symm_apply] at hh
  exact hh.trans (congrArg Subtype.val (NormalElementaryQuotient.representation_apply U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (eK.symm g) (i v))).symm



end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
