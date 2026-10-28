module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.Nilpotent
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralNormality
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# The actual Sylow subgroup in the remaining nilpotent row

A nonquasisimple C-component is normal in an SQTK group with trivial
two-core, by the noncentral plane argument of A.3.8. Reflect this normality
through the literal two-core quotient of G₁. Independently, restriction of
the original Sylow subgroup gives T∩I in Syl₂(I), and T∩I=R₁∩I proves
that the original Cartan normalizes it.

The coprime actor fixes the SL₂(5) Fitting quotient. Since the Fitting
kernel has odd order, its quotient map is injective on a preserved
two-subgroup. Thus X fixes the actual image of T∩I in I/O₂(I).
The concluding original-Geometry application obtains the nilpotent row
from the complete component sieve; it assumes no normality, Sylow
alignment or Sylow-action conclusion.

This retains extraspecial factors and arbitrary homocyclic exponents.
It does not exclude the surviving scalar action on the odd radical.
That exclusion and source 11.5.6(3) remain with
qt-d-1222-natural-closure-cartan; the parent qt-d-1222-natural-closure
retains discharge of the preceding flag and Cartan geometry.
Source: Aschbacher--Smith A.3.6 and A.3.8, pp.43--46, and 11.5.6(3),
pp.780--781.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter1.Section02

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

/-- Trivial quotient action fixes each preserved two-subgroup through the odd Fitting kernel. -/
theorem nilpotent_actor_fixes_twoSubgroup {Q : Type*} [Group Q] [Finite Q]
    (hn : A36Nilpotent Q) (hc : A36Common Q) (a : MulAut Q)
    (hcop : Nat.Coprime (orderOf a) (Nat.card Q))
    (S : Subgroup Q) (hS : IsPGroup 2 S)
    (hSa : ∀ s ∈ S, a s ∈ S) : ∀ s ∈ S, a s = s := by
  let q := QuotientGroup.mk' (fittingSubgroup Q)
  have hker : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk',hc.1]
    exact pPrimeCore_coprime_card
  have hf := injective_comp_subtype_of_coprime_ker q hker S hS
  intro s hs
  have he := DFunLike.congr_fun (nilpotent_quotient_actor_eq_one hn hc a hcop) (q s)
  rw [quotientAut_apply_mk] at he
  exact congrArg Subtype.val (@hf ⟨a s,hSa s hs⟩ ⟨s,hs⟩ he)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.OddLinear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- Restrict the original ambient Sylow subgroup to the relative component. -/
theorem exists_component_sylow_intersection (hT : (T : Subgroup G) ≤ E.G₁)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I) :
    ∃ S : Sylow 2 I, (S : Subgroup I) = (T : Subgroup G).subgroupOf I := by
  let A := I.subgroupOf E.G₁
  let e : A ≃* I := subgroupOfEquivOfLe (hI.1.trans E.Y_le_G₁)
  obtain ⟨S,hS⟩ := (T.subtype hT).exists_subgroupOf_eq_of_subnormal A
    (E.component_in_point_normalizer hI).subnormal
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (S : Subgroup A).map e.toMonoidHom = _
  rw [hS]
  ext i
  constructor
  · rintro ⟨s,hs,rfl⟩
    exact hs
  · intro hi
    exact ⟨e.symm i,hi,e.apply_symm_apply i⟩

/-- The surviving nilpotent component is normal in G₁, not just in its normalizer. -/
theorem nilpotent_component_relative_normal (hp : E.point ≠ ⊥)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hn : A36Nilpotent
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁)))) :
    (I.subgroupOf E.G₁).Normal := by
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  have hH : IsSQTK KnownSimple.IsKnownSimple E.G₁ :=
    E.input.source.simpleQTKE.twoLocal_sqtk (D.centralQuotientPreimage_twoLocal E.point hp)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (E.G₁ ⧸ pCore 2 E.G₁) := by
    refine ⟨?_, hH.isKGroup.quotient (pCore 2 E.G₁)⟩
    intro p hprime ho
    let : Fact p.Prime := ⟨hprime⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hprime ho)
  let := pCore_isNilpotent (p := 2) (G := E.G₁)
  have hrel := E.component_in_point_normalizer hI
  have hB := hrel.map_quotient (pCore 2 E.G₁)
  have hnormal : B.Normal := by
    apply (ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hQ
      (pCore_quotient_pCore_eq_bot 2) hB).resolve_right
    intro hs
    let : IsQuasisimple B := hs
    let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hB.ne_bot
    let : Group.IsNilpotent (generalizedFitting B) := hn.2.1
    let : Group.IsNilpotent B := Group.nilpotent_of_mulEquiv
      ((MulEquiv.subgroupCongr (generalizedFitting_eq_top_of_quasisimple (G := B))).trans topEquiv)
    exact Group.IsPerfect.not_isNilpotent B inferInstance
  exact cComponent_normal_of_quotient_normal hrel (pCore 2 E.G₁) hnormal

/-- The literal Cartan quotient action fixes every element of the original Sylow intersection. -/
theorem nilpotent_component_sylow_fixed (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hodd : Odd (Nat.card E.X)) (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hcop : Nat.Coprime (Nat.card E.X) (Nat.card E.Y))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hn : A36Nilpotent
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))))
    (hc : A36Common
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))))
    (x : normalizer (I : Set G)) (hx : (x : G) ∈ E.X)
    (s : I) (hs : (s : G) ∈ (T : Subgroup G)) :
    coreQuotientAction I x (QuotientGroup.mk' (pCore 2 I) s) =
      QuotientGroup.mk' (pCore 2 I) s := by
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  let e := E.componentImageQuotientEquiv hI
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  let a : MulAut B := MulAut.congr e (coreQuotientAction I x)
  let S := ((T : Subgroup G).subgroupOf I).map f
  have ha : Nat.Coprime (orderOf a) (Nat.card B) := by
    have hd : orderOf a ∣ Nat.card E.X := by
      apply ((orderOf_map_dvd (MulAut.congr e).toMonoidHom _).trans
        (orderOf_map_dvd (coreQuotientAction I) x)).trans
      rw [← Subgroup.orderOf_coe x]
      exact E.X.orderOf_dvd_natCard hx
    have hB : Nat.card B ∣ Nat.card E.Y := by
      rw [← Nat.card_congr e.toEquiv]
      exact (pCore 2 I).card_quotient_dvd_card.trans (card_dvd_of_le hI.1)
    exact hcop.of_dvd hd hB
  have hSa : ∀ b ∈ S, a b ∈ S := by
    rintro _ ⟨t,ht,rfl⟩
    let t' := I.normalizerMonoidHom x t
    have ht' : t' ∈ (T : Subgroup G).subgroupOf I := by
      exact (le_normalizer_iff.mp
        (E.cartan_normalizes_component_sylow hp hT hX hodd hXR hI)
        x hx t ⟨ht,t.property⟩).1
    refine ⟨t',ht',?_⟩
    change e (QuotientGroup.mk' (pCore 2 I) t') =
      e (coreQuotientAction I x (e.symm (e (QuotientGroup.mk' (pCore 2 I) t))))
    rw [e.symm_apply_apply, coreQuotientAction_apply_mk]
  have hfix := nilpotent_actor_fixes_twoSubgroup hn hc a ha S
    (T.isPGroup'.comap_subtype.map f) hSa (f s) (mem_map_of_mem f hs)
  change e (coreQuotientAction I x
    (e.symm (e (QuotientGroup.mk' (pCore 2 I) s)))) =
      e (QuotientGroup.mk' (pCore 2 I) s) at hfix
  rw [e.symm_apply_apply] at hfix
  exact e.injective hfix

/-- Translate pointwise fixation back to the intrinsic two-core of the actual component. -/
theorem nilpotent_component_sylow_commutator (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hodd : Odd (Nat.card E.X)) (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hcop : Nat.Coprime (Nat.card E.X) (Nat.card E.Y))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hn : A36Nilpotent
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))))
    (hc : A36Common
      ((I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁)))) :
    ⁅(T : Subgroup G) ⊓ I,E.X⁆ ≤ I.pCoreIn 2 := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx s hs
  let x' : normalizer (I : Set G) :=
    ⟨x,E.cartan_normalizes_component hp hX hodd hI hx⟩
  let s' : I := ⟨s,hs.2⟩
  have he := E.nilpotent_component_sylow_fixed hp hT hX hodd hXR hcop hI hn hc
    x' hx s' hs.1
  rw [coreQuotientAction_apply_mk] at he
  refine ⟨I.normalizerMonoidHom x' s' * s'⁻¹,?_,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (pCore 2 I) (I.normalizerMonoidHom x' s' * s'⁻¹) = 1
  rw [map_mul,map_inv,he,mul_inv_cancel]

/-- Apply the completed catalogue sieve to the original Geometry: every
remaining moved component is relatively normal and has fixed Sylow quotient.
Movement on the odd radical remains to be excluded for source 11.5.6(3). -/
theorem moved_component_normal_and_sylow_fixed (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1) (hodd : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    (I.subgroupOf E.G₁).Normal ∧
      (∃ S : Sylow 2 I, (S : Subgroup I) = (T : Subgroup G).subgroupOf I) ∧
      ⁅(T : Subgroup G) ⊓ I,E.X⁆ ≤ I.pCoreIn 2 := by
  obtain ⟨hn,hc,_⟩ := E.moved_component_nilpotent_fitting_case hp hT hX c
    hcart hXR hCX hz hNG hr hodd hI hmoved
  have hcop := E.cartan_coprime_of_local_action hp hX hcart.odd
    (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
  exact ⟨E.nilpotent_component_relative_normal hp hI hn,
    E.exists_component_sylow_intersection hT hI,
    E.nilpotent_component_sylow_commutator hp hT hX hcart.odd hXR
      (E.cartan_coprime_Y_of_split_marking (c.cartanTorusEquiv hcart) hcop) hI hn hc⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
