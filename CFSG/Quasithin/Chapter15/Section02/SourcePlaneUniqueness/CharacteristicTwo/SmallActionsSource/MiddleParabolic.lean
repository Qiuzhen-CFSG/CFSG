module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Orbit
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.CubicSeeds
public import Theory.SpecificGroups.BinaryLinear.FourMiddleLift
public import Theory.GroupTheory.PResidual.OrderSix
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.PResidual.SylowIndexThree

/-!
# The middle parabolic in the original L₄(2) branch

Lift the automorphism-invariant middle node through the literal quotient
Kc/O₂(Kc). Its index-three product with T lies in M: an escaping minimal
overgroup would have the order-72 wreath quotient of 15.2.8. The intersection
formula of 15.2.14(5) then puts its two-residual Y₀ inside C_M(V).

When S is reducible, Kc centralizes ZS. Intersecting the original T with the
lift therefore gives the original S-intersection, so Y₀S/O₂(Y₀S) is S₃.
Consequently the three-prime centralizer branch is impossible. ElementaryStar
applies this to the actual elementary-nine residual of 15.2.3.

The wreath-quotient and component-orbit premises are earlier source inputs
owned by the small-parabolic and plane-geometry source developments; final
plane-uniqueness assembly must supply them. No split or normalizer
contradiction is assumed here.

Source: Aschbacher--Smith 15.2.21(3), printed p.1114; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

omit d in
include hsource in
/-- Original 15.2.8 excludes an escaping cubic overgroup of T: its
wreath quotient would require a factor nine in its order. -/
theorem cubic_overgroup_le_M
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    {X : Subgroup G} (hTX : (T : Subgroup G) ≤ X) (hXMc : X ≤ Mc)
    (hi : (T : Subgroup G).relIndex X = 3) : X ≤ M := by
  classical
  by_contra hn
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hsource.partner ▸ Set.mem_singleton _
  have hX : X ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTX hXMc
      ⟨Chapter1.mem_H_of_isTwoLocal hMc.1.1, hTX.trans hXMc⟩
  let F : Set (Subgroup G) := {P | P ∈ Chapter1.HOver G (T : Set G) ∧ ¬ P ≤ M ∧ P ≤ X}
  obtain ⟨P, hP⟩ := (Set.toFinite F).exists_minimalFor id F ⟨X, hX, hn, le_rfl⟩
  have hpstar : P ∈ Chapter3.HStar (T : Subgroup G) M := by
    refine ⟨⟨hP.1.1, hP.1.2.1⟩, ?_⟩
    intro Q hQ hQP
    exact hP.2 ⟨hQ.1, hQ.2, hQP.trans hP.1.2.2⟩ hQP
  obtain ⟨e⟩ := hquotient P hpstar
  have hc : Nat.card (P ⧸ pCore 2 P) = 72 := by
    rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card]
  have h9 : 9 ∣ Nat.card X :=
    (show 9 ∣ Nat.card (P ⧸ pCore 2 P) by rw [hc]; decide).trans
      ((card_quotient_dvd_card _).trans (card_dvd_of_le hP.1.2.2))
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) (T : Subgroup G) X bot_le hTX
  rw [relIndex_bot_left,relIndex_bot_left,hi] at hcard
  rw [←hcard] at h9
  have h3 : 3 ∣ Nat.card T := by
    have hh : 3 * 3 ∣ Nat.card T * 3 := h9
    exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 3)).mp hh
  obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop) h3

/-- Construct the actual middle parabolic in Kc, and put its residual in
C_M(V) using 15.2.8 and the literal intersection formula of 15.2.14(5). -/
theorem exists_middle_residual_in_centralizer
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (eK : (smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ∃ E : Subgroup G, E ≤ smallActionKc H Mc ∧
      (T : Subgroup G) ≤ normalizer (E : Set G) ∧
      (T : Subgroup G).relIndex (E ⊔ (T : Subgroup G)) = 3 ∧
      E ⊔ (T : Subgroup G) ≤ M ∧
      Nonempty ((E ⧸ pCore 2 E) ≃* Equiv.Perm (Fin 3)) ∧
      (pResidual 2 E).map E.subtype ≤ M ⊓ centralizer (V : Set G) := by
  have hTMc : (T : Subgroup G) ≤ Mc :=
    d.geometry.outside.1.1.2.trans d.geometry.in_partner
  have hKMc : smallActionKc H Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans d.geometry.in_partner)
  obtain ⟨E,hEK,hTE,hi,he⟩ := BinaryLinear.FourMiddleLift.exists_middle_lift T
    (smallActionKc H Mc) (hTMc.trans (le_normalizer_conjugateSpanBy _ _))
    (eK.trans (BinaryLinear.OuterCyclic.slEquivLinear 4))
  have hEMc := hEK.trans hKMc
  have hPM := cubic_overgroup_le_M (hsource := hsource) hquotient le_sup_right (sup_le hEMc hTMc) hi
  refine ⟨E,hEK,hTE,hi,hPM,he,?_⟩
  exact (embedded_pResidual_mono 2 (le_inf (le_sup_left.trans hPM) hEMc)).trans
    d.partner_intersection_residual_le_module_centralizer

/-- The same middle residual has the required S₃ quotient after adjoining
S. The Sylow subgroup is the actual C_T(ZS), not a separately chosen lift. -/
theorem middle_planeSylow_quotient {I E : Subgroup G}
    (hI : PlaneEscapes Mc ZS I) (hEI : E ≤ I)
    (hTE : (T : Subgroup G) ≤ normalizer (E : Set G))
    (hi : (T : Subgroup G).relIndex (E ⊔ (T : Subgroup G)) = 3)
    (eE : (E ⧸ pCore 2 E) ≃* Equiv.Perm (Fin 3)) :
    Nonempty (((E ⊔ smallActionS T ZS : Subgroup G) ⧸
      pCore 2 (E ⊔ smallActionS T ZS : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  let S := smallActionS T ZS
  let D := E ⊔ S
  have hSE : S ≤ normalizer (E : Set G) := inf_le_left.trans hTE
  have hTS : (T : Subgroup G).subgroupOf E = S.subgroupOf E := by
    ext x
    constructor
    · intro hx
      have hh : (x : G) ∈ I ⊓ (T : Subgroup G) := ⟨hEI x.property,hx⟩
      rw [d.twoGroup_intersection hI le_rfl] at hh
      exact hh.1
    · exact fun hx => (show S ≤ (T : Subgroup G) from inf_le_left) hx
  have hindex : (S.subgroupOf D).index = 3 := by
    change S.relIndex (E ⊔ S) = 3
    rw [relIndex_sup_of_normalizes_left E S hSE]
    rw [relIndex_sup_of_normalizes_left E (T : Subgroup G) hTE] at hi
    change ((T : Subgroup G).subgroupOf E).index = 3 at hi
    rwa [hTS] at hi
  have hp : IsPGroup 2 (S.subgroupOf D) :=
    (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
  let P : Sylow 2 D := hp.toSylow (by rw [hindex]; decide)
  apply sylow_index_three_core_quotient P hindex
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P)
  intro he
  have hRcore : (T : Subgroup G).subgroupOf E ≤ pCore 2 E := by
    intro x hx
    have hxS : x ∈ S.subgroupOf E := by rwa [← hTS]
    let xD : D := ⟨x, (show S ≤ D from le_sup_right) hxS⟩
    have hxP : xD ∈ (P : Subgroup D) := hxS
    have hxD : xD ∈ pCore 2 D := he.symm ▸ hxP
    have hxC : (x : G) ∈ E.pCoreIn 2 :=
      inf_pCoreIn_le_of_le 2 (show E ≤ D from le_sup_left)
        ⟨x.property,mem_map_of_mem D.subtype hxD⟩
    obtain ⟨y,hy,hyx⟩ := hxC
    exact (show y = x from Subtype.ext hyx) ▸ hy
  have hd := index_dvd_of_le hRcore
  have hiE : ((T : Subgroup G).subgroupOf E).index = 3 := by
    rwa [relIndex_sup_of_normalizes_left E (T : Subgroup G) hTE] at hi
  have hc : (pCore 2 E).index = 6 := by
    rw [index_eq_card,Nat.card_congr eE.toEquiv,Nat.card_perm,Nat.card_fin]
    rfl
  rw [hiE,hc] at hd
  omega

/-- In the reducible L₄ branch, the middle residual lies in C_M(V) and
its product with the original S has the S₃ core quotient used in 15.2.21(3). -/
theorem exists_middle_seed
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    {I : Subgroup G} (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (eK : (smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ∃ Y₀ : Subgroup G, Y₀ ≤ M ⊓ centralizer (V : Set G) ∧
      Y₀ ≤ smallActionKc H Mc ∧ IsPPerfect 2 Y₀ ∧
      (T : Subgroup G) ≤ normalizer (Y₀ : Set G) ∧
      Nat.card (Y₀ ⧸ pCore 2 Y₀) = 3 ∧
      Nonempty (((Y₀ ⊔ smallActionS T ZS : Subgroup G) ⧸
        pCore 2 (Y₀ ⊔ smallActionS T ZS : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨E,hEK,hTE,hi,_,⟨eE⟩,hRC⟩ := exists_middle_residual_in_centralizer d hquotient eK
  have hEI : E ≤ I := hEK.trans ((orbit_centralizes_of_reducible d horbit hI hnot).trans
    ((d.centralizer_le_intersection hI).trans inf_le_right))
  let Y₀ := (pResidual 2 E).map E.subtype
  have hYE : Y₀ ≤ E := map_subtype_le _
  have hSY : (T : Subgroup G) ≤ normalizer (Y₀ : Set G) :=
    hTE.trans (normalizer_le_normalizer_characteristic_image E (pResidual 2 E))
  obtain ⟨R,hR⟩ := NormalSylowQuotientAction.intersection_sylow T E hTE
  have hRS : (R : Subgroup E).map E.subtype ≤ smallActionS T ZS := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hh : (y : G) ∈ I ⊓ (T : Subgroup G) := ⟨hEI y.property,show y ∈ (T : Subgroup G).subgroupOf E from hR ▸ hy⟩
    rw [d.twoGroup_intersection hI le_rfl] at hh
    exact hh.1
  have hEYS : E ≤ Y₀ ⊔ smallActionS T ZS := by
    have hh := congrArg (Subgroup.map E.subtype) (pResidual_sup_sylow_eq_top R)
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.ge.trans (sup_le_sup_left hRS _)
  have hjoin : Y₀ ⊔ smallActionS T ZS = E ⊔ smallActionS T ZS :=
    le_antisymm (sup_le_sup_right hYE _) (sup_le hEYS le_sup_right)
  have hquot : Nonempty (((Y₀ ⊔ smallActionS T ZS : Subgroup G) ⧸
      pCore 2 (Y₀ ⊔ smallActionS T ZS : Subgroup G)) ≃* Equiv.Perm (Fin 3)) := by
    rw [hjoin]
    exact middle_planeSylow_quotient d hI hEI hTE hi eE
  have hp := isPPerfect_embedded_pResidual 2 E
  have seed : Seed M I (smallActionS T ZS) Y₀ :=
    ⟨le_inf (hRC.trans inf_le_left) (hYE.trans hEI),hp,inf_le_left.trans hSY,hquot⟩
  exact ⟨Y₀,hRC,hYE.trans hEK,hp,hSY,
    seed.core_quotient_card (T.isPGroup'.to_le inf_le_left),hquot⟩


/-- The middle-node construction excludes the three-prime centralizer branch
of 15.2.21(3); no supplied local split or normalizer callback is used. -/
theorem linearFour_irreducible_of_threePrime
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    {I : Subgroup G} (hI : PlaneEscapes Mc ZS I)
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (eK : (smallActionKc H Mc ⧸ pCore 2 (smallActionKc H Mc)) ≃*
      Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) := by
  by_contra hn
  obtain ⟨Y₀,hYC,hYK,hp,hTY,_,hq⟩ := exists_middle_seed d hquotient horbit hI hn eK
  have hYI : Y₀ ≤ I := hYC.trans (inf_le_right.trans (d.module_centralizer_le hI))
  have seed : Seed M I (smallActionS T ZS) Y₀ :=
    ⟨le_inf (hYC.trans inf_le_left) hYI,hp,inf_le_left.trans hTY,hq⟩
  apply seed.not_le_MI d hC
  exact le_inf (hYK.trans (conjugateSpanBy_le_self
    ((map_subtype_le _).trans d.geometry.in_partner))) hYI
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
