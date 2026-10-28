module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ChiefPair
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.TerminalExclusion
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Stellmacher.ElementaryAbelianMaxGlobalClosure

/-!
# The literal KS quotient from the source Thompson layer

The global J(H) lies in the H-normal subgroup KS, because J(T) centralizes
ZS. If O₂(H) lies in S, the image of KS in H/O₂(H) is proper. It contains
the original Thompson image, already identified with S₃ × S₃ of index two,
so the images coincide. Relative normality identifies the intrinsic
KS/O₂(KS) with that same image.

Reducibility supplies the core containment. This proves the paired quotient
used by the terminal component on the original maps, and gives its binary
application with reducibility as the sole remaining local action input.
It does not identify the individual chief-space centralizers H₁,H₂, nor
assert reducibility for an arbitrary terminal binary component.

Source: Aschbacher--Smith15.2.21(1), printed p.1114; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 ChapterD ChapterD.UniqueFactor PlaneUniquenessPreceding.OmegaAction TerminalLinear
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Normal closure of the original J(T) lies in the literal KS. -/
theorem thompson_le_residual_plane_join (hI : PlaneEscapes Mc ZS I) :
    elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ (KS H T ZS).subgroupOf H := by
  let B := (KS H T ZS).subgroupOf H
  let P := T.subtype d.geometry.outside.1.1.2
  let : B.Normal := normal_subgroupOf_of_le_normalizer (d.residual_plane_join_normalized hI)
  rw [elementaryAbelianMaxJ_top_eq_normalClosure_sylow P]
  apply normalClosure_le_normal
  have hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ smallActionS T ZS :=
    le_inf (sSup_le fun _ hA => hA.1)
      (hsource.centralizing.trans (centralizer_le
        (d.geometry.plane_le.trans hsource.prepared.le_local)))
  have hm : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    change elementaryAbelianMaxJ (((T : Subgroup G).subgroupOf H).map H.subtype) = _
    rw [map_subgroupOf_eq_of_le d.geometry.outside.1.1.2]
  intro x hx
  exact (show smallActionS T ZS ≤ KS H T ZS from le_sup_right)
    (hJS (hm ▸ mem_map_of_mem H.subtype hx))

/-- Core containment identifies the actual KS image with the distinguished J(H) image. -/
theorem residual_plane_image_eq_thompson (hI : PlaneEscapes Mc ZS I)
    (hQ : H.pCoreIn 2 ≤ smallActionS T ZS) :
    ((KS H T ZS).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) =
      (elementaryAbelianMaxJ (⊤ : Subgroup H)).map (QuotientGroup.mk' (pCore 2 H)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := (elementaryAbelianMaxJ (⊤ : Subgroup H)).map q
  let B := (KS H T ZS).subgroupOf H
  have hAB : A ≤ B.map q := map_mono (thompson_le_residual_plane_join d hI)
  have hcardA : Nat.card A = 36 := by
    obtain ⟨e⟩ := thompson_core_image_pair d
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_prod,Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,
      Fintype.card_perm,Nat.factorial]
  have hcardH : Nat.card (H ⧸ pCore 2 H) = 72 := by
    rw [Nat.card_congr d.geometry.quotient.some.toEquiv,RegularWreathProduct.card]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hindex : A.index = 2 := by
    have hc := A.card_mul_index
    rw [hcardA,hcardH] at hc
    omega
  have hmax : IsCoatom A := by
    refine ⟨fun ht => by simp [ht] at hindex, fun C hAC => ?_⟩
    have hm := relIndex_mul_index hAC.le
    rw [hindex] at hm
    have hp : (A.relIndex C * C.index).Prime := by rw [hm]; exact Nat.prime_two
    rcases Nat.prime_mul_iff.mp hp with ⟨_,hC⟩ | ⟨_,hrel⟩
    · exact index_eq_one.mp hC
    · exact (hAC.not_ge (relIndex_eq_one.mp hrel)).elim
  rcases hmax.le_iff.mp hAB with he | he
  · have hker : q.ker ≤ B := by
      rw [QuotientGroup.ker_mk']
      intro x hx
      exact (show smallActionS T ZS ≤ KS H T ZS from le_sup_right)
        (hQ (mem_map_of_mem H.subtype hx))
    have hb := congrArg (Subgroup.comap q) he
    rw [comap_map_eq_self hker,comap_top] at hb
    exfalso
    apply d.sylow_not_le_escape hI
    intro x hx
    have hm : (⟨x,d.geometry.outside.1.1.2 hx⟩ : H) ∈ B := hb ▸ mem_top _
    exact ((d.residual_sup_planeSylow_le hI).trans inf_le_right) hm
  · exact he

/-- The intrinsic KS quotient, through its original embedding in H. -/
theorem pair_quotient_of_core_le (hI : PlaneEscapes Mc ZS I)
    (hQ : H.pCoreIn 2 ≤ smallActionS T ZS) :
    Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let B := (KS H T ZS).subgroupOf H
  have hBH : KS H T ZS ≤ H :=
    sup_le (map_subtype_le _) (inf_le_left.trans d.geometry.outside.1.1.2)
  let : B.Normal := normal_subgroupOf_of_le_normalizer (d.residual_plane_join_normalized hI)
  let a := (subgroupOfEquivOfLe hBH).symm
  let e := QuotientGroup.congr (pCore 2 (KS H T ZS)) (pCore 2 B) a (pCore_map_iso 2 a)
  obtain ⟨b⟩ := thompson_core_image_pair d
  exact ⟨e.trans ((coreQuotientEquivImage 2 B).trans
    ((MulEquiv.subgroupCongr (residual_plane_image_eq_thompson d hI hQ)).trans b))⟩

/-- The quotient consequence of corrected15.2.21(1), with core containment discharged. -/
theorem pair_quotient_of_reducible (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H)) :
    Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :=
  pair_quotient_of_core_le d hI (core_le_planeSylow_of_reducible d hI hnot)

/-- The paired quotient and S-reducibility are equivalent on the original K,S. -/
theorem pair_quotient_iff_reducible (hI : PlaneEscapes Mc ZS I) :
    Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ↔
      ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H) :=
  ⟨reducible_of_symmetricThreePair d,pair_quotient_of_reducible d hI⟩

/-- Actual binary terminal application: the original wreath and Thompson
layer discharge its pair quotient once the original S-action is reducible. -/
theorem binaryBranch_false_of_reducible
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃* ChosenGeometry.Wreath))
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    {n : ℕ} (b : BinaryBranch M I X n)
    (hX : X = (primeToResidual 3 I).map I.subtype)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (hNI : ¬ M ⊓ I ≤ Mc ⊓ I)
    (eNI : intersectionImage hsource I ≃* Equiv.Perm (Fin 3)) :
    letI := hsource.prepared.elementary
    SourceCases.Omega (imageRepresentation M V hsource.prepared.normalized) → False :=
  binaryBranch_false_from_smallActions d hquotient horbit hI hfit hn hout b hX hKX
    (pair_quotient_of_reducible d hI hnot) hNI eNI

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
