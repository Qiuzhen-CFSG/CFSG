module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Selection
public import Theory.GroupTheory.WreathTwoCoreQuotient
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Generation and relative normality from the actual wreath quotient

The quotient H/O₂(H) is the source wreath product. Its Sylow maximality
identifies H ∩ M and N_H(V) with T. Every subgroup outside T consequently
generates H together with T. For a quadratic Delta actor, this proves
H-invariance of its commutator plane from the established T-invariance.
The plane centralizer is then normal in H and supplemented by T, so it
contains the actual O²(H).

This shorter route removes the marked-generator premise from the plane
consumer. Uniform Delta quadraticity and fixed-centralizer equality remain
local obligations of qt-e-152-offender-plane. The preceding action alternatives
and wreath quotient are supplied by qt-e-152-small-parabolic and discharged
in the final assembly by qt-e-152-plane-geometry.

Source: Aschbacher--Smith 15.2.8--11, printed pp.1110--1111.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor
namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01
variable {G : Type*} [Group G] [Finite G]

/-- The chosen module has the full original maximal-local normalizer. -/
theorem ChosenSmallSource.normalizer_eq_selected
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    normalizer (V : Set G) = M := by
  let := h.prepared.elementary
  exact (h.maximal.1.1.eq_of_le
    ⟨V,h.prepared.nontrivial,IsElementaryAbelian.isPGroup 2 V,rfl⟩
    h.prepared.normalized).symm

/-- Maximality of the original Sylow subgroup follows through the literal
wreath quotient, with the entire two-core in the original Sylow kernel. -/
theorem ChosenSmallSource.wreath_intersections
    {T : Sylow 2 G} {M Mc V H : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    H ⊓ M = (T : Subgroup G) ∧
      H ⊓ normalizer (V : Set G) = (T : Subgroup G) := by
  obtain ⟨e⟩ := he
  let ew := RegularWreathProduct.congr SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let S := T.subtype hTH
  have hc := WreathTwoResidual.sylow_isCoatom_of_core_quotient S (e.trans ew)
  have hSB : (S : Subgroup H) ≤ M.subgroupOf H := fun _ hx => h.maximal.1.2 hx
  have hBT : M.subgroupOf H = (S : Subgroup H) := by
    rcases hc.le_iff.mp hSB with hb | hb
    · exfalso
      apply hH.1.2
      intro x hx
      exact show (⟨x,hx⟩ : H) ∈ M.subgroupOf H from hb ▸ mem_top _
    · exact hb
  have heq : H ⊓ M = (T : Subgroup G) := by
    have hm := congrArg (Subgroup.map H.subtype) hBT
    rw [subgroupOf_map_subtype,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,inf_comm] at hm
    exact hm
  exact ⟨heq,by rw [h.normalizer_eq_selected,heq]⟩

/-- Every actual offender outside T generates H together with T. -/
theorem ChosenSmallSource.offender_sup_sylow_eq
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hA : A ≤ H) (hAT : ¬ A ≤ (T : Subgroup G)) :
    A ⊔ (T : Subgroup G) = H := by
  have hle : A ⊔ (T : Subgroup G) ≤ H := sup_le hA hH.1.1.2
  apply le_antisymm hle
  by_contra hn
  have hM := Chapter3.HStar.proper_overgroup_le T hH le_sup_right
    (lt_of_le_not_ge hle hn)
  have hAB : A ≤ H ⊓ M := le_inf hA (le_sup_left.trans hM)
  exact hAT ((h.wreath_intersections hH he).1 ▸ hAB)

/-- The plane is H-invariant because its quadratic actor and T generate H. -/
theorem ChosenSmallSource.sigmaOutside_normalized_of_wreath
    {T : Sylow 2 G} {M Mc V H B : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hquad : ∀ A ∈ delta H, ⁅⁅conjugateSpan H V,A⁆,A⁆ = ⊥)
    (hfix : ∀ A ∈ delta H,
      conjugateSpan H V ⊓ centralizer (A : Set G) =
        conjugateSpan H V ⊓ centralizer (A ⊓ twoCoreIn H : Subgroup G))
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    H ≤ normalizer (⁅V,B⁆ : Subgroup G) := by
  let := h.prepared.elementary
  have hTZ := (h.sigmaOutside_plane ha hH (h.wreath_intersections hH he).2 hquad hfix hB).2.2.2.2
  obtain ⟨A,hA,hAT,rfl⟩ := exists_offender_of_mem_sigmaOutside hB
  have hVU : V ≤ conjugateSpan H V := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hc : A ≤ centralizer (⁅V,A ⊓ twoCoreIn H⁆ : Subgroup G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (bot_unique ((commutator_mono (commutator_mono hVU inf_le_left) le_rfl).trans
        (hquad A hA).le)))
  exact (h.offender_sup_sylow_eq hH he hA.1.1 hAT).ge.trans
    (sup_le (hc.trans (Subgroup.centralizer_le_normalizer _)) hTZ)

/-- A quadratic outside actor centralizes the plane, so the normal plane's
centralizer has a two-subgroup supplement. Its quotient kills O²(H). -/
theorem ChosenSmallSource.sigmaOutside_residual_centralizes_of_wreath
    {T : Sylow 2 G} {M Mc V H B : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hquad : ∀ A ∈ delta H, ⁅⁅conjugateSpan H V,A⁆,A⁆ = ⊥)
    (hfix : ∀ A ∈ delta H,
      conjugateSpan H V ⊓ centralizer (A : Set G) =
        conjugateSpan H V ⊓ centralizer (A ⊓ twoCoreIn H : Subgroup G))
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    ChosenGeometry.residual H ≤ centralizer (⁅V,B⁆ : Subgroup G) := by
  have hn := h.sigmaOutside_normalized_of_wreath ha hH he hquad hfix hB
  obtain ⟨A,hA,hAT,rfl⟩ := exists_offender_of_mem_sigmaOutside hB
  let Z := (⁅V,A ⊓ twoCoreIn H⁆ : Subgroup G)
  let C := (centralizer (Z : Set G)).subgroupOf H
  let S := T.subtype hH.1.1.2
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (hn.trans (normalizer_le_normalizer_centralizer _))
  have hVU : V ≤ conjugateSpan H V := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hc : A ≤ centralizer (Z : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (bot_unique ((commutator_mono (commutator_mono hVU inf_le_left) le_rfl).trans
        (hquad A hA).le)))
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hH.1.1.2
  have hsup : C ⊔ (S : Subgroup H) = ⊤ := by
    apply (map_injective H.subtype_injective)
    rw [Subgroup.map_sup,subgroupOf_map_subtype,hS,
      ←MonoidHom.range_eq_map,range_subtype]
    refine le_antisymm (show centralizer (Z : Set G) ⊓ H ⊔ (T : Subgroup G) ≤ H from
      sup_le inf_le_right hH.1.1.2) ?_
    exact (h.offender_sup_sylow_eq hH he hA.1.1 hAT).ge.trans
      (sup_le_sup (le_inf hc hA.1.1) le_rfl)
  have hK : pResidual 2 H ≤ C :=
    sInf_le ⟨inferInstance,isPGroup_quotient_of_sup_eq_top C S S.isPGroup' hsup⟩
  rintro z ⟨k,hk,rfl⟩
  exact hK hk

/-- Normalizer bookkeeping in the plane consumer is supplied by 15.2.8.
The uniform chief identities remain explicit local obligations. -/
theorem ChosenSmallSource.sigmaOutside_plane_of_wreath
    {T : Sylow 2 G} {M Mc V H B : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (ha : letI := h.prepared.elementary
      SmallActionAlternatives T M V h.prepared.normalized)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hquad : ∀ A ∈ delta H, ⁅⁅conjugateSpan H V,A⁆,A⁆ = ⊥)
    (hfix : ∀ A ∈ delta H,
      conjugateSpan H V ⊓ centralizer (A : Set G) =
        conjugateSpan H V ⊓ centralizer (A ⊓ twoCoreIn H : Subgroup G))
    (hB : B ∈ sigmaOutside (T : Subgroup G) H) :
    letI := h.prepared.elementary
    Representation.BinaryOffender.IsElementaryTwo (actor M V B h.prepared.normalized) ∧
      Representation.BinaryOffender.IsQuadratic (imageRepresentation M V h.prepared.normalized)
        (actor M V B h.prepared.normalized) ∧
      ⁅V,B⁆ ≤ V ∧ Nat.card (⁅V,B⁆ : Subgroup G) = 4 ∧
      (T : Subgroup G) ≤ normalizer (⁅V,B⁆ : Subgroup G) :=
  h.sigmaOutside_plane ha hH (h.wreath_intersections hH he).2 hquad hfix hB

end CFSG.Quasithin.Chapter15.Section02
