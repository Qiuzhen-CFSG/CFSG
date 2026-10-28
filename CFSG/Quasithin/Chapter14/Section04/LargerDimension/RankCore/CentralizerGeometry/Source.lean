module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.QuotientAction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.Relative
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.Symmetry
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry.Uniqueness
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Ambient consumers for the centralizer argument in 14.4.7

`EarlierGeometry` names the precise earlier 12.8/14.3 inputs, with the
literal H/O₂(H) action on U/Z(U). Its fields include neither a conclusion
about D nor the equality U=O₂(H). The extraspecial lift and the rank
obstruction give Q^g=U^gD, D≤Q, [D,U]≤V₁, and [D,W]=1. The symmetric
bounds are transported through the earlier natural-module point orbit.

The last part of the first paragraph remains conditional on the model
generation identity in the literal quotient of H^g. It lifts that identity
to K^g=[K^g,W] and applies uniqueness over LT^g to prove C_D(L)=1.
The source-model generation calculation is a separate remaining obligation;
this module does not assert that the entire source theorem is complete.

Source: Aschbacher--Smith, 14.4.7, printed pp.1008--1009. Earlier inputs:
12.8.4(4), 12.8.8(1), 12.8.9(5),(7), and the natural action in 14.3.16.
The parent source owner retains their discharge and the involution-rank
dichotomy; the subsequent Sylow/Gaschütz argument is separate.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
open Subgroup
open scoped commutatorElement
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]

theorem ambient_core_lift (H U : Subgroup G) (hUH : U ≤ H)
    [(U.subgroupOf H).Normal] [IsExtraspecial 2 (U.subgroupOf H)]
    (d : SourceAction H (U.subgroupOf H) V)
    (hHZ : H ≤ centralizer (Z U : Set G)) :
    H.pCoreIn 2 = U ⊔ (H ⊓ centralizer (U : Set G)) := by
  have hz (a : H) (z : U.subgroupOf H) (hz : z ∈ center (U.subgroupOf H)) :
      MulAut.conjNormal a z = z := by
    apply Subtype.ext
    apply Subtype.ext
    have hzG : ((z : H) : G) ∈ Z U := by
      rw [← center_subgroupOf_map H U hUH]
      exact mem_map_of_mem H.subtype (mem_map_of_mem _ hz)
    change (a : G) * ((z : H) : G) * (a : G)⁻¹ = ((z : H) : G)
    rw [← hHZ a.property _ hzG, mul_inv_cancel_right]
  unfold pCoreIn
  rw [d.core_eq_sup_centralizer hz, Subgroup.map_sup,
    map_subgroupOf_eq_of_le hUH, centralizer_subgroupOf_map H U hUH]

theorem conjugate_core_lift (H U : Subgroup G) (hUH : U ≤ H)
    [(U.subgroupOf H).Normal] [IsExtraspecial 2 (U.subgroupOf H)]
    (d : SourceAction H (U.subgroupOf H) V)
    (hHZ : H ≤ centralizer (Z U : Set G)) (g : G) :
    conjugate (H.pCoreIn 2) g = conjugate U g ⊔ D H U g := by
  rw [ambient_core_lift H U hUH d hHZ]
  simp only [conjugate, D, Subgroup.map_sup, map_inf _ _ (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective,
    centralizer_map]

omit [Finite G] in
theorem ambient_relative_centralizer_isTwoGroup (H U : Subgroup G) (hUH : U ≤ H)
    [(U.subgroupOf H).Normal] (d : SourceAction H (U.subgroupOf H) V) :
    IsPGroup 2 (H ⊓ centralizer (U : Set G) : Subgroup G) := by
  rw [← centralizer_subgroupOf_map H U hUH]
  exact (pCore_isPGroup.to_le d.centralizer_le_core).map H.subtype

variable [Module.Finite (ZMod 2) V]
theorem ambient_centralizes_quotient (H J U P A B V₂ : Subgroup G)
    (hUH : U ≤ H) [(U.subgroupOf H).Normal]
    (d : SourceAction H (U.subgroupOf H) V)
    (hH : H = centralizer (A : Set G)) (hJ : J = centralizer (B : Set G))
    (hA : A ≤ V₂) (hB : B ≤ V₂) (hVP : V₂ ≤ P)
    (hHU : H ≤ normalizer (U : Set G)) (hJP : J ≤ normalizer (P : Set G))
    (h12895 : QuotientKernel U P V₂)
    (hZP : Z P = B) (hZU : Z U = A)
    (hD : IsPGroup 2 (J ⊓ centralizer (P : Set G) : Subgroup G))
    (hW : Module.finrank (ZMod 2) (V ⧸ d.image ((W U V₂).subgroupOf H)) = 1)
    (hV₂ : Module.finrank (ZMod 2) (d.image (V₂.subgroupOf H)) = 1)
    (hrank : ∀ a : H ⧸ pCore 2 H, orderOf a = 2 →
      2 < d.movedRank a ∨ (d.movedRank a = 2 ∧ ¬ d.image (V₂.subgroupOf H) ≤ d.moved a)) :
    (J ⊓ centralizer (P : Set G)) ≤ H.pCoreIn 2 ∧
      ⁅J ⊓ centralizer (P : Set G), U⁆ ≤ A := by
  let C := J ⊓ centralizer (P : Set G)
  have hCH : C ≤ H := relative_centralizer_le H J P A V₂ hH hA hVP
  have hcomm : ⁅C, W U V₂⁆ ≤ V₂ := by
    have hh := relative_commutator_le_center H J U P A B V₂ hH hJ hA hB
      hVP hHU hJP h12895
    rw [hZP] at hh
    exact hh.trans hB
  have hcommH : ⁅C.subgroupOf H, (W U V₂).subgroupOf H⁆ ≤ V₂.subgroupOf H := by
    apply commutator_le.mpr
    intro a ha w hw
    exact hcomm (commutator_mem_commutator ha hw)
  have hcore : C.subgroupOf H ≤ pCore 2 H :=
    d.le_twoCore_of_hyperplane (U.subgroupOf H) (C.subgroupOf H)
      ((W U V₂).subgroupOf H) (V₂.subgroupOf H) hD.comap_subtype hW hV₂
      (d.image_displacement_le _ _ _ hcommH) hrank
  have hCA : ⁅C, U⁆ ≤ A := by
    have hh := map_mono (f := H.subtype) (d.commutator_le_center (C.subgroupOf H) hcore)
    rw [map_commutator, map_subgroupOf_eq_of_le hCH, map_subgroupOf_eq_of_le hUH] at hh
    change ⁅C, U⁆ ≤ (Z (U.subgroupOf H)).map H.subtype at hh
    rwa [center_subgroupOf_map H U hUH, hZU] at hh
  refine ⟨?_, hCA⟩
  have hh := map_mono (f := H.subtype) hcore
  rwa [map_subgroupOf_eq_of_le hCH] at hh

theorem ambient_commutator_eq_bot (H J U P A B V₂ : Subgroup G)
    (hUH : U ≤ H) [(U.subgroupOf H).Normal]
    (d : SourceAction H (U.subgroupOf H) V)
    (hH : H = centralizer (A : Set G)) (hJ : J = centralizer (B : Set G))
    (hA : A ≤ V₂) (hB : B ≤ V₂) (hVP : V₂ ≤ P)
    (hHU : H ≤ normalizer (U : Set G)) (hJP : J ≤ normalizer (P : Set G))
    (h12895 : QuotientKernel U P V₂)
    (hZP : Z P = B) (hZU : Z U = A) (hAB : A ⊓ B = ⊥)
    (hD : IsPGroup 2 (J ⊓ centralizer (P : Set G) : Subgroup G))
    (hW : Module.finrank (ZMod 2) (V ⧸ d.image ((W U V₂).subgroupOf H)) = 1)
    (hV₂ : Module.finrank (ZMod 2) (d.image (V₂.subgroupOf H)) = 1)
    (hrank : ∀ a : H ⧸ pCore 2 H, orderOf a = 2 →
      2 < d.movedRank a ∨ (d.movedRank a = 2 ∧ ¬ d.image (V₂.subgroupOf H) ≤ d.moved a)) :
    ⁅J ⊓ centralizer (P : Set G), W U V₂⁆ = ⊥ := by
  have hCA := (ambient_centralizes_quotient H J U P A B V₂ hUH d hH hJ hA hB hVP
    hHU hJP h12895 hZP hZU hD hW hV₂ hrank).2
  have hCB := relative_commutator_le_center H J U P A B V₂ hH hJ hA hB hVP hHU hJP h12895
  rw [hZP] at hCB
  apply le_bot_iff.mp
  rw [← hAB]
  exact le_inf ((commutator_mono le_rfl inf_le_left).trans hCA) hCB
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
open Subgroup
variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Earlier source data from Hypothesis 14.3.10, 12.8.4(4), 12.8.8(1), and
12.8.9(5),(7). The action, hyperplane and line are the literal quotient markings.
No conclusion about D or equality of U with the two-core is a field. -/
structure EarlierGeometry (H U A V₂ L : Subgroup G) (g : G)
    [(U.subgroupOf H).Normal] where
  U_le_H : U ≤ H
  H_eq_centralizer : H = centralizer (A : Set G)
  center_eq : Z U = A
  V₂_le_U : V₂ ≤ U
  A_le_V₂ : A ≤ V₂
  g_normalizes : g ∈ normalizer (V₂ : Set G)
  g_mem_L : g ∈ L
  g_not_mem_H : g ∉ H
  disjoint : A ⊓ conjugate A g = ⊥
  quotient_kernel : QuotientKernel U (conjugate U g) V₂
  action : SourceAction H (U.subgroupOf H) V
  hyperplane : Module.finrank (ZMod 2) (V ⧸ action.image ((W U V₂).subgroupOf H)) = 1
  line : Module.finrank (ZMod 2) (action.image (V₂.subgroupOf H)) = 1

variable {H U A V₂ L : Subgroup G} {g : G} [(U.subgroupOf H).Normal]

theorem EarlierGeometry.normalizes (d : EarlierGeometry (V := V) H U A V₂ L g) :
    H ≤ normalizer (U : Set G) :=
  (normal_subgroupOf_iff_le_normalizer d.U_le_H).mp inferInstance

theorem EarlierGeometry.plane_le_conjugate (d : EarlierGeometry (V := V) H U A V₂ L g) :
    V₂ ≤ conjugate U g := by
  have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) d.V₂_le_U
  change conjugate V₂ g ≤ conjugate U g at h
  rwa [conjugate_eq_self V₂ d.g_normalizes] at h

theorem EarlierGeometry.conjugate_line_le_plane (d : EarlierGeometry (V := V) H U A V₂ L g) :
    conjugate A g ≤ V₂ := by
  have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) d.A_le_V₂
  change conjugate A g ≤ conjugate V₂ g at h
  rwa [conjugate_eq_self V₂ d.g_normalizes] at h

theorem EarlierGeometry.D_isTwoGroup (d : EarlierGeometry (V := V) H U A V₂ L g) :
    IsPGroup 2 (D H U g) := by
  have hp := (ambient_relative_centralizer_isTwoGroup H U d.U_le_H d.action).map
    (MulAut.conj g⁻¹).toMonoidHom
  have he : (H ⊓ centralizer (U : Set G)).map (MulAut.conj g⁻¹).toMonoidHom = D H U g := by
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective, centralizer_map]
    rfl
  exact he ▸ hp

variable [Finite G]

theorem EarlierGeometry.core_lift [IsExtraspecial 2 U]
    (d : EarlierGeometry (V := V) H U A V₂ L g) :
    conjugate (H.pCoreIn 2) g = conjugate U g ⊔ D H U g := by
  let _ : IsExtraspecial 2 (U.subgroupOf H) :=
    IsExtraspecial.of_mulEquiv (subgroupOfEquivOfLe d.U_le_H).symm inferInstance
  apply conjugate_core_lift H U d.U_le_H d.action _ g
  rw [d.center_eq, ← d.H_eq_centralizer]

variable [Module.Finite (ZMod 2) V]

theorem EarlierGeometry.centralizer_bounds (d : EarlierGeometry (V := V) H U A V₂ L g)
    (hrank : ∀ a : H ⧸ pCore 2 H, orderOf a = 2 →
      2 < d.action.movedRank a ∨ (d.action.movedRank a = 2 ∧
        ¬ d.action.image (V₂.subgroupOf H) ≤ d.action.moved a)) :
    D H U g ≤ H.pCoreIn 2 ∧ ⁅D H U g, U⁆ ≤ A ∧ ⁅D H U g, W U V₂⁆ = ⊥ := by
  have hJ : conjugate H g = centralizer (conjugate A g : Set G) := by
    rw [d.H_eq_centralizer, conjugate_centralizer]
  have hZ : Z (conjugate U g) = conjugate A g := by
    rw [← conjugate_center, d.center_eq]
  have hbounds := ambient_centralizes_quotient H (conjugate H g) U (conjugate U g)
    A (conjugate A g) V₂ d.U_le_H d.action d.H_eq_centralizer hJ d.A_le_V₂
    d.conjugate_line_le_plane d.plane_le_conjugate d.normalizes
    (conjugate_normalizes H U g d.normalizes) d.quotient_kernel hZ d.center_eq
    d.D_isTwoGroup d.hyperplane d.line hrank
  refine ⟨hbounds.1, hbounds.2, ?_⟩
  exact ambient_commutator_eq_bot H (conjugate H g) U (conjugate U g)
    A (conjugate A g) V₂ d.U_le_H d.action d.H_eq_centralizer hJ d.A_le_V₂
    d.conjugate_line_le_plane d.plane_le_conjugate d.normalizes
    (conjugate_normalizes H U g d.normalizes) d.quotient_kernel hZ d.center_eq
    d.disjoint d.D_isTwoGroup d.hyperplane d.line hrank
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Lifting the literal star generation kills the two-group quotient of the
commutator subgroup by two-perfectness. -/
theorem ambient_residual_generation (J W : Subgroup G) (hWJ : W ≤ J)
    (hstar : (pResidual 2 J).map (QuotientGroup.mk' (pCore 2 J)) =
      ⁅(pResidual 2 J).map (QuotientGroup.mk' (pCore 2 J)),
        (W.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))⁆) :
    (pResidual 2 J).map J.subtype = ⁅(pResidual 2 J).map J.subtype, W⁆ := by
  have hh := congrArg (fun N : Subgroup J => N.map J.subtype)
    (pResidual_eq_commutator_of_quotient (W.subgroupOf J) hstar)
  rwa [map_commutator, map_subgroupOf_eq_of_le hWJ] at hh

/-- The residual transported by right conjugation is the residual of Hᵍ. -/
theorem conjugate_residual (H : Subgroup G) (g : G) :
    conjugate ((pResidual 2 H).map H.subtype) g =
      (pResidual 2 (conjugate H g)).map (conjugate H g).subtype :=
  map_embedded_pResidual 2 H (MulAut.conj g⁻¹).toMonoidHom

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
variable {H U A V₂ L : Subgroup G} {g : G} [(U.subgroupOf H).Normal]

/-- Consumer of the model-generation branch. Uniqueness is used through the
normalizer of the actual two-subgroup C_D(L), not an intersection assumption. -/
theorem EarlierGeometry.centralizer_eq_bot_of_star_generation
    (d : EarlierGeometry (V := V) H U A V₂ L g)
    (hrank : ∀ a : H ⧸ pCore 2 H, orderOf a = 2 →
      2 < d.action.movedRank a ∨ (d.action.movedRank a = 2 ∧
        ¬ d.action.image (V₂.subgroupOf H) ≤ d.action.moved a))
    (T M : Subgroup G) (hTH : T ≤ H) (hTL : T ≤ normalizer (L : Set G))
    (hstar : (pResidual 2 (conjugate H g)).map (QuotientGroup.mk' (pCore 2 (conjugate H g))) =
      ⁅(pResidual 2 (conjugate H g)).map (QuotientGroup.mk' (pCore 2 (conjugate H g))),
        ((W U V₂).subgroupOf (conjugate H g)).map
          (QuotientGroup.mk' (pCore 2 (conjugate H g)))⁆)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ conjugate T g ≤ N → N = M)
    (hKM : ¬ conjugate ((pResidual 2 H).map H.subtype) g ≤ M) :
    conjugate ((pResidual 2 H).map H.subtype) g ≤ centralizer (D H U g : Set G) ∧
      D H U g ⊓ centralizer (L : Set G) = ⊥ := by
  have hJD : conjugate H g ≤ normalizer (D H U g : Set G) :=
    relative_centralizer_normalized _ _ (conjugate_normalizes H U g d.normalizes)
  have hWJ : W U V₂ ≤ conjugate H g := by
    rw [d.H_eq_centralizer, conjugate_centralizer]
    exact inf_le_right.trans (centralizer_le d.conjugate_line_le_plane)
  have hgen := ambient_residual_generation (conjugate H g) (W U V₂) hWJ hstar
  have hDW := (d.centralizer_bounds hrank).2.2
  have hKC : (pResidual 2 (conjugate H g)).map (conjugate H g).subtype ≤
      centralizer (D H U g : Set G) := by
    rw [hgen]
    exact commutator_centralizes_of_normalizes _ _ _ ((map_subtype_le _).trans hJD) hDW
  have hTgL : conjugate T g ≤ normalizer (L : Set G) := by
    have hh := conjugate_normalizes T L g hTL
    rwa [conjugate_eq_self L (L.le_normalizer d.g_mem_L)] at hh
  rw [conjugate_residual] at hKM ⊢
  refine ⟨hKC, ?_⟩
  exact relative_centralizer_eq_bot_of_unique _ _ L (conjugate T g) M d.D_isTwoGroup hKC
    ((map_mono hTH).trans hJD) hTgL hunique hKM
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
open Subgroup
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {H U A V₂ L : Subgroup G} {g : G} [(U.subgroupOf H).Normal] [IsExtraspecial 2 U]

omit [Finite G] [Module.Finite (ZMod 2) V] in
theorem EarlierGeometry.H_eq_normalizer (d : EarlierGeometry (V := V) H U A V₂ L g) :
    H = normalizer (A : Set G) := by
  have hcard : Nat.card A = 2 := by
    rw [← d.center_eq]
    exact (Nat.card_congr ((center U).equivMapOfInjective U.subtype U.subtype_injective).toEquiv).symm.trans
      (IsExtraspecial.center_order_p 2 U)
  rw [d.H_eq_centralizer]
  exact le_antisymm (centralizer_le_normalizer _) (normalizer_le_centralizer_of_card_two A hcard)

/-- The symmetric bounds consumed by the complement argument. The only
symmetry input is the point-stabilizer orbit from the earlier natural
L₃(2)-action on V; the centralizer and commutator conclusions are proved. -/
theorem EarlierGeometry.symmetric_bounds (d : EarlierGeometry (V := V) H U A V₂ L g)
    (hrank : ∀ a : H ⧸ pCore 2 H, orderOf a = 2 →
      2 < d.action.movedRank a ∨ (d.action.movedRank a = 2 ∧
        ¬ d.action.image (V₂.subgroupOf H) ≤ d.action.moved a))
    (V₀ : Subgroup G) (hAV : A ≤ V₀) (hLV : L ≤ normalizer (V₀ : Set G))
    (hpoints : ∀ x ∈ L, conjugate A x = conjugate A g ∨
      ∃ t ∈ conjugate H g, conjugate A x = conjugate A t) :
    ∀ x ∈ L, ⁅D H U g, conjugate U x⁆ ≤ conjugate A x ∧ conjugate A x ≤ V₀ :=
  symmetric_commutator_bounds H U A L V₀ g d.H_eq_normalizer d.normalizes hAV hLV hpoints
    (d.centralizer_bounds hrank).2.1
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.CentralizerGeometry
