module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Factors
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedThompsonChiefActions
public import CFSG.Quasithin.Chapter15.Section01.MinimalParabolicSource
public import Theory.GroupTheory.WreathTwoCoreQuotient

/-!
# The actual Thompson image in the original wreath quotient

Choose a noncentral chief factor of the original normal closure of V.
Its action kernel is O₂(H): maximality of the wreath Sylow forces the
kernel into that Sylow, and irreducibility gives the reverse core inclusion.
The matched chief-action classification therefore identifies the image of
J(H) in the literal H/O₂(H) with S₃ × S₃. Cardinalities distinguish the
four source rows. The final transport uses the original quotient map.

This supplies the distinguished paired layer used in15.2.21(1), without
identifying an arbitrary pair of cubic lines with the source factors.
The KS quotient application is in PairedQuotient.

Source: Aschbacher--Smith15.1.12(3), Notation15.2.9 and15.2.21(1),
printed pp.1090,1110,1114; refs/quasithin.pdf.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original global Thompson subgroup has the paired image in H/O₂(H). -/
theorem thompson_core_image_pair :
    Nonempty (((elementaryAbelianMaxJ (⊤ : Subgroup H)).map
      (QuotientGroup.mk' (pCore 2 H))) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let h := hsource.prepared
  let := h.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((h.inside_core H d.geometry.outside).trans (twoCore_le H)))
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hcount := (h.chief_data hsource.ambient T hsource.empty hsource.maximal hsource.centralizing H d.geometry.outside).2 s
  obtain ⟨i,j,hij,hi,hj⟩ := s.one_lt_noncentralCount_iff.mp (by omega)
  let := s.factorRepresentation_irreducible i
  let q := Representation.BinaryOffender.actionHom (G := H) (V := Additive (s.Factor i))
    (s.factorRepresentation i)
  have hq : Function.Surjective q := (s.factorRepresentation i).asGroupHom.rangeRestrict_surjective
  have hn : q.ker ≠ ⊤ := by
    intro hn
    apply hi
    rw [s.central_iff_action]
    intro g x
    have hg : q g = 1 := by
      change g ∈ q.ker
      rw [hn]
      exact mem_top g
    exact congrArg Additive.toMul ((actionHom_eq_one_iff _ g).mp hg (Additive.ofMul x))
  let S := T.subtype d.geometry.outside.1.1.2
  have hp := (source_centralizing_minimalParabolic hsource.ambient T hsource.maximal
    hsource.centralizing H d.geometry.outside).2.1
  have hred := (ChapterB.minimalParabolic_reduced_image S hp q hq
    (irreducible_image_twoCore_eq_bot (s.factorRepresentation i)) hn).2
  have hkerS : q.ker ≤ (S : Subgroup H) := by
    have hc := WreathTwoResidual.sylow_isCoatom_of_core_quotient S
      (d.geometry.quotient.some.trans ChosenGeometry.matrixWreathEquiv)
    rcases hc.le_iff.mp (le_sup_left : (S : Subgroup H) ≤ (S : Subgroup H) ⊔ q.ker) with he | he
    · have hm := congrArg (Subgroup.map q) he
      have hz : q.ker.map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
      rw [Subgroup.map_sup,hz,sup_bot_eq,map_top_of_surjective _ hq] at hm
      exact (((ChapterB.isMinimalParabolicOver_top_iff _).mp hred).2 (by
        change ((S : Subgroup H).map q).Normal
        rw [hm]
        infer_instance)).elim
    · exact le_sup_right.trans he.le
  have hk : q.ker = pCore 2 H := le_antisymm
    (le_sSup ⟨inferInstance,S.isPGroup'.to_le hkerS⟩) (by
      change pCore 2 H ≤ (Representation.BinaryOffender.actionHom (s.factorRepresentation i)).ker
      rw [actionHom_ker_eq]
      exact normal_p_subgroup_le_ker (s.factorRepresentation i) _ pCore_isPGroup)
  have ht := h.chief_thompson_actor_layer_types hsource.ambient T hsource.empty
    hsource.maximal hsource.centralizing d.geometry.outside s i hi
  have hc : Nat.card (H ⧸ q.ker) = 72 := by
    rw [hk,Nat.card_congr d.geometry.quotient.some.toEquiv,RegularWreathProduct.card]
    norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  obtain ⟨a⟩ : Nonempty ((elementaryAbelianMaxJ (⊤ : Subgroup H)).map q ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
    rcases ht with ⟨⟨a⟩,_⟩ | ⟨_,ha⟩ | ⟨⟨a⟩,_⟩ | ⟨⟨a⟩,_⟩
    · have hh := Nat.card_congr a.toEquiv
      rw [hc] at hh
      norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
    · exact ha
    · have hh := Nat.card_congr a.toEquiv
      rw [hc] at hh
      norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
    · have hh := Nat.card_congr a.toEquiv
      rw [hc,RegularWreathProduct.card] at hh
      norm_num [Nat.card_perm,Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hh
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have he : e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H)) = q := by
    ext x
    rfl
  let J := (elementaryAbelianMaxJ (⊤ : Subgroup H)).map (QuotientGroup.mk' (pCore 2 H))
  have hmap : J.map e.toMonoidHom = (elementaryAbelianMaxJ (⊤ : Subgroup H)).map q := by
    rw [map_map,he]
  exact ⟨(e.subgroupMap J).trans ((MulEquiv.subgroupCongr hmap).trans a)⟩

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
