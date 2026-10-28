module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalCubic
public import Theory.GroupTheory.RankOneInnerSplitting
/-!
# The original point residual over a rank-one normal component

The original Sylow E₉ survives the full O₂(H) quotient. Inner action on a
centerless component of three-rank one therefore has nontrivial kernel.
Relative component normality makes this centralizer normal in H-star;
its intrinsic two-core vanishes, so the ambient rank bound makes it cubic.
The inner-supplement splitting then gives multiplication of the actual
component and centralizing intersections, preserving both inclusions.

AbelianNormalUnitaryEven supplies the model premises for the original
normal even-degree PSU₃ row. No field-size or final natural-module conclusion
is assumed. Source: Aschbacher--Smith 12.6.31, printed p.836,
refs/quasithin.pdf.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hH hKH hK hgen in
/-- A centerless rank-one component with abelian outer group splits the
original residual image, with a normal elementary cubic as its second factor. -/
theorem SourceHypothesis.original_normal_rankOne_point_split
    (hn : (K.subgroupOf H).Normal)
    [IsMulCommutative (MulAut.Outer (actorImage H K))]
    (hzB : center (actorImage H K) = ⊥)
    (hr : primeRank 3 (actorImage H K) = 1) :
    let A := actorImage H (D.fullSetup hZ T z).L₁
    let B := actorImage H K
    let C := A ⊓ centralizer (B : Set (H ⧸ pCore 2 H))
    C.Normal ∧ IsElementaryAbelian 3 C ∧ Nat.card C = 3 ∧
      A = (A ⊓ B) ⊔ C ∧
      ∃ e : (A ⊓ B : Subgroup (H ⧸ pCore 2 H)) × C ≃* A,
        ∀ b c, (e (b,c) : H ⧸ pCore 2 H) = (b : H ⧸ pCore 2 H) * c := by
  let E := D.fullSetup hZ T z
  let A := actorImage H E.L₁
  let B := actorImage H K
  let C := A ⊓ centralizer (B : Set (H ⧸ pCore 2 H))
  let q := QuotientGroup.mk' (pCore 2 H)
  let : B.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hTA : actorImage H T ≤ normalizer (A : Set (H ⧸ pCore 2 H)) := by
    have ht : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
      (le_inf hTH hTV).trans (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
    rintro _ ⟨x,hx,rfl⟩
    apply (E.L₁.subgroupOf H).le_normalizer_map q
    apply mem_map_of_mem
    rw [←subgroupOf_normalizer_eq hLH]
    exact ht hx
  have hstar : B ⊔ A ⊔ actorImage H T = ⊤ := by
    have hg := hgen
    rw [conjugateSpan_eq_of_normal H K T hKH hTH hn] at hg
    unfold B A actorImage
    rw [←Subgroup.map_sup,←Subgroup.map_sup,←subgroupOf_sup hKH hLH,
      ←subgroupOf_sup (sup_le hKH hLH) hTH,hg,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  obtain ⟨_,_,_,d,_⟩ := S.original_point_star_core_quotient D hZ z hz hTz hH
  let : IsElementaryAbelian 3 (A ⧸ pCore 2 A) :=
    IsElementaryAbelian.of_injective d.toMonoidHom d.injective
  have hinner := S.original_point_residual_inner_of_outer_abelian D hZ z hz hTz hH hn
  have hnC : C.Normal := by
    have hh := S.original_abelian_residual_centralizer_normal D hZ z hz hTV hH hKH hK hgen
    rwa [conjugateSpan_eq_of_normal H K T hKH hTH hn] at hh
  let _ := hnC
  let : IsElementaryAbelian 3 C := normal_elementary_of_core_quotient A C
    (pCore_quotient_pCore_eq_bot 2) inf_le_left
  let P : Sylow 3 E.L₁ := Classical.choice inferInstance
  let P₀ := (P : Subgroup E.L₁).map E.L₁.subtype
  obtain ⟨hP,hPc,_⟩ := S.original_point_sylow_star D hZ z hz hTz hH P
  let : IsElementaryAbelian 3 (actorImage H P₀) := hP
  have hPA : actorImage H P₀ ≤ A := map_mono (comap_mono (map_subtype_le _))
  have hne : C ≠ ⊥ := by
    have hh := elementary_plane_inner_centralizer_ne_bot (actorImage H P₀) B hPc hzB hr.le
      (hPA.trans hinner)
    intro hC
    exact hh (bot_unique ((inf_le_inf_right _ hPA).trans hC.le))
  have hC : Nat.card C = 3 := centralizing_elementary_card_prime B C hzB hr
    (S.original_star_three_rank D hZ z hz hH) inf_le_right hne
  have hs : A = (A ⊓ B) ⊔ C := split_inner_supplement_of_elementary_core_quotient A B (actorImage H T)
    (pCore_quotient_pCore_eq_bot 2) hzB hr (S.original_star_three_rank D hZ z hz hH)
    hinner
    hTA hstar
    hne
  have hd : Disjoint (A ⊓ B) C := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hc : (⟨x,hx.1.2⟩ : B) ∈ center B := by
      rw [mem_center_iff]
      intro b
      exact Subtype.ext (hx.2.2 b b.property)
    exact mem_bot.mpr (congrArg (fun b : B => b.val)
      (show (⟨x,hx.1.2⟩ : B) = 1 from mem_bot.mp (hzB ▸ hc)))
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting (A ⊓ B) C hd
    (inf_le_right.trans (le_centralizer_iff.mp (show C ≤ centralizer (B : Set _) from inf_le_right)))
  exact ⟨hnC,inferInstance,hC,hs,e.trans (MulEquiv.subgroupCongr hs.symm),he⟩

end CFSG.Quasithin.Chapter12.Section06
