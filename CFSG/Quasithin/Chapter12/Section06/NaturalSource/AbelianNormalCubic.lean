module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalLinearTwo
public import Theory.GroupTheory.RankOneCentralizingCubic
public import Theory.GroupTheory.PResidual.FiniteImage
/-!
# The actual centralizing cubic in the normal PSL₂ branch

The intrinsic two-core quotient of the original L₁-star is E₉, through
the same quotient projection H → H/O₂(H). Its normal centralizer on the
component therefore embeds in E₉: its two-core lies in O₂(H-star)=1.
The centerless component has three-rank one, so the ambient rank-two
bound makes that nontrivial elementary centralizer have order three.

The source LC=O²(C_L₁(K-star)) maps onto exactly this subgroup. Odd-order
averaging and the previously established full movement give no fixed
vectors on the entire original U_H/V₁. All earlier point, Sylow, TI,
intersection and nonsingular-centralizer inputs remain explicit.

Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
The normal Borel, field restrictions and universal natural reduction
remain obligations of the source assembly.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {catalog : GroupClass} {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis catalog T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)

include hz hTz hH in
/-- The intrinsic core quotient of the original residual image is E₉.
The comparison retains both the original E₉ map and H's quotient projection. -/
theorem SourceHypothesis.original_point_star_core_quotient :
    ∃ (g : (D.fullSetup hZ T z).L₁ →*
        BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9),
      Function.Surjective g ∧ g.ker = pCore 2 (D.fullSetup hZ T z).L₁ ∧
      ∃ e : (actorImage H (D.fullSetup hZ T z).L₁ ⧸
        pCore 2 (actorImage H (D.fullSetup hZ T z).L₁)) ≃*
        BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9,
      ∀ (x : (D.fullSetup hZ T z).L₁),
        e (QuotientGroup.mk' _ ⟨QuotientGroup.mk' (pCore 2 H)
          ⟨x.val,hH.1.2 (Or.inl x.property)⟩,
          mem_map_of_mem _ x.property⟩) = g x := by
  let E := D.fullSetup hZ T z
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  let c := subgroupOfEquivOfLe hLH
  let q := QuotientGroup.mk' (pCore 2 H)
  let f : E.L₁ →* actorImage H E.L₁ :=
    (q.subgroupMap (E.L₁.subgroupOf H)).comp c.symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp c.symm.surjective
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 H).comap (inclusion hLH) := by
      ext x
      change f x = 1 ↔ inclusion hLH x ∈ pCore 2 H
      rw [←QuotientGroup.eq_one_iff]
      exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
    rw [he]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hLH)
  obtain ⟨g,hg,hgk,e9,he9,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
  let d := f.quotientPCoreEquivOfSurjective hf hk
  refine ⟨g,hg,hgk,d.symm.trans e9,?_⟩
  intro x
  change e9 (d.symm (QuotientGroup.mk' _ (f x))) = g x
  rw [←MonoidHom.quotientPCoreEquivOfSurjective_mk f hf hk,d.symm_apply_apply]
  exact he9 x
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
open Representation Representation.BinaryOffender
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
/-- The actual normal centralizer in L₁-star is a cubic subgroup. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_centralizer_card
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    let C := actorImage H (D.fullSetup hZ T z).L₁ ⊓
      centralizer (actorImage H K : Set (H ⧸ pCore 2 H))
    C.Normal ∧ IsElementaryAbelian 3 C ∧ Nat.card C = 3 := by
  let A := actorImage H (D.fullSetup hZ T z).L₁
  let C := A ⊓ centralizer (actorImage H K : Set (H ⧸ pCore 2 H))
  have hnormal : C.Normal := by
    have hh := S.original_abelian_residual_centralizer_normal D hZ z hz hTV hH hKH hK hgen
    rwa [conjugateSpan_eq_of_normal H K T hKH (fun x hx => hH.1.2 (Or.inr hx)) hn] at hh
  let _ := hnormal
  obtain ⟨_,_,_,d,_⟩ := S.original_point_star_core_quotient D hZ z hz hTz hH
  let : IsElementaryAbelian 3 (A ⧸ pCore 2 A) :=
    IsElementaryAbelian.of_injective d.toMonoidHom d.injective
  let : IsElementaryAbelian 3 C := normal_elementary_of_core_quotient A C
    (pCore_quotient_pCore_eq_bot 2) inf_le_left
  obtain ⟨F,hF,hfin,hcardF,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardF)
  let e : actorImage H K ≃* SL(2,F) :=
    (componentStarEquiv H K hKH hK).symm.trans
      (eK.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)
  have hzK : center (actorImage H K) = ⊥ := by
    apply bot_unique
    intro x hx
    have hc : center SL(2,F) = ⊥ := BenderSuzuki.Converse.center_SL2_eq_bot
    have he : e x = 1 := mem_bot.mp (hc.le ((centerCongr e) ⟨x,hx⟩).property)
    exact mem_bot.mpr (e.map_eq_one_iff.mp he)
  have hr : primeRank 3 (actorImage H K) = 1 := by
    rw [primeRank_equiv 3 e]
    exact Matrix.SL2.binary_threeRank_eq_one (F := F)
  refine ⟨hnormal,inferInstance,centralizing_elementary_card_prime (actorImage H K) C hzK hr
    (S.original_star_three_rank D hZ z hz hH) inf_le_right ?_⟩
  exact S.original_abelian_normal_linearTwo_centralizer_ne_bot D hZ z hz hTz hH hn hKH hK
    hn2 ⟨F,hF,hfin,hcardF,⟨eK⟩⟩
include hz hTV hTz hH hKH hK hgen in
/-- The source LC = O²(C_L₁(K-star)) maps onto exactly this cubic.
The centralizer is taken through the literal H/O₂(H) quotient. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_centralizing_residual
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    let q := QuotientGroup.mk' (pCore 2 H)
    let X := ((D.fullSetup hZ T z).L₁.subgroupOf H) ⊓
      (centralizer (actorImage H K : Set (H ⧸ pCore 2 H))).comap q
    let LC := ((pResidual 2 X).map X.subtype).map H.subtype
    LC ≤ (D.fullSetup hZ T z).L₁ ∧ IsPPerfect 2 LC ∧
      actorImage H LC = actorImage H (D.fullSetup hZ T z).L₁ ⊓
        centralizer (actorImage H K : Set (H ⧸ pCore 2 H)) ∧
      Nat.card (actorImage H LC) = 3 := by
  dsimp only
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := actorImage H (D.fullSetup hZ T z).L₁
  let C := A ⊓ centralizer (actorImage H K : Set (H ⧸ pCore 2 H))
  let X := ((D.fullSetup hZ T z).L₁.subgroupOf H) ⊓
    (centralizer (actorImage H K : Set (H ⧸ pCore 2 H))).comap q
  let Y := (pResidual 2 X).map X.subtype
  have hX : X.map q = C := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨mem_map_of_mem q hx.1,hx.2⟩
    · rintro x ⟨⟨y,hy,rfl⟩,hc⟩
      exact ⟨y,⟨hy,hc⟩,rfl⟩
  obtain ⟨_,_,hc⟩ := S.original_abelian_normal_linearTwo_centralizer_card
    D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
  have hres : pResidual 2 C = ⊤ := by
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right
      (hc ▸ _root_.orderOf_dvd_natCard x))
  have hstar : actorImage H (Y.map H.subtype) = C := by
    change ((Y.map H.subtype).comap H.subtype).map q = C
    rw [comap_map_eq_self_of_injective H.subtype_injective]
    change ((pResidual 2 X).map X.subtype).map q = C
    rw [map_embedded_pResidual,hX,hres,←MonoidHom.range_eq_map,range_subtype]
  refine ⟨?_,(isPPerfect_embedded_pResidual 2 X).of_surjective
    (H.subtype.subgroupMap Y) (H.subtype.subgroupMap_surjective Y),hstar,?_⟩
  · rintro _ ⟨y,⟨x,_,rfl⟩,rfl⟩
    exact x.property.1
  · rw [hstar]
    exact hc

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The constructed cubic acts without fixed vectors on the entire
original U_H/V₁ section, with the same literal quotient action. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_fixed_free_cubic
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    let C := actorImage H (D.fullSetup hZ T z).L₁ ⊓
      centralizer (actorImage H K : Set (H ⧸ pCore 2 H))
    C.Normal ∧ Nat.card C = 3 ∧
      ∃ hU : IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H),
        let _ := hU
        ∃ a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁,
          subspaceCommutator a.representation ⊤ C = ⊤ ∧
          fixedSpace a.representation C = ⊥ := by
  let C := actorImage H (D.fullSetup hZ T z).L₁ ⊓
    centralizer (actorImage H K : Set (H ⧸ pCore 2 H))
  obtain ⟨_,_,hc⟩ := S.original_abelian_normal_linearTwo_centralizer_card
    D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
  obtain ⟨hnC,_,hU,a,ha⟩ := S.original_abelian_normal_linearTwo_moving_centralizer
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hn2 hm
  let _ := hU
  have hsplit : IsCompl (fixedSpace a.representation C)
      (subspaceCommutator a.representation ⊤ C) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := a.representation) (Y := C)
        (by rw [hc]; decide))
  refine ⟨hnC,hc,hU,a,ha,?_⟩
  have hd := hsplit.disjoint
  rw [ha] at hd
  exact disjoint_top.mp hd

end CFSG.Quasithin.Chapter12.Section06
