module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.NormalRankOnePoint
public import Theory.SpecificGroups.SU3.EvenRankOne
/-!
# Splitting the original residual over an even-degree PSU₃ component

Cyclic outer automorphisms kill the outer action of the original
L₁=[L₁,T intersect L]. The genuine unitary model is centerless with
three-rank one. Its original surviving Sylow E₉ therefore supplies a
normal cubic centralizer, and multiplication splits L₁-star into its
component and centralizing intersections. Both inclusions are retained.

The source LC=O²(C_L₁(K-star)) maps onto this same cubic through the
literal H/O₂(H) projection. On the full original U_H/V₁ it has no fixed
vectors, using the earlier point geometry and the original quotient action.
The even field degree is a branch condition, not a conclusion for all
unitary rows. Odd-degree unitary exclusions, field-size restrictions and
universal NaturalReduction remain with the source assembly.

Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
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
/-- The actual even-degree unitary branch has a cubic centralizer and
splits by multiplication of the original subgroup inclusions. -/
theorem SourceHypothesis.original_abelian_normal_unitaryEven_split
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n) (heven : Even n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) :
    let A := actorImage H (D.fullSetup hZ T z).L₁
    let B := actorImage H K
    let C := A ⊓ centralizer (B : Set (H ⧸ pCore 2 H))
    C.Normal ∧ IsElementaryAbelian 3 C ∧ Nat.card C = 3 ∧
      A = (A ⊓ B) ⊔ C ∧
      ∃ e : (A ⊓ B : Subgroup (H ⧸ pCore 2 H)) × C ≃* A,
        ∀ b c, (e (b,c) : H ⧸ pCore 2 H) = (b : H ⧸ pCore 2 H) * c := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let e := (componentStarEquiv H K hKH hK).symm.trans eK
  obtain ⟨hzJ,hrJ,houter⟩ :=
    BenderSuzuki.MatrixGroups.HermitianForm.BinaryCubicRankParity.even_rank_one_outer
      J hn2 heven hcard hconj
  let _ := houter
  let : IsCyclic (MulAut.Outer (actorImage H K)) := (MulAut.outerCongr e).isCyclic.mpr houter
  have hzB : center (actorImage H K) = ⊥ := by
    apply bot_unique
    intro x hx
    exact mem_bot.mpr (e.map_eq_one_iff.mp
      (mem_bot.mp (hzJ ▸ ((centerCongr e) ⟨x,hx⟩).property)))
  have hr : primeRank 3 (actorImage H K) = 1 := (primeRank_equiv 3 e).trans hrJ
  exact S.original_normal_rankOne_point_split D hZ z hz hTV hTz hH hKH hK hgen hn hzB hr

include hz hTV hTz hH hKH hK hgen in
/-- The component factor of the same split has order divisible by three. -/
theorem SourceHypothesis.original_abelian_normal_unitaryEven_component_cubic
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n) (heven : Even n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) :
    3 ∣ Nat.card (actorImage H (D.fullSetup hZ T z).L₁ ⊓ actorImage H K :
      Subgroup (H ⧸ pCore 2 H)) := by
  obtain ⟨_,_,hC,_,e,_⟩ := S.original_abelian_normal_unitaryEven_split
    D hZ z hz hTV hTz hH hKH hK hgen hn hn2 heven hm
  let E := D.fullSetup hZ T z
  let P : Sylow 3 E.L₁ := Classical.choice inferInstance
  let P₀ := (P : Subgroup E.L₁).map E.L₁.subtype
  have h9 : 9 ∣ Nat.card (actorImage H E.L₁) := by
    have hh := card_dvd_of_le (map_mono (comap_mono (map_subtype_le (P : Subgroup E.L₁))) :
      actorImage H P₀ ≤ actorImage H E.L₁)
    change Nat.card (actorImage H P₀) ∣ Nat.card (actorImage H E.L₁) at hh
    have hp := (S.original_point_sylow_star D hZ z hz hTz hH P).2.1
    change Nat.card (actorImage H P₀) = 9 at hp
    rwa [hp] at hh
  rw [←Nat.card_congr e.toEquiv,Nat.card_prod,hC] at h9
  exact (mul_dvd_mul_iff_right (by decide : (3 : ℕ) ≠ 0)).mp h9

include hz hTV hTz hH hKH hK hgen in
/-- The source LC = O²(C_L₁(K-star)) maps onto exactly this cubic.
The centralizer is taken through the literal H/O₂(H) quotient. -/
theorem SourceHypothesis.original_abelian_normal_unitaryEven_centralizing_residual
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n) (heven : Even n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) :
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
  obtain ⟨_,_,hc,_,_⟩ := S.original_abelian_normal_unitaryEven_split
    D hZ z hz hTV hTz hH hKH hK hgen hn hn2 heven hm
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
/-- The same centralizing cubic has no fixed vectors on the full original
U_H/V₁, retaining its literal quotient action and all earlier geometry. -/
theorem SourceHypothesis.original_abelian_normal_unitaryEven_fixed_free_cubic
    (hn : (K.subgroupOf H).Normal) {n : ℕ} (hn2 : 2 ≤ n) (heven : Even n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) :
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
  obtain ⟨hnC,_,hc,_,_⟩ := S.original_abelian_normal_unitaryEven_split
    D hZ z hz hTV hTz hH hKH hK hgen hn hn2 heven hm
  change Nat.card C = 3 at hc
  let _ := hnC
  have hne : C ≠ ⊥ := by
    intro h
    have hcard : Nat.card C = 1 := card_eq_one.mpr h
    omega
  obtain ⟨hU,a,_⟩ := S.original_abelian_quadratic_actor D hZ z hz hTV hTz hbound hTI hns hH
  let _ := hU
  have ha : subspaceCommutator a.representation ⊤ C = ⊤ :=
    S.original_normal_local_actor_full_movement D hZ z hz hTV hTz hbound hH a C hne
      (inf_le_left.trans (map_mono (comap_mono le_sup_left)))
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
