module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourCore
public import Theory.GroupTheory.HeisenbergNormalizedSubgroups
public import Theory.GroupTheory.PResidual.ConjugateSpanSupplement
public import Theory.GroupTheory.PResidual.SupplementCommutator

/-!
# The common cubic and the original three-core branch

The actual common Sylow three-subgroup Y of K and H is Heisenberg27, and
X = Y ∩ L₁ is exactly Z(Y). Every Y-normalized subgroup of C_G(x) whose
order is divisible by three has an invariant Sylow containing X centrally.
Since X normally generates the original two-perfect L₁, any such subgroup
also normalized by L₁ contains L₁. In particular this applies to the actual
normal subgroups of every overgroup H ∩ C_G(x) < G₀ ≤ C_G(x).

When O₃(G₀/O₂(G₀)) is nontrivial, its literal preimage contains L₁, and
O₂(L₁) lies in O₂(G₀). The actual residual identity is
L₁ = O²(X O₂(G₀)) = X[O₂(G₀),X]. A full Sylow three-subgroup of G₀ then
normalizes L₁, so it lies in H ∩ C_G(x). That proper subgroup already
contains a full Sylow two-subgroup, hence G₀ has a prime divisor greater
than three.

The extension ExtraspecialFourThreeCore uses the quotient three-core
action to exclude such a prime and complete three-core vanishing.
No normality of L₁ in G₀ or local-recognition premise is assumed.
Source: Aschbacher–Smith, refs/quasithin.pdf, 14.7.26, printed pp.1052–1053.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Representation Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
open scoped IsMulCommutative Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Select the actual common three-Sylow in K and H. Its intersection with
L₁ is precisely its center of order three. -/
theorem extraspecial_four_three_sylow_center
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ Y : Subgroup G, Y ≤ K F ∧ IsSylowIn 3 Y (K F) ∧ IsSylowIn 3 Y F.H ∧
      Nonempty (Y ≃* HeisenbergPrime 3) ∧ Nat.card (Y ⊓ F.Li L 1 : Subgroup G) = 3 ∧
      Y ⊓ F.Li L 1 = (center Y).map Y.subtype := by
  obtain ⟨B,hYK,_,⟨e⟩,_,_⟩ := extraspecial_normalizer_three_sylow_in_residual
    d h hab structural previous faithful earlier he
  let Y := (B : Subgroup _).map (normalizer (K F : Set G)).subtype
  have hNH := (extraspecial_source_14721 d h hab structural previous faithful earlier he).1
  have hYH : IsSylowIn 3 Y F.H := by
    rw [←hNH]
    exact ⟨B,rfl⟩
  have hc := (extraspecial_normalizer_point_three_sylow h hab structural previous faithful he B).2
  have hYN : Y ≤ normalizer (K F : Set G) := map_subtype_le _
  have hYL : Y ≤ normalizer (F.Li L 1 : Set G) := hYN.trans
    (extraspecial_normalizer_normalizes_point h hab structural previous faithful he)
  let X := (F.Li L 1).subgroupOf Y
  let : X.Normal := normal_subgroupOf_of_le_normalizer hYL
  have hX : Nat.card X = 3 := by
    rw [←card_map_of_injective Y.subtype_injective,subgroupOf_map_subtype,inf_comm]
    exact hc
  have hp : IsPGroup 3 Y := B.isPGroup'.map (normalizer (K F : Set G)).subtype
  have hXZ : X ≤ center Y := hp.normal_le_center_of_card_dvd_prime X (by rw [hX])
  have hXeq : X = center Y := eq_of_le_of_card_ge hXZ (by
    rw [hX,Nat.card_congr (centerCongr e).toEquiv,HeisenbergPrime.card_center])
  have hh := congrArg (map Y.subtype) hXeq
  rw [subgroupOf_map_subtype,inf_comm] at hh
  exact ⟨Y,hYK,IsSylowIn.restrict hYH hYK (K_le_H F),hYH,⟨e⟩,hc,hh⟩

/-- The original central cubic lies centrally in an invariant Sylow of
every Y-normalized subgroup of the outside involution centralizer whose
order is divisible by three. This applies simultaneously to all the
source overgroups G₀ and their normalized subgroups. -/
theorem extraspecial_four_invariant_three_sylows
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
    ∃ Y : Subgroup G, Y ≤ K F ∧ IsSylowIn 3 Y (K F) ∧ IsSylowIn 3 Y F.H ∧
      Nonempty (Y ≃* HeisenbergPrime 3) ∧ Nat.card (Y ⊓ F.Li L 1 : Subgroup G) = 3 ∧
      Y ⊓ F.Li L 1 = (center Y).map Y.subtype ∧
      ∀ I : Subgroup G, I ≤ centralizer ({x} : Set G) →
        Y ≤ normalizer (I : Set G) → 3 ∣ Nat.card I →
        ∃ P : Sylow 3 I,
          let R := (P : Subgroup I).map I.subtype
          Y ≤ normalizer (R : Set G) ∧ Y ⊓ F.Li L 1 ≤ (center R).map R.subtype := by
  obtain ⟨Y,hYK,hSYK,hSYH,⟨e⟩,hc,hX⟩ := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  refine ⟨Y,hYK,hSYK,hSYH,⟨e⟩,hc,hX,?_⟩
  let C := centralizer ({x} : Set G)
  have hC := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hr : primeRank 3 C ≤ 2 := hC.stronglyQuasithin 3 (by decide) (by decide)
  have hKC : K F ≤ C := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  intro I hIC hYI hd
  rw [hX]
  exact exists_sylow_center_containing_heisenberg_center_in Y I C e hr (hYK.trans hKC) hIC hYI hd


/-- The cubic intersection normally generates the actual two-perfect point
residual; its complement is the literal two-core of L₁. -/
theorem extraspecial_point_generated_by_cubic
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (X : Subgroup G) (hXL : X ≤ F.Li L 1) (hc : Nat.card X = 3) :
    X ⊔ (F.Li L 1).pCoreIn 2 = F.Li L 1 ∧
      conjugateSpanBy X (F.Li L 1) = F.Li L 1 := by
  let A := F.Li L 1
  let Q := A.pCoreIn 2
  have hx : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [hc]; decide)
  have hd : Disjoint X Q := hx.disjoint_of_coprime (isPGroup_pCoreIn 2 A) (by decide)
  have hn : A ≤ normalizer (Q : Set G) := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hjoin : X ⊔ Q = A := eq_of_le_of_card_ge (sup_le hXL (pCoreIn_le 2 A)) (by
    rw [sup_comm X Q,card_sup_eq_mul_of_normalizes_of_disjoint Q X (hXL.trans hn) hd.symm,hc]
    have he := card_eq_card_quotient_mul_card_subgroup (s := pCore 2 A)
    rw [show Nat.card (A ⧸ pCore 2 A) = 3 from pointResidual_core_quotient_card h structural] at he
    have hQ : Nat.card Q = Nat.card (pCore 2 A) := card_map_of_injective A.subtype_injective
    rw [hQ,he,Nat.mul_comm])
  refine ⟨hjoin,?_⟩
  exact conjugateSpan_eq_of_pPerfect_supplement A X A Q
    (isPPerfect_embedded_pResidual 2 (L ⊓ F.H)) (isPGroup_pCoreIn 2 A)
    hjoin (pCoreIn_le 2 A) A.le_normalizer

/-- Every subgroup normalized by the original Y and L₁ whose order is
divisible by three contains L₁. The conclusion uses the actual central
cubic and its normal generation, rather than a group-family label. -/
theorem extraspecial_four_point_containment
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
    ∃ Y : Subgroup G, Y ≤ K F ∧ IsSylowIn 3 Y (K F) ∧ IsSylowIn 3 Y F.H ∧
      Nonempty (Y ≃* HeisenbergPrime 3) ∧ Nat.card (Y ⊓ F.Li L 1 : Subgroup G) = 3 ∧
      Y ⊓ F.Li L 1 = (center Y).map Y.subtype ∧
      ∀ I : Subgroup G, I ≤ centralizer ({x} : Set G) →
        Y ≤ normalizer (I : Set G) → F.Li L 1 ≤ normalizer (I : Set G) →
        3 ∣ Nat.card I → F.Li L 1 ≤ I := by
  obtain ⟨Y,hYK,hSYK,hSYH,heY,hc,hX,hSyl⟩ := extraspecial_four_invariant_three_sylows
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  refine ⟨Y,hYK,hSYK,hSYH,heY,hc,hX,?_⟩
  intro I hIC hYI hLI hd
  obtain ⟨P,_,hXP⟩ := hSyl I hIC hYI hd
  have hXI : Y ⊓ F.Li L 1 ≤ I :=
    hXP.trans ((map_subtype_le _).trans (map_subtype_le _))
  rw [←(extraspecial_point_generated_by_cubic h structural (Y ⊓ F.Li L 1) inf_le_right hc).2]
  exact conjugateSpanBy_le hXI hLI

/-- For every actual overgroup G₀, a normal subgroup divisible by three
contains the original L₁. Thus the nontrivial three-core preimage and every
normal component candidate are constrained by the same original cubic. -/
theorem extraspecial_four_normal_subgroup_contains_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (G₀ I : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hIG : I ≤ G₀) (hGI : G₀ ≤ normalizer (I : Set G)) (hd : 3 ∣ Nat.card I) :
    F.Li L 1 ≤ I := by
  obtain ⟨Y,hYK,_,_,_,_,_,hcontains⟩ := extraspecial_four_point_containment
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  have hKG : K F ≤ G₀ := (le_inf (K_le_H F) hKC).trans hJG
  exact hcontains I (hIG.trans hGC) (hYK.trans (hKG.trans hGI))
    ((pointResidual_le F).trans (hKG.trans hGI)) hd


/-- A nontrivial three-core above O₂(G₀) contains L₁ in its literal
preimage. Consequently the intrinsic core of L₁ lies in O₂(G₀). -/
theorem extraspecial_four_threeCore_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) ≤ G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hthree : pCore 3 (G₀ ⧸ pCore 2 G₀) ≠ ⊥) :
    let I := (pCore 3 (G₀ ⧸ pCore 2 G₀)).comap (QuotientGroup.mk' (pCore 2 G₀))
    F.Li L 1 ≤ I.map G₀.subtype ∧ (F.Li L 1).pCoreIn 2 ≤ G₀.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 G₀)
  let R := pCore 3 (G₀ ⧸ pCore 2 G₀)
  let I := R.comap q
  have hi : I.Normal := inferInstance
  have hd : 3 ∣ Nat.card (I.map G₀.subtype) := by
    rw [card_map_of_injective G₀.subtype_injective]
    have hRdiv : 3 ∣ Nat.card R := (pCore_isPGroup (p := 3)).card_eq_or_dvd.resolve_left
      (fun hc => hthree ((eq_bot_iff_card R).mpr hc))
    have hm : I.map q = R := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    exact hRdiv.trans (hm ▸ card_map_dvd I q)
  have hGI : G₀ ≤ normalizer (I.map G₀.subtype : Set G) := by
    have hh := (I.le_normalizer_map G₀.subtype)
    rw [I.normalizer_eq_top, ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hLI := extraspecial_four_normal_subgroup_contains_point
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    G₀ (I.map G₀.subtype) hJG hGC (map_subtype_le _) hGI hd
  refine ⟨hLI,?_⟩
  let P := (F.Li L 1).pCoreIn 2
  have hPI : P ≤ I.map G₀.subtype := (pCoreIn_le 2 _).trans hLI
  have hPG : P ≤ G₀ := hPI.trans (map_subtype_le _)
  have hmap : (P.subgroupOf G₀).map q ≤ R := by
    rintro _ ⟨p,hp,rfl⟩
    obtain ⟨i,hi,hie⟩ := hPI hp
    exact (show i = p from Subtype.ext hie) ▸ hi
  have h2 : IsPGroup 2 ((P.subgroupOf G₀).map q) :=
    (isPGroup_pCoreIn 2 (F.Li L 1)).comap_subtype.map q
  have h3 : IsPGroup 3 ((P.subgroupOf G₀).map q) :=
    (pCore_isPGroup (p := 3)).to_le hmap
  have hbot : (P.subgroupOf G₀).map q = ⊥ := by
    simpa only [inf_idem] using (h2.disjoint_of_coprime h3 (by decide)).eq_bot
  have hk : P.subgroupOf G₀ ≤ pCore 2 G₀ := by
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hbot
  change P ≤ (pCore 2 G₀).map G₀.subtype
  simpa only [map_subgroupOf_eq_of_le hPG] using map_mono (f := G₀.subtype) hk

/-- In the three-core branch, the point residual is the literal two-residual
of X O₂(G₀), equivalently X[O₂(G₀),X], for the actual X = Y ∩ L₁.
The original strict-overgroup hypotheses provide normalization; no
ambient normality of L₁ is asserted or assumed. -/
theorem extraspecial_four_threeCore_point_reconstruction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hthree : pCore 3 (G₀ ⧸ pCore 2 G₀) ≠ ⊥) :
    ∃ Y : Subgroup G, Y ≤ K F ∧ IsSylowIn 3 Y (K F) ∧ IsSylowIn 3 Y F.H ∧
      Nonempty (Y ≃* HeisenbergPrime 3) ∧ Nat.card (Y ⊓ F.Li L 1 : Subgroup G) = 3 ∧
      Y ⊓ F.Li L 1 = (center Y).map Y.subtype ∧
      let X := Y ⊓ F.Li L 1
      (pResidual 2 (G₀.pCoreIn 2 ⊔ X : Subgroup G)).map (G₀.pCoreIn 2 ⊔ X).subtype = F.Li L 1 ∧
        F.Li L 1 = X ⊔ ⁅G₀.pCoreIn 2,X⁆ := by
  obtain ⟨Y,hYK,hSYK,hSYH,heY,hc,hX⟩ := extraspecial_four_three_sylow_center
    d h hab structural previous faithful earlier he
  refine ⟨Y,hYK,hSYK,hSYH,heY,hc,hX,?_⟩
  let X := Y ⊓ F.Li L 1
  let Q := G₀.pCoreIn 2
  have hcore := (extraspecial_four_threeCore_point d h hab structural previous faithful earlier he
    D hZD hDK hcard hDT hND hx hxZ G₀ hJG.le hGC hthree).2
  have hQH := (extraspecial_four_strict_overgroup_geometry
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC).2.1
  have hNL : Q ≤ normalizer (F.Li L 1 : Set G) :=
    (hQH.trans (pCoreIn_le 2 F.H)).trans (by
      rw [←(extraspecial_source_14721 d h hab structural previous faithful earlier he).1]
      exact extraspecial_normalizer_normalizes_point h hab structural previous faithful he)
  have hgen := (extraspecial_point_generated_by_cubic h structural X inf_le_right hc).1
  have hjoin : Q ⊔ X = F.Li L 1 ⊔ Q := by
    apply le_antisymm
    · exact sup_le le_sup_right (inf_le_right.trans le_sup_left)
    · apply sup_le _ le_sup_left
      rw [←hgen]
      exact sup_le le_sup_right (hcore.trans le_sup_left)
  have hp : IsPPerfect 2 (F.Li L 1) := isPPerfect_embedded_pResidual 2 (L ⊓ F.H)
  have hr : (pResidual 2 (Q ⊔ X : Subgroup G)).map (Q ⊔ X).subtype = F.Li L 1 := by
    rw [hjoin]
    exact embedded_pResidual_join_pGroup _ _ hp (isPGroup_pCoreIn 2 G₀) hNL
  refine ⟨hr,?_⟩
  have hXp : IsPPerfect 2 X := by
    apply (pResidual_eq_top_iff 2 X).mp
    apply top_unique
    intro a _
    exact mem_pResidual_of_orderOf_coprime
      ((show Nat.Coprime 2 (Nat.card X) by rw [hc]; decide).of_dvd_right (orderOf_dvd_natCard a))
  change F.Li L 1 = X ⊔ ⁅Q,X⁆
  exact hr.symm.trans (embedded_pResidual_sup_eq_sup_commutator Q X (isPGroup_pCoreIn 2 G₀) hXp)


/-- If the actual quotient has a three-core, a full Sylow three-subgroup
of G₀ lies in H ∩ G₀. This is normalizer control from the retained
X O₂(G₀) residual, without assuming L₁ normal in G₀. -/
theorem extraspecial_four_threeCore_sylow_control
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hthree : pCore 3 (G₀ ⧸ pCore 2 G₀) ≠ ⊥) :
    ∃ P : Sylow 3 G₀, (P : Subgroup G₀).map G₀.subtype ≤
      F.H ⊓ centralizer ({x} : Set G) := by
  obtain ⟨Y,hYK,_,_,⟨e⟩,hc,hX,hr,_⟩ := extraspecial_four_threeCore_point_reconstruction
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hthree
  let Q := G₀.pCoreIn 2
  let X := Y ⊓ F.Li L 1
  have hKC : K F ≤ centralizer ({x} : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDK hx).2 k hk)
  have hYG : Y ≤ G₀ := hYK.trans ((le_inf (K_le_H F) hKC).trans hJG.le)
  have hC := (extraspecial_four_centralizer_source_setup
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).1
  have hG : IsSQTK KnownSimple.IsKnownSimple G₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hGC)).mp
      (hC.subgroup (G₀.subgroupOf (centralizer ({x} : Set G))))
  have hdiv : 3 ∣ Nat.card G₀ := (by
    rw [Nat.card_congr e.toEquiv,HeisenbergPrime.card]
    decide : 3 ∣ Nat.card Y).trans (card_dvd_of_le hYG)
  obtain ⟨P,_,hXP⟩ := exists_sylow_center_containing_heisenberg_center_in Y G₀ G₀ e
    (hG.stronglyQuasithin 3 (by decide) (by decide)) hYG le_rfl
    (hYG.trans G₀.le_normalizer) hdiv
  let R := (P : Subgroup G₀).map G₀.subtype
  have hRX : R ≤ normalizer (X : Set G) := by
    change R ≤ normalizer ((Y ⊓ F.Li L 1 : Subgroup G) : Set G)
    rw [hX]
    have hh : (center Y).map Y.subtype ≤ centralizer (R : Set G) :=
      hXP.trans (by rw [map_center_subtype_eq_inf_centralizer R]; exact inf_le_right)
    exact (le_centralizer_iff.mp hh).trans (Subgroup.centralizer_le_normalizer _)
  have hRQ : R ≤ normalizer (Q : Set G) := (map_subtype_le _).trans
    (G₀.le_normalizer.trans (normalizer_le_normalizer_characteristic_image G₀ (pCore 2 G₀)))
  have hRjoin : R ≤ normalizer ((Q ⊔ X : Subgroup G) : Set G) :=
    (le_inf hRQ hRX).trans (normalizer_inf_normalizer_le_normalizer_sup Q X)
  have hRL : R ≤ normalizer (F.Li L 1 : Set G) := by
    rw [←hr]
    exact hRjoin.trans (normalizer_le_normalizer_characteristic_image (Q ⊔ X) (pResidual 2 _))
  have hNL : normalizer (F.Li L 1 : Set G) = F.H :=
    (extraspecial_core_normalizer_eq d h hab structural previous faithful he).2.trans
      (extraspecial_source_14721 d h hab structural previous faithful earlier he).1
  exact ⟨P,le_inf (hRL.trans_eq hNL) ((map_subtype_le _).trans hGC)⟩

/-- In the three-core branch the strict overgroup has a prime divisor
larger than three: its proper point normalizer already contains full
Sylow two- and three-subgroups. This is the contradiction used once the
quotient three-core action excludes every prime greater than three. -/
theorem extraspecial_four_threeCore_large_prime
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H)
    (G₀ : Subgroup G) (hJG : F.H ⊓ centralizer ({x} : Set G) < G₀)
    (hGC : G₀ ≤ centralizer ({x} : Set G))
    (hthree : pCore 3 (G₀ ⧸ pCore 2 G₀) ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ 3 < q ∧ q ∣ Nat.card G₀ := by
  let J := (F.H ⊓ centralizer ({x} : Set G)).subgroupOf G₀
  obtain ⟨P,hP⟩ := extraspecial_four_threeCore_sylow_control
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc hx hxZ hout
    G₀ hJG hGC hthree
  have hPJ : (P : Subgroup G₀) ≤ J := fun p hp => hP (mem_map_of_mem G₀.subtype hp)
  have h3 : ¬ 3 ∣ J.index := fun hd => P.not_dvd_index (hd.trans (index_dvd_of_le hPJ))
  have hSyl := IsSylowIn.restrict (H := centralizer ({x} : Set G))
    (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
    ((le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right).trans hJG.le) hGC
  obtain ⟨S,hS⟩ := hSyl
  have hSJ : (S : Subgroup G₀) ≤ J := by
    intro s hs
    have hm : (s : G) ∈ (S : Subgroup G₀).map G₀.subtype := mem_map_of_mem _ hs
    rw [hS] at hm
    exact ⟨F.invariant 1 hm.1,hm.2⟩
  have h2 : ¬ 2 ∣ J.index := fun hd => S.not_dvd_index (hd.trans (index_dvd_of_le hSJ))
  have hn : J.index ≠ 1 := by
    intro heq
    exact hJG.not_ge (relIndex_eq_one.mp heq)
  obtain ⟨q,hq,hqd⟩ := Nat.exists_prime_and_dvd hn
  have hq2 : q ≠ 2 := fun hh => h2 (hh ▸ hqd)
  have hq3 : q ≠ 3 := fun hh => h3 (hh ▸ hqd)
  exact ⟨q,hq,by have := hq.two_le; omega,hqd.trans J.index_dvd_card⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
