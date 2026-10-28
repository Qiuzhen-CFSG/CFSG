module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentElevenCore
public import Theory.GroupTheory.RankOneOuterCentralizer
public import Theory.Representation.BinaryOffender.CentralizingDisplacement
public import Theory.Representation.BinaryConjugationSection.FrattiniGeneration

/-!
# The original point span lies in the residual two-core

The actual E₉ image of L₁ contains a nontrivial cubic centralizing K-star:
its outer action vanishes, and rank one prevents an injection into the
component. This actor displaces the entire faithful Irr⁺ section U_H/V₁.
Its lifted commutators lie in the intrinsic O₂(L₁), since the original
Sylow containment gives normalization of L₁ by U_H.

In the contrary nonabelian branch, the point V₁ is exactly the Frattini
subgroup of U_H. Full displacement therefore lifts to U_H ≤ O₂(L₁).
All original geometric hypotheses, component markings and literal quotient
maps are retained. The numerical upper bound |O₂(L₁)| = 2⁹, the abelian
point-span assembly and the universal natural reduction remain to prove.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)

include hz hTV hTz hbound hH hn a in
/-- A genuine cubic element in the original L₁-star centralizes K-star. -/
theorem SourceHypothesis.original_selectedComponent_central_cubic
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ∃ x : Nonabelian.Setup.Hstar H,
      x ∈ Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ ∧ orderOf x = 3 ∧
      x ∈ centralizer (Nonabelian.Setup.star H c.K : Set (Nonabelian.Setup.Hstar H)) := by
  let A := Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁
  let B := Nonabelian.Setup.star H c.K
  obtain ⟨hA,hAc,_⟩ := S.original_selectedComponent_residual_star_elementary
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let := hA
  let : B.Normal := (S.original_selectedComponent_normal
    D hZ z hz hTV hTz hbound hH hn c a hTI hns).2
  let := c.component.2
  let : IsSimpleGroup B := S.original_selectedComponent_simple
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
  obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ :=
    S.original_selectedComponent_linearTwoEleven D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let := hfield
  let := hfinite
  have ho := (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
    (p := 11) (n := 1) (by decide) (by decide) (by decide) (by simpa using hF)).of_equiv
      (MulAut.outerCongr e).symm
  have hr : primeRank 3 B ≤ 1 :=
    (c.three_rank_eq_star.symm.trans (S.original_selectedComponent_rank_one
      D hZ z hz hTV hTz hbound hH hn c a hTI hns)).le
  have hc := elementary_plane_centralizer_ne_bot A B hAc center_eq_bot_of_simple_perfect hr ho
  obtain ⟨x,hx,hne⟩ := (A ⊓ centralizer (B : Set (Nonabelian.Setup.Hstar H))).bot_or_exists_ne_one.resolve_left hc
  refine ⟨x,hx.1,?_,hx.2⟩
  exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian x hx.1) hne

include hz hTV hTz hbound hH in
/-- The actual point span commutator with L₁ lies in intrinsic O₂(L₁).
The original Sylow containment supplies normalization of L₁. -/
theorem SourceHypothesis.original_point_span_residual_commutator_le :
    ⁅(D.fullSetup hZ T z).UH H,(D.fullSetup hZ T z).L₁⁆ ≤
      (D.fullSetup hZ T z).L₁.pCoreIn 2 := by
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hQN : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hUN : E.UH H ≤ normalizer (E.L₁ : Set G) :=
    (le_inf h.UH_le_H ((h.UH_le_QH.trans h.QH_le_T).trans hTV)).trans
      (S.original_module_normalizer_normalizes_residual D hZ z hTV hH)
  have hcore : E.L₁ ⊓ H.pCoreIn 2 ≤ E.L₁.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 H).to_le inf_le_right)
      inf_le_left ((le_inf E.L₁.le_normalizer (hAH.trans hQN)).trans inf_normalizer_le_normalizer_inf)
  exact (le_inf (le_normalizer_iff_commutator_le_right.mp hUN)
    ((commutator_mono h.UH_le_QH le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hAH.trans hQN)))).trans hcore

include hz hTV hTz hbound hH hn in
/-- In the contrary nonabelian branch, the marked point is precisely the
Frattini subgroup of the original U_H. -/
theorem SourceHypothesis.original_nonabelian_point_frattini :
    (frattini ((D.fullSetup hZ T z).UH H)).map ((D.fullSetup hZ T z).UH H).subtype =
      (D.fullSetup hZ T z).V₁ := by
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hnU := (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).1
  let : Fact (IsPGroup 2 (E.UH H)) := ⟨h.g2_hypothesis.U_isPGroup⟩
  have hphi : frattini (E.UH H) ≠ ⊥ := by
    intro he
    let := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp he
    exact hnU inferInstance
  let R := (frattini (E.UH H)).map (E.UH H).subtype
  have hR : R ≠ ⊥ := by
    intro he
    exact hphi ((map_eq_bot_iff_of_injective _ (E.UH H).subtype_injective).mp he)
  have hc : Nat.card R = 2 := by
    have hd : Nat.card R ∣ Nat.card E.V₁ := card_dvd_of_le h.frattini_UH_le_point
    rw [E.point_card hz] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (fun h1 => hR (card_eq_one.mp h1))
  exact eq_of_le_of_card_ge h.frattini_UH_le_point (by rw [hc,E.point_card hz])

include hz hTV hTz hbound hH hn a in
/-- The original U_H lies in the intrinsic O₂(L₁). The cubic centralizer
acts on the whole literal quotient; Frattini lifting retains its point kernel. -/
theorem SourceHypothesis.original_selectedComponent_pointSpan_le_residual_core
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    (D.fullSetup hZ T z).UH H ≤ (D.fullSetup hZ T z).L₁.pCoreIn 2 := by
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let _ : (E.V₁.subgroupOf (E.UH H)).Normal := h.point_normal_in_UH
  let _ : IsElementaryAbelian 2 (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) := h.point_quotient_elementary
  obtain ⟨σ,κ,hσ,_⟩ := h.faithful_point_quotient
  change Representation (ZMod 2) (Nonabelian.Setup.Hstar H)
    (Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))) at σ
  change BinaryConjugationSection H (E.UH H) E.V₁
    (σ.comp (QuotientGroup.mk' (pCore 2 H))) at κ
  have hI := (S.original_selectedComponent_whole_module D hZ z hz hTV hTz hbound
    hH hn c a hTI hns (W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))) σ hσ κ).2.2.1
  obtain ⟨x,hx,hx3,hc⟩ := S.original_selectedComponent_central_cubic
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
  have hfull := hI.centralizing_displacement_eq_top
    (W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))) σ hσ x hc
    (by intro he; simp [he] at hx3)
  obtain ⟨y,hy,rfl⟩ := hx
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  let R := E.L₁.pCoreIn 2 ⊓ E.UH H
  have hcomm : ⁅E.L₁,E.UH H⁆ ≤ R := by
    rw [commutator_comm]
    exact le_inf (S.original_point_span_residual_commutator_le D hZ z hz hTV hTz hbound hH)
      (le_normalizer_iff_commutator_le_left.mp (hAH.trans κ.normalized))
  have hrange := κ.displacement_range_le_imageSpace_of_commutator_le
    (W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))) E.L₁ R hcomm y hy
  change LinearMap.range (σ (QuotientGroup.mk' (pCore 2 H) y) - LinearMap.id) ≤ κ.imageSpace R at hrange
  rw [hfull] at hrange
  have himage : κ.imageSpace R = ⊤ := top_unique hrange
  exact (κ.le_of_full_image_of_kernel_le_frattini
    (W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))) R inf_le_right
    (S.original_nonabelian_point_frattini D hZ z hz hTV hTz hbound hH hn).ge himage).trans inf_le_left

include hz hTV hTz hbound hH hn in
/-- Original-source application of the core comparison. Component selection
and the literal action marking are constructed, leaving only the retained
earlier geometry. The remaining order-2⁹ upper bound would contradict the
lower bound here on the same intrinsic core. -/
theorem SourceHypothesis.original_nonabelian_point_span_core_bounds
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    let E := D.fullSetup hZ T z
    E.UH H ≤ E.L₁.pCoreIn 2 ∧ E.L₁.pCoreIn 2 ≤ H.pCoreIn 2 ∧
      2^11 ≤ Nat.card (E.L₁.pCoreIn 2) := by
  obtain ⟨c,_,_,⟨a⟩⟩ := S.original_selectedComponent_with_action
    D hZ z hz hTV hTz hbound hns hH hn
  have hu := S.original_selectedComponent_pointSpan_le_residual_core
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
  have hl := S.original_selectedComponent_pointSpan_large
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
  exact ⟨hu,S.original_selectedComponent_residual_core_le
    D hZ z hz hTV hTz hbound hH hn c a hTI hns,
    hl.trans (Nat.card_le_card_of_injective (inclusion hu) (inclusion_injective hu))⟩

end CFSG.Quasithin.Chapter12.Section06
