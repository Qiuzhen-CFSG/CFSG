module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.NaturalChiefBounds
public import CFSG.Quasithin.Chapter13.Section07.SourceDuality
public import Theory.GroupAction.NoncentralTwoChiefLength.QuotientImage
public import Theory.GroupAction.NoncentralTwoChiefLength.CoreMaps
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.ChiefCubicCores
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex

/-!
# The cubic upper bound in the nonabelian case-one branch

The literal quotient V_H/U_H contributes at most two to every cubic
fixed-point length. The residual centralization of H_C/V_H makes its
contribution zero. The surviving natural coordinates give |U_H| = 32,
including the central line. The original central pairing identifies
Q_H/H_C with the dual of U_H/C_U_H(Q_H), so both remaining intervals
contribute at most two. Thus the whole Q_H has length at most six.

The last theorem constructs the marked syntheme quotient of the common
local overgroup and restricts it to the actual two-core. Its quotient has
order eight, giving total length at most seven for the same actor.
No abelianness of U_L or replacement of its central kernel is assumed.
The matching Steinberg lower bound and the later abelian-span exclusion
remain with qt-d-138-a6-endgame-source; ordinary setup and markings remain
with qt-d-138-six-g2-source. This does not assert full 13.8.33.

Source: Aschbacher--Smith, Lemma 13.8.33, printed pp.966--967,
using the source duality of 13.7.4(2).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open NoncentralChiefRefinement.CubicComparison
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The actual dual quotient has no more elements than the whole seed span.
The source central kernel is retained. -/
theorem core_centralizer_index_le_span_card
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    (Source.HC H V₃).relIndex (Source.QH H) ≤ Nat.card (Source.UH H V₃) := by
  obtain ⟨hE,ρ,sU,sQ,_,_⟩ := Section07.source_central_duality (localNaturalSetup d) h
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  let := hE
  let U := Source.UH H V₃
  let U₀ := U ⊓ centralizer (Source.QH H : Set G)
  let W := Additive (U ⧸ U₀.subgroupOf U)
  let := sQ.kernel_normal
  let : ((Source.HC H V₃).subgroupOf (Source.QH H)).Normal := sQ.kernel_normal
  have hc : (Source.HC H V₃).relIndex (Source.QH H) =
      Nat.card (Module.Dual (ZMod 2) W) := by
    change (Source.HC H V₃ |>.subgroupOf (Source.QH H)).index = _
    rw [index_eq_card]
    exact Nat.card_congr sQ.quotientEquiv.toEquiv
  have hd : Nat.card (Module.Dual (ZMod 2) W) = Nat.card W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W), Subspace.dual_finrank_eq]
  rw [hc,hd]
  exact Nat.le_of_dvd Nat.card_pos (U₀.subgroupOf U).index_dvd_card

/-- The surviving natural branch has the whole span of order 32, including V₁. -/
theorem nonabelian_seed_span_card
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃)) :
    Nat.card (Source.UH H V₃) = 32 := by
  obtain ⟨F,_,_⟩ := natural_model_of_nonabelian d h c hDH hDg hcentral a e model hn
  have hq : Nat.card (Source.Utilde H V₃ V₁) = 16 := by
    change Nat.card (Additive (Source.Utilde H V₃ V₁)) = 16
    rw [Nat.card_congr F.toEquiv, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    decide
  have hVU : V₁ ≤ Source.UH H V₃ :=
    (d.line_le_plane.trans d.plane_le_seed).trans (le_conjugateSpanBy V₃ H)
  rw [card_eq_card_quotient_mul_card_subgroup (V₁.subgroupOf (Source.UH H V₃)),
    show Nat.card (Source.UH H V₃ ⧸ V₁.subgroupOf (Source.UH H V₃)) = 16 from hq,
    Nat.card_congr (subgroupOfEquivOfLe hVU).toEquiv, d.line_card]

/-- Transfer the chief-series bound from H/U_H to the original V_H/U_H section. -/
theorem nonabelian_span_section_length_le_two
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃))
    (A : Subgroup G) (hAH : A ≤ H) (hA : IsPGroup 3 A) :
    sectionCubicLength A (Source.UH H V₃) (Source.VH H V) ≤ 2 := by
  let U := (Source.UH H V₃).subgroupOf H
  let W := (Source.VH H V).subgroupOf H
  let : U.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V₃ H)
  let : W.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy V H)
  let π := QuotientGroup.mk' U
  let : (W.map π).Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  obtain ⟨s⟩ := NoncentralChiefRefinement.SeriesOn.exists_series (W.map π)
  have hb := (nonabelian_span_quotient_chief_structure d h c hH hDH hDg
    hcentral a e model hn s).2.2 ((A.subgroupOf H).map π) (hA.comap_subtype.map π)
  have hW2 : IsPGroup 2 W := ((isPGroup_pCoreIn 2 H).to_le
    (Section07.VH_le_core (localNaturalSetup d) h
      (show IsMulCommutative (Source.UH H V₃) from inferInstance))).comap_subtype
  have hUW : U ≤ W := subgroupOf_mono H (conjugateSpanBy_mono d.seed_le le_rfl)
  rw [← sectionCubicLength_eq_quotient_image (A.subgroupOf H) W U
    hA.comap_subtype hW2 hUW le_normalizer_of_normal] at hb
  change conjugationCubicLength (A.subgroupOf H) ((Source.VH H V).subgroupOf H) -
    conjugationCubicLength (A.subgroupOf H) ((Source.UH H V₃).subgroupOf H) ≤ 2 at hb
  rw [length_subgroupOf A (Source.VH H V) H hAH h.VH_le_H,
    length_subgroupOf A (Source.UH H V₃) H hAH h.UH_le_H] at hb
  exact hb

/-- Every three-subgroup of H has the same cubic length on H_C and V_H
in the contrary nonabelian branch. -/
theorem nonabelian_centralizer_length_eq
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃))
    (A : Subgroup G) (hAH : A ≤ H) (hA : IsPGroup 3 A) :
    conjugationCubicLength A (Source.HC H V₃) =
      conjugationCubicLength A (Source.VH H V) := by
  have hCQ : Source.HC H V₃ ≤ Source.QH H := by
    apply le_trans _ h.kernel_UH_eq_QH.le
    intro x hx
    exact (h.mem_kernel_iff h.UH_le_H).mpr ⟨hx.1,fun u hu => by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 u hu)]
      exact V₁.one_mem⟩
  have hVC := Section07.VH_centralizes_UH (localNaturalSetup d) h
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  have hCn : H ≤ normalizer (Source.HC H V₃ : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy V₃ H).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let : ((Source.VH H V).subgroupOf (Source.HC H V₃)).Normal :=
    normal_subgroupOf_of_le_normalizer
      ((show Source.HC H V₃ ≤ H from inf_le_left).trans (le_normalizer_conjugateSpanBy V H))
  have hperfect : IsPPerfect 2 (A.subgroupOf H) := by
    apply (pResidual_eq_top_iff 2 (A.subgroupOf H)).mp
    apply top_unique
    intro x _
    obtain ⟨n,hn⟩ := hA.comap_subtype.exists_orderOf_dvd_pow x
    exact mem_pResidual_of_orderOf_coprime
      (((by decide : Nat.Coprime 2 3).pow_right n).of_dvd_right hn)
  have hres : A ≤ (pResidual 2 H).map H.subtype := by
    have hm := map_mono (f := H.subtype) (le_pResidual_of_isPPerfect (A.subgroupOf H) hperfect)
    rwa [map_subgroupOf_eq_of_le hAH] at hm
  symm
  apply length_eq_of_commutator_le A (Source.HC H V₃) (Source.VH H V)
    hA ((isPGroup_pCoreIn 2 H).to_le hCQ) hVC (hAH.trans hCn)
    (hAH.trans (le_normalizer_conjugateSpanBy V H))
  exact (commutator_mono le_rfl hres).trans
    (nonabelian_centralizer_residual_commutator d h c hH hDH hDg hcentral a e model hn)

/-- The actual H-side filtration bounds every cubic action on Q_H by six.
The four contributions are at most two, two, zero and two, respectively. -/
theorem nonabelian_core_length_le_six
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃))
    (A : Subgroup G) (hAH : A ≤ H) (hA : IsPGroup 3 A) :
    conjugationCubicLength A (Source.QH H) ≤ 6 := by
  have hUcard := nonabelian_seed_span_card d h c hDH hDg hcentral a e model hn
  have hU := length_le_log_card A (Source.UH H V₃)
  rw [hUcard] at hU
  norm_num at hU
  have hW := nonabelian_span_section_length_le_two d h c hH hDH hDg hcentral a e model hn A hAH hA
  have hC := nonabelian_centralizer_length_eq d h c hH hDH hDg hcentral a e model hn A hAH hA
  obtain ⟨_,_,_,sQ,_,_⟩ := Section07.source_central_duality (localNaturalSetup d) h
    (show IsMulCommutative (Source.UH H V₃) from inferInstance)
  let := sQ.kernel_normal
  let : ((Source.HC H V₃).subgroupOf (Source.QH H)).Normal := sQ.kernel_normal
  have hCn : H ≤ normalizer (Source.HC H V₃ : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy V₃ H).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hQn : H ≤ normalizer (Source.QH H : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hQ := section_length_le_log_card A (Source.QH H) (Source.HC H V₃)
    hA (isPGroup_pCoreIn 2 H) sQ.kernel_le (hAH.trans hQn) (hAH.trans hCn)
  have hcard := core_centralizer_index_le_span_card d h
  rw [hUcard] at hcard
  have hbound : Nat.card (Source.QH H ⧸ (Source.HC H V₃).subgroupOf (Source.QH H)) ≤ 32 := hcard
  have hsmall := hQ.trans (Nat.log_mono_right hbound)
  norm_num at hsmall
  unfold sectionCubicLength at hW hsmall
  omega

/-- The common local two-core has cubic length at most seven in the
nonabelian branch. Its extra contribution is the actual syntheme core
of order eight, transported through the original star quotient. -/
theorem nonabelian_parabolic_core_length_le_seven
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (hn : ¬ IsMulCommutative (Source.UL L H V₃))
    (hmark : (Source.starImage H ((L ⊔ (T : Subgroup G)) ⊓ H)).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2)
    (A : Subgroup G) (hAP : A ≤ (L ⊔ (T : Subgroup G)) ⊓ H) (hA : IsPGroup 3 A) :
    conjugationCubicLength A (((L ⊔ (T : Subgroup G)) ⊓ H).pCoreIn 2) ≤ 7 := by
  let P := (L ⊔ (T : Subgroup G)) ⊓ H
  let D := Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hm : (P.subgroupOf H).map q = D := by
    rw [← map_map]
    exact hmark
  let φ : P →* D := (q.comp (inclusion inf_le_right)).codRestrict D
    (fun x => hm ▸ mem_map_of_mem q x.property)
  have hφ : Function.Surjective φ := by
    rintro ⟨y,hy⟩
    obtain ⟨x,hx,hxy⟩ := show y ∈ (P.subgroupOf H).map q from hm.symm ▸ hy
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  have hk : φ.ker = (Source.QH H).subgroupOf P := by
    ext x
    change φ x = 1 ↔ (x : G) ∈ Source.QH H
    rw [← Subtype.coe_inj]
    change e (QuotientGroup.mk' (pCore 2 H) (inclusion inf_le_right x)) = 1 ↔ _
    rw [← map_one e,e.injective.eq_iff]
    exact (QuotientGroup.eq_one_iff (inclusion (show P ≤ H from inf_le_right) x)).trans
      (mem_map_iff_mem H.subtype_injective).symm
  let f : A →* D := φ.comp (inclusion hAP)
  let localQuotient : LocalCoreQuotient A (Source.QH H) P D D f := {
    actor_le := hAP
    kernel_le := le_inf (h.QH_le_T.trans le_sup_right) (pCoreIn_le 2 H)
    projection := φ
    onto := hφ
    kernel := hk
    marked := fun _ => rfl }
  have hD : D ≤ normalizer (D.pCoreIn 2 : Set (Equiv.Perm (Fin 6))) :=
    D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))
  let := conjMulDistribMulActionOfLeNormalizer D (D.pCoreIn 2) hD
  let s := localQuotient.coreSection (isPGroup_pCoreIn 2 H) hD
  let := s.normal
  have hcard : Nat.card (P.pCoreIn 2 ⧸ (Source.QH H).subgroupOf (P.pCoreIn 2)) = 8 := by
    rw [Nat.card_congr s.quotientEquiv.toEquiv]
    change Nat.card (Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2.pCoreIn 2) = 8
    rw [Theory.SpecificGroups.SymmetricSix.BinaryFlags.H2_core_eq_D,
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.D_card]
  have htop := section_length_le_log_card A (P.pCoreIn 2) (Source.QH H)
    hA (isPGroup_pCoreIn 2 P) s.le s.normalizes s.normalizes_kernel
  rw [hcard] at htop
  norm_num at htop
  have hcore := nonabelian_core_length_le_six d h c hH hDH hDg hcentral a e model hn
    A (hAP.trans inf_le_right) hA
  unfold sectionCubicLength at htop
  change conjugationCubicLength A (P.pCoreIn 2) ≤ 7
  omega

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
