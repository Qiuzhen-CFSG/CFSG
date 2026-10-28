module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.AssemblyBridges
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions.Transport
public import Theory.Representation.SixLetterTransvections

/-!
# Extending the common axis from Uγ to Vγ

If A₁ is outside U_H, its intersection with U_H is trivial. The definition
of D_H therefore makes D_H centralize Uγ. After transporting the relative
centralizer H_C to the genuine endpoint, 13.7.3(7) makes D_H centralize Vγ
as well. An index-two fixed subgroup gives transvections on U_H and its
central quotient. The faithful six-letter action then bounds |Vγ*| by two.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.8.34(1), printed p.968; Lemma 13.7.3(7), printed p.936.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments
open CriticalGeometry CriticalGeometry.SectionActions
variable {G : Type*} [Group G] [Finite G]

private theorem line_inf_eq_bot (A U : Subgroup G) (hA : Nat.card A = 2)
    (hnot : ¬ A ≤ U) : A ⊓ U = ⊥ := by
  have hd : Nat.card (A ⊓ U : Subgroup G) ∣ 2 := hA ▸ card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact card_eq_one.mp h
  · exact (hnot ((eq_of_le_of_card_ge inf_le_left (by rw [hA, h]) : A ⊓ U = A).ge.trans
      inf_le_right)).elim

/-- The source 13.7.3(7) bound is transported through the actual endpoint
conjugator. It is not replaced by an assumed centralization of Vγ. -/
theorem denominator_centralizes_endpoint
    {L T H V : Subgroup G} (c : CriticalPair L T H V) (V₃ Z : Subgroup G)
    (hV₃V : V₃ ≤ V) (hZ : Nat.card Z = 2) (hnot : ¬ c.Aone Z ≤ Source.UH H V₃)
    (hz : H ≤ normalizer (Z : Set G))
    (hUJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hVγH : c.Vgamma ≤ H)
    (hHC : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ Z) :
    ⁅Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z), c.Ugamma V₃⁆ = ⊥ ∧
    ⁅c.Vgamma, Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z)⁆ = ⊥ := by
  let D := Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone Z)
  have hDU : D ≤ Source.UH H V₃ := commutatorPreimage_le _ _ _
  have hVnorm := hVγH.trans (le_normalizer_conjugateSpanBy V₃ H)
  have hUnorm : c.Ugamma V₃ ≤ normalizer (Source.UH H V₃ : Set G) := by
    exact (map_mono (conjugateSpanBy_mono hV₃V le_rfl)).trans hVnorm
  have hdis : c.Aone Z ⊓ Source.UH H V₃ = ⊥ :=
    line_inf_eq_bot _ _ (by
      change Nat.card (Z.map (MulAut.conj (c.gb : G)).toMonoidHom) = 2
      rw [card_map_of_injective (MulAut.conj (c.gb : G)).injective, hZ]) hnot
  have hc : ⁅D, c.Ugamma V₃⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hdis]
    exact le_inf
      (commutator_commutatorPreimage_le _ _ _
        (hUJ.trans (SectionActions.CriticalPair.normalizes_Aone c Z hz)))
      ((commutator_mono hDU le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hUnorm))
  have hDHC : D ≤ (Source.HC H V₃).conjBy (c.gb : G) :=
    AsymmetricPair.le_conjugate_HC (c.gb : G)
      (by
        change D ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom
        rw [← c.vertexGroup_gamma]
        exact hDU.trans hUJ) hc
  have hbound : ⁅c.Vgamma, D⁆ ≤ c.Aone Z := by
    have hm := map_mono (f := (MulAut.conj (c.gb : G)).toMonoidHom) hHC
    rw [map_commutator] at hm
    exact (commutator_mono le_rfl hDHC).trans hm
  refine ⟨hc, le_bot_iff.mp ?_⟩
  rw [← hdis]
  exact le_inf hbound ((commutator_mono le_rfl hDU).trans
    (le_normalizer_iff_commutator_le_right.mp hVnorm))

private theorem transvections_fixing_index_two (P U D : Subgroup G)
    [IsElementaryAbelian 2 U]
    (hn : P ≤ normalizer (U : Set G))
    (hindex : D.relIndex U = 2) (hc : ⁅D, P⁆ = ⊥) :
    ∀ p : P, binaryLinear (conjugationAction P U hn p) ∈
      LinearEquiv.transvections (ZMod 2) (Additive U) := by
  let A := (conjugationAction P U hn).range
  have hfix : D.subgroupOf U ≤ FixedPoints.subgroup A U := by
    rw [conjugationAction_fixed]
    exact subgroupOf_mono U (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hd : (FixedPoints.subgroup A U).index ∣ 2 := hindex ▸ index_dvd_of_le hfix
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo
  · have ht := index_eq_one.mp hone
    intro p
    have he : conjugationAction P U hn p = 1 := by
      apply MulEquiv.ext
      intro u
      have hu : u ∈ FixedPoints.subgroup A U := ht ▸ mem_top u
      exact hu ⟨conjugationAction P U hn p, ⟨p, rfl⟩⟩
    rw [he]
    exact LinearEquiv.one_mem_transvections
  · exact fun p => transvections_of_fixed_index_two A htwo _ ⟨p, rfl⟩

private theorem quotient_transvections_fixing_index_two (P U Z D : Subgroup G)
    [IsElementaryAbelian 2 U]
    (hn : P ≤ normalizer (U : Set G)) (hz : P ≤ normalizer (Z : Set G))
    (hindex : D.relIndex U = 2) (hc : ⁅D, P⁆ = ⊥) :
    ∀ p : P, binaryLinear (quotientAction P U Z hn hz p) ∈
      LinearEquiv.transvections (ZMod 2) (Additive (U ⧸ Z.subgroupOf U)) := by
  intro p
  let q := QuotientGroup.mk' (Z.subgroupOf U)
  apply transvection_of_surjective_intertwiner (binaryMap q)
    (QuotientGroup.mk'_surjective (Z.subgroupOf U))
    (binaryLinear (conjugationAction P U hn p)) _
  · intro w
    change q (conjugationAction P U hn p w.toMul) =
      quotientAction P U Z hn hz p (q w.toMul)
    rw [quotientAction_apply]
    rfl
  · exact transvections_fixing_index_two P U D hn hindex hc p

/-- A common fixed hyperplane in U descends to U/Z. Faithfulness on that
actual quotient bounds the star image by two and identifies the nested images. -/
theorem star_eq_of_centralized_index_two (H U Z X Y D : Subgroup G)
    [IsElementaryAbelian 2 U]
    (hn : H ≤ normalizer (U : Set G)) (hz : H ≤ normalizer (Z : Set G))
    (hYH : Y ≤ H) (hXY : X ≤ Y)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (U ⧸ Z.subgroupOf U)))
    (hρ : Function.Injective ρ)
    (hact : ∀ h : H, ρ (QuotientGroup.mk' (pCore 2 H) h) =
      (binaryLinear (quotientAction H U Z hn hz h)).toLinearMap)
    (model : Nonempty (Source.Hstar H ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Source.Hstar H ≃* Equiv.Perm (Fin 6)))
    (hX : Nat.card (Source.starImage H X) = 2)
    (hindex : D.relIndex U = 2) (hc : ⁅D, Y⁆ = ⊥) :
    Source.starImage H Y = Source.starImage H X ∧
      Representation.BinaryOffender.rank (Source.starImage H Y) = 1 := by
  have hcard : Nat.card (Source.starImage H Y) ≤ 2 := by
    apply Representation.SixLetterTransvections.card_le_two_of_element_displacements ρ hρ model
    rintro a ⟨y, hy, rfl⟩
    rw [hact]
    apply LinearEquiv.mem_dilatransvections_iff_finrank.mp
    apply LinearEquiv.transvections_subset_dilatransvections
    have he : quotientAction H U Z hn hz y =
        quotientAction Y U Z (hYH.trans hn) (hYH.trans hz) ⟨y, hy⟩ := by
      ext w
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w
      rw [quotientAction_apply, quotientAction_apply]
    rw [he]
    exact quotient_transvections_fixing_index_two Y U Z D
      (hYH.trans hn) (hYH.trans hz) hindex hc ⟨y, hy⟩
  have he : Source.starImage H X = Source.starImage H Y :=
    eq_of_le_of_card_ge (map_mono (subgroupOf_mono H hXY)) (by rw [hX]; exact hcard)
  refine ⟨he.symm, ?_⟩
  change Nat.log 2 (Nat.card (Source.starImage H Y)) = 1
  rw [← he, hX]
  decide

/-- Corrected 13.8.10 in the opposite orientation gives the actual
common axis D_H of Uγ on U_H when A₁ is outside U_H. -/
theorem axis_of_noncontained_line (U Uγ A Z : Subgroup G)
    [IsElementaryAbelian 2 U] [IsElementaryAbelian 2 Uγ]
    (hn : Uγ ≤ normalizer (U : Set G)) (hA : U ≤ normalizer (A : Set G))
    (hγindex : (Source.Dgamma Uγ U Z).relIndex Uγ = 2)
    (hHindex : (Source.DH U Uγ A).relIndex U = 2)
    (hline : Nat.card A = 2) (hnot : ¬ A ≤ U) :
    HasTransvectionAxis Uγ U (Source.DH U Uγ A) hn := by
  have hp : Source.DH Uγ U Z < Uγ := by
    refine lt_of_le_of_ne (commutatorPreimage_le _ _ _) ?_
    intro he
    change (Source.DH Uγ U Z).relIndex Uγ = 2 at hγindex
    rw [he, relIndex_self] at hγindex
    omega
  have hcmp : (Source.DH Uγ U Z).relIndex Uγ ≤ (Source.Dgamma U Uγ A).relIndex U := by
    change (Source.Dgamma Uγ U Z).relIndex Uγ ≤ (Source.DH U Uγ A).relIndex U
    omega
  exact (corrected_rank_one Uγ U Z A hp hcmp hHindex hline hn hA).2.resolve_left hnot

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments
