module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.SylowMarking
/-!
# Characteristic Baumann alternatives for the covered S₅ action

Keep the full first member of the canonical characteristic pair. Its
centrality in the selected local group implies normalization by the cubic;
the full Sylow normalizes it by characteristicity in the Baumann subgroup.
Their actual generation gives normality in the original group. The second
member has the same normality conclusion. Thus this version applies to the
literal no-characteristic-Baumann hypothesis, without replacing it by a
hypothesis about characteristic subgroups of the full Sylow.

Source: Aschbacher–Smith C.1.21(3), C.1.24(a), printed pp.128–131.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open ChapterB Theory.SpecificGroups.SymmetricFive Theory.SpecificGroups.SymmetricFive.CubicSelection
universe u v
variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
theorem local_pair_normal_alternatives
    (R Y : Subgroup H) (hgen : Y ⊔ R = ⊤)
    (D : GlaubermanNiles.CharacteristicPair (baumann R))
    {A : Type v} [Group A] (k : A →* H) (j : baumann R →* A)
    (hkj : k.comp j = (baumann R).subtype) (hY : Y ≤ k.range)
    (hAlt : GlaubermanNiles.Alternatives D.first D.second j) :
    (D.first.map (baumann R).subtype).Normal ∨
      (D.second.map (baumann R).subtype).Normal ∨ GlaubermanNiles.BlockAlternative A := by
  have step (C : Subgroup (baumann R)) [C.Characteristic] (hn : (C.map j).Normal) :
      (C.map (baumann R).subtype).Normal := by
    let : (C.map j).Normal := hn
    have he : (C.map j).map k = C.map (baumann R).subtype := by rw [map_map,hkj]
    have ha : k.range ≤ normalizer (C.map (baumann R).subtype : Set H) := by
      have hh := (C.map j).le_normalizer_map k
      rwa [normalizer_eq_top,←MonoidHom.range_eq_map,he] at hh
    have hr : R ≤ normalizer (C.map (baumann R).subtype : Set H) :=
      (R.le_normalizer.trans (normalizer_le_normalizer_baumann R)).trans
        (normalizer_le_normalizer_characteristic_image _ C)
    apply normalizer_eq_top_iff.mp
    exact top_le_iff.mp (hgen ▸ sup_le (hY.trans ha) hr)
  rcases hAlt with hc | hn | hb
  · let := D.first_characteristic
    exact Or.inl (step D.first (by
      constructor
      intro x hx g
      have heq : g * x * g⁻¹ = x := by
        rw [(mem_center_iff.mp (hc hx)) g]
        simp [mul_assoc]
      rwa [heq]))
  · let := D.second_characteristic
    exact Or.inr (Or.inl (step D.second hn))
  · exact Or.inr (Or.inr hb)

theorem marked_source_normal_alternatives
    (R : Sylow 2 H) (hfit : generalizedFitting H = pCore 2 H)
    (L : Subgroup H) [L.Normal] (hcomp : L.IsCComponent)
    (hprod : L ⊔ (R : Subgroup H) = ⊤)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (hR : (R : Subgroup H).map q = OuterFourGeometry.eight)
    (hL : L.map q = alternatingGroup (Fin 5))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (U : Set H))
    (D : GlaubermanNiles.CharacteristicPair (baumann (R : Subgroup H)))
    (hD : D.Universal.{u,u}) :
    (D.first.map (baumann (R : Subgroup H)).subtype).Normal ∨
      (D.second.map (baumann (R : Subgroup H)).subtype).Normal ∨
      (IsBlock L ∧ IsAlternatingBlock L 5 ∧
        L = ⁅L,elementaryAbelianMaxJ (R : Subgroup H)⁆ ∧
        (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U) := by
  have hc := Nat.card_congr eL.toEquiv
  obtain ⟨A,j,hA,hj,hclass,halt⟩ := marked_quotient_original_pair R hfit L hprod hc U
    q hq hk hR hL p hp he hfix hJ D hD
  let Y := selectedResidual q L
  let B := baumann (R : Subgroup H)
  let N := cubicLocalGroup q
  let k : A →* H := N.subtype.comp A.subtype
  have hkp := action_kernel_twoGroup q L R hprod R.isPGroup' hL hc
  have hgen : Y ⊔ (R : Subgroup H) = ⊤ :=
    selectedResidual_generates q L R hL hR (hkp.le_sylow_of_normal R)
  have hrange : k.range = Y ⊔ B := by
    rw [MonoidHom.range_comp,range_subtype]
    exact hA
  have hYr : Y ≤ k.range := hrange.symm ▸ le_sup_left
  rcases local_pair_normal_alternatives (R : Subgroup H) Y hgen D k j hj hYr halt with hn | hn | hb
  · exact Or.inl hn
  · exact Or.inr (Or.inl hn)
  · right; right
    have hUR : U ≤ R := (show U ≤ pCore 2 H from
      le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩).trans
        (pCore_isPGroup.le_sylow_of_normal R)
    obtain ⟨hJi,hBi⟩ := marked_quotient_images R U hUR q hq hk hR p hp he hfix hJ
    have hblock := selected_local_block_propagates R hfit L hcomp eL q hq hL hBi A hA hb
    have hQ : pCore 2 H ≤ q.ker := by
      rw [←MonoidHom.comap_bot]
      apply map_le_iff_le_comap.mp
      rw [←Theory.SpecificGroups.SymmetricFive.pCore_two_eq_bot]
      exact le_sSup ⟨Subgroup.Normal.map inferInstance q hq,pCore_isPGroup.map q⟩
    obtain ⟨ha,hs⟩ := alternating_block_of_covered_quotient U q hq hk L hL hblock
      (hQ.trans_eq hk) p hp he hfix
    have hcomm : L = ⁅L,elementaryAbelianMaxJ (R : Subgroup H)⁆ :=
      @component_eq_thompson_commutator H inferInstance (R : Subgroup H) L inferInstance
        hblock.short.twoPerfect q hkp hL hJi
    exact ⟨hblock,ha,hcomm,hs,hs.le.trans (commutator_le_left U L)⟩

theorem source_normal_alternatives
    (R : Sylow 2 H) (hfit : generalizedFitting H = pCore 2 H)
    (L : Subgroup H) [L.Normal] (hcomp : L.IsCComponent)
    (hprod : L ⊔ (R : Subgroup H) = ⊤)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set H))
    (hL : L.map q = alternatingGroup (Fin 5))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup H) ≤ centralizer (U : Set H))
    (D : GlaubermanNiles.CharacteristicPair (baumann (R : Subgroup H)))
    (hD : D.Universal.{u,u}) :
    (D.first.map (baumann (R : Subgroup H)).subtype).Normal ∨
      (D.second.map (baumann (R : Subgroup H)).subtype).Normal ∨
      (IsBlock L ∧ IsAlternatingBlock L 5 ∧
        L = ⁅L,elementaryAbelianMaxJ (R : Subgroup H)⁆ ∧
        (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U) := by
  obtain ⟨q',hq',hk',p',hR',hL',hp',he',hfix'⟩ :=
    exists_sylow_natural_marking R U q hq hk L hL p hp he hfix
  exact marked_source_normal_alternatives R hfit L hcomp hprod eL U q' hq' hk' hR' hL'
    p' hp' he' hfix' hJ D hD

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
