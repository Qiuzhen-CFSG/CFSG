module
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.TwoKernel
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerConjugacy

/-!
# Aligning the original nonsingular local residual

The original local normalization makes O2(K_v) normalize L_v. After the
checked Sylow conjugator sends K_v onto L, its image of L_v is normalized
by O2(L). The original L_v is normalized by the same core, which centralizes
V. Their actual A6 sections in L/O2(L) are conjugate in A8, and two-residual
uniqueness lifts that conjugacy through O2(L).

Adjusting the conjugator by an element of L therefore fixes the literal
L_v while still sending K_v onto L and K_v S onto LT. The final export
applies this to the preferred escaping point and the original C_V(L).
This supplies the local-residual alignment in 12.6.16(1); alignment of R_v
and the final normalizer contradiction are separate steps. Neither 12.6.2
nor 12.6.23 is asserted. Earlier invariance/TI retain qt-d-1222-source and
final source discharge remains with qt-d-12634-source.
Source: Aschbacher--Smith, 12.6.4--5 and 12.6.16--17, printed pp.824,826--827,
combined manuscript of 1 March 2004.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The canonical two-core normalizes the original local two-residual. -/
theorem SourceHypothesis.nonsingular_core_normalizes_local_residual
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4) :
    (Kv (v : G)).pCoreIn 2 ≤ normalizer (Lv L (v : G) : Set G) := by
  obtain ⟨S,hTS,hn,_,_⟩ := H.local_normalization_of_nonsingular D v hv hs hi
  let P := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ P
  have hJG : J ≤ Gv (v : G) := sup_le (Kv_le_Gv _) (map_subtype_le _)
  have hJN : J ≤ normalizer (Kv (v : G) : Set G) :=
    hJG.trans ((normal_subgroupOf_iff_le_normalizer (Kv_le_Gv _)).mp (Kv_normalIn_Gv _))
  exact (pCoreIn_mono_of_normalizes (show Kv (v : G) ≤ J from le_sup_left) hJN).trans
    ((core_le_R_of_sylow L (Kv (v : G)) (v : G) S (Kv_le_Gv _)).trans hn)

/-- The original local residual and its conjugated copy are conjugate inside L. -/
theorem SourceHypothesis.nonsingular_local_residual_alignment
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (g : G) (hg : (Kv (v : G)).map (MulAut.conj g).toMonoidHom = L) :
    ∃ l : L, ((Lv L (v : G)).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (l : G)).toMonoidHom = Lv L (v : G) := by
  let c := (MulAut.conj g).toMonoidHom
  let A := (Lv L (v : G)).map c
  have hLK := (H.nonsingular_canonical_component D v hv).2.1
  have hAL : A ≤ L := (map_mono hLK).trans_eq hg
  let A₀ := A.subgroupOf L
  let B₀ := (Lv L (v : G)).subgroupOf L
  let a : A₀ ≃* Lv L (v : G) := (subgroupOfEquivOfLe hAL).trans
    ((Lv L (v : G)).equivMapOfInjective c (MulAut.conj g).injective).symm
  let b : B₀ ≃* Lv L (v : G) := subgroupOfEquivOfLe (Lv_le_L L (v : G))
  have hp : IsPPerfect 2 (Lv L (v : G)) := isPPerfect_embedded_pResidual 2 (CLv L (v : G))
  obtain ⟨e⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  have hLnA : L.pCoreIn 2 ≤ normalizer (A : Set G) := by
    have hh := map_mono (f := c) (H.nonsingular_core_normalizes_local_residual D v hv hs hi)
    rw [map_pCoreIn_of_injective 2 _ c (MulAut.conj g).injective,hg] at hh
    exact hh.trans ((Lv L (v : G)).le_normalizer_map c)
  have hLnB : L.pCoreIn 2 ≤ normalizer (Lv L (v : G) : Set G) := by
    apply (show L.pCoreIn 2 ≤ Mv L (v : G) from ?_).trans (Mv_le_normalizer_Lv L _)
    refine le_inf ((pCoreIn_le 2 L).trans L.le_normalizer) ?_
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (H.centralizer_eq_core.symm ▸ hx).2 (v : G) v.property).symm
  let f := D.actorMap
  have hf : f.ker = pCore 2 L := D.actorMap_ker H.chosen H.source.quasisimple
  have hk : IsPGroup 2 f.ker := hf ▸ pCore_isPGroup
  have hnA : f.ker ≤ normalizer (A₀ : Set L) := by
    rw [hf,←subgroupOf_normalizer_eq hAL]
    exact fun x hx => hLnA (mem_map_of_mem L.subtype hx)
  have hnB : f.ker ≤ normalizer (B₀ : Set L) := by
    rw [hf,←subgroupOf_normalizer_eq (Lv_le_L L (v : G))]
    exact fun x hx => hLnB (mem_map_of_mem L.subtype hx)
  obtain ⟨l,hl⟩ := Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.six_sections_conjugate
    f D.actorMap_surjective hk A₀ B₀
    (hp.of_surjective a.symm.toMonoidHom a.symm.surjective)
    (hp.of_surjective b.symm.toMonoidHom b.symm.surjective) hnA hnB
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e)
    ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans e)
  refine ⟨l,?_⟩
  have hh := congrArg (Subgroup.map L.subtype) hl
  rw [map_subgroupOf_eq_of_le (Lv_le_L L (v : G))] at hh
  have hc : L.subtype.comp (MulAut.conj l).toMonoidHom =
      (MulAut.conj (l : G)).toMonoidHom.comp L.subtype := by ext x; rfl
  rw [map_map,hc,←map_map,map_subgroupOf_eq_of_le hAL] at hh
  exact hh

/-- Adjust the chosen conjugator inside L, preserving the image of K_v S. -/
theorem SourceHypothesis.nonsingular_aligned_conjugator
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (S : Subgroup G) (g : G)
    (hg : (Kv (v : G)).map (MulAut.conj g).toMonoidHom = L)
    (hJ : (Kv (v : G) ⊔ S).map (MulAut.conj g).toMonoidHom = LT T L) :
    ∃ k : G, (Kv (v : G)).map (MulAut.conj k).toMonoidHom = L ∧
      (Kv (v : G) ⊔ S).map (MulAut.conj k).toMonoidHom = LT T L ∧
      (Lv L (v : G)).map (MulAut.conj k).toMonoidHom = Lv L (v : G) := by
  obtain ⟨l,hl⟩ := H.nonsingular_local_residual_alignment D v hv hs hi g hg
  have hc : (MulAut.conj ((l : G)*g)).toMonoidHom =
      (MulAut.conj (l : G)).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  have hL : L.map (MulAut.conj (l : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer l.property)
  have hLT : (LT T L).map (MulAut.conj (l : G)).toMonoidHom = LT T L :=
    mem_normalizer_iff_map_conj_eq.mp ((LT T L).le_normalizer (mem_sup_left l.property))
  refine ⟨(l : G)*g,?_,?_,?_⟩
  · rw [hc,←map_map,hg,hL]
  · rw [hc,←map_map,hJ,hLT]
  · rw [hc,←map_map]
    exact hl

/-- Preferred-point application with the original local residual aligned. -/
theorem SourceHypothesis.exists_preferred_nonsingular_aligned_conjugacy_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
      V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
      ¬ IsQuasisimple (Kv (w : G)) ∧
      (normalizer (Rv T L (w : G) : Set G) ≤ M L →
        ∃ S : Sylow 2 (Gv (w : G)), ∃ k : G,
          let S₀ := (S : Subgroup (Gv (w : G))).map (Gv (w : G)).subtype
          Tv T (w : G) ≤ S₀ ∧
          (Kv (w : G)).map (MulAut.conj k).toMonoidHom = L ∧
          (Kv (w : G) ⊔ S₀).map (MulAut.conj k).toMonoidHom = LT T L ∧
          (Lv L (w : G)).map (MulAut.conj k).toMonoidHom = Lv L (w : G)) := by
  obtain ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,hm⟩ :=
    H.exists_preferred_nonsingular_normalizer_conjugacy_of_fixed D hTV hTI hz v hv he
  refine ⟨w,hw,he,hs,hi,hlt,hnot,hline,hnq,fun hNM => ?_⟩
  obtain ⟨S,g,hTS,_,_,_,hK,hJ,_⟩ := hm hNM
  obtain ⟨k,hk,hkJ,hkA⟩ := H.nonsingular_aligned_conjugator D w hw hs hi _ g hK hJ
  exact ⟨S,k,hTS,hk,hkJ,hkA⟩
end CFSG.Quasithin.Chapter12.Section06
