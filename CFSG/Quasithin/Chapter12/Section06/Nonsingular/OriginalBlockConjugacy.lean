module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalBlockModel
public import Theory.GroupTheory.Commutator.ConjugateIndexTwo

/-!
# The aligned original blocks and their common commutator line

An ambient Sylow centralizing the original nonsingular point gives the
source conjugator carrying K_v to L and K_v S to LT. After aligning L_v,
the actual A6 centralizer in LT/Q forces R=R_v and fixes R_v under that
same conjugator. The contrary normalizer hypothesis is not needed.

If V commuted with its inverse conjugate, their product would lie in Q
and be normalized by L, R_v and K_v. The original [Q,L]=V identity and
local uniqueness exclude this. The index-two mutual-action argument then
shows that their commutator is exactly [V,R_v], has order two, and is
fixed by the conjugator. Its intersection with the original C_V(L) is
trivial, so projection to the original orthogonal quotient is faithful.

The preferred-point application constructs every block and alignment
premise, retaining only the source's ambient Sylow hypothesis. Identifying
this line in the original weight-two orbit and finishing 12.6.16(2) remain;
so do the remaining HS/J4 exclusions, canonical-module arguments, splitting
and fixed-space elimination. Neither 12.6.2 nor 12.6.23 is asserted.
Earlier invariance/TI retain qt-d-1222-source and final discharge remains
with qt-d-12634-source. Source: Aschbacher--Smith 12.6.16(2), printed
pp.826--827, combined manuscript of 1 March 2004.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Strict core enlargement aligns the literal R and R_v through the original A6 section. -/
theorem SourceHypothesis.nonsingular_residual_alignment_of_core_lt
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (hlt : Q T L < Rv T L (v : G))
    (S : Sylow 2 (Gv (v : G)))
    (hTS : Tv T (v : G) ≤ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype)
    (g : G)
    (hJ : (Kv (v : G) ⊔ (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype).map
      (MulAut.conj g).toMonoidHom = LT T L)
    (hA : (Lv L (v : G)).map (MulAut.conj g).toMonoidHom = Lv L (v : G)) :
    R L (Kv (v : G)) ((S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype) (v : G) =
      Rv T L (v : G) ∧
    (Rv T L (v : G)).map (MulAut.conj g).toMonoidHom = Rv T L (v : G) := by
  let P := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
  let J := Kv (v : G) ⊔ P
  let R₀ := R L (Kv (v : G)) P (v : G)
  let c := (MulAut.conj g).toMonoidHom
  obtain ⟨e,_,_⟩ := H.nonsingular_original_symmetric_quotient D v hv hlt
  have hC := H.nonsingular_relative_core_centralizer_eq D v hv e hlt
  obtain ⟨ea⟩ := D.nonsingular_local_quotient H.chosen H.source.quasisimple v hv
  have hLK := (H.nonsingular_canonical_component D v hv).2.1
  obtain ⟨P₀,hP₀⟩ := hs.restrict
    (show Tv T (v : G) ≤ LT T L ⊓ Gv (v : G) from inf_le_inf le_sup_right le_rfl)
    (show LT T L ⊓ Gv (v : G) ≤ Mv L (v : G) from
      inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)
  have hR := (nonsingular_normalization_of_A6 T L (Kv (v : G)) (v : G)
    H.chosen.sylow_normalizes_component (Kv_le_Gv _) hLK ea P₀ hP₀ hi S hTS).2.2
  have hRvR : Rv T L (v : G) ≤ R₀ := by
    rw [←R_inf_Tv_eq_Rv T L (Kv (v : G)) P (v : G)
      H.chosen.sylow_normalizes_component hLK hTS P₀ hP₀
      (Lv_coreQuotient_center_eq_bot_of_A6 L (v : G) ea)]
    exact inf_le_left
  have hRC : R₀ ≤ coreQuotientCentralizer (Lv L (v : G)) := hR.le.trans inf_le_right
  have hmap : R₀.map c ≤ Rv T L (v : G) := by
    apply le_trans ?_ hC.le
    apply le_inf ((map_mono (show R₀ ≤ J from inf_le_left.trans le_sup_right)).trans_eq hJ)
    rintro _ ⟨r,hr,rfl⟩
    have hh := (mem_coreQuotientCentralizer_iff_map c (Lv L (v : G))
      (IsPGroup.ker_isPGroup_of_injective (MulAut.conj g).injective)
      (coreQuotientCentralizer_le_normalizer _ (hRC hr))).mp (hRC hr)
    rwa [hA] at hh
  have heq : Rv T L (v : G) = R₀ := eq_of_le_of_card_ge hRvR (by
    have hh := card_le_of_le hmap
    rwa [card_map_of_injective (MulAut.conj g).injective] at hh)
  refine ⟨heq.symm,?_⟩
  rw [←heq] at hmap
  exact eq_of_le_of_card_ge hmap (by rw [card_map_of_injective (MulAut.conj g).injective])

/-- The original ambient Sylow gives a conjugator preserving the literal R_v,
with no contrary normalizer assumption. -/
theorem SourceHypothesis.nonsingular_full_alignment_of_ambient_sylow
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V) (hv : D.Nonsingular v)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hz : ZV L V ≠ ⊥)
    (hnot : ¬ IsQuasisimple (Kv (v : G)))
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4)
    (he : ¬ Kv (v : G) ≤ M L)
    (P : Sylow 2 G) (hPG : (P : Subgroup G) ≤ Gv (v : G))
    (hTP : Tv T (v : G) ≤ (P : Subgroup G)) :
    ∃ g : G, (Kv (v : G)).map (MulAut.conj g).toMonoidHom = L ∧
      (Kv (v : G) ⊔ (P : Subgroup G)).map (MulAut.conj g).toMonoidHom = LT T L ∧
      (Lv L (v : G)).map (MulAut.conj g).toMonoidHom = Lv L (v : G) ∧
      (Rv T L (v : G)).map (MulAut.conj g).toMonoidHom = Rv T L (v : G) ∧
      R L (Kv (v : G)) (P : Subgroup G) (v : G) = Rv T L (v : G) ∧
      g ∉ M L := by
  have hn := H.nonsingular_normalizer_escape_of_not_quasisimple D v hv hTV hnot hs hi he
  have hlt : Q T L < Rv T L (v : G) := lt_of_le_of_ne (Q_le_Rv H.chosen v)
    (fun h => hn (h ▸ H.core_normalizer_le))
  have hJT := H.nonsingular_thompson_not_le_core_of_not_quasisimple D v hv hTV hnot hs hi he
  have hgen := (H.nonsingular_thompson_generation D v hv hTV hs hJT).2.2
  have hLZ := H.component_centralizes_Z_of_thompson_generation D hz hgen
  obtain ⟨g,hg,_,_,hgK⟩ := H.nonsingular_sylow_component_conjugacy D hLZ v hv P hPG
  have hgJ : (Kv (v : G) ⊔ (P : Subgroup G)).map (MulAut.conj g).toMonoidHom = LT T L := by
    rw [Subgroup.map_sup,hgK,hg]
    rfl
  obtain ⟨k,hk,hkJ,hkA⟩ := H.nonsingular_aligned_conjugator D v hv hs hi _ g hgK hgJ
  let S : Sylow 2 (Gv (v : G)) := P.subtype hPG
  have hS : (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype = (P : Subgroup G) :=
    map_subgroupOf_eq_of_le hPG
  obtain ⟨hR,hkR⟩ := H.nonsingular_residual_alignment_of_core_lt D v hv hs hi hlt S
    (hS.symm ▸ hTP) k (hS.symm ▸ hkJ) hkA
  rw [hS] at hR
  refine ⟨k,hk,hkJ,hkA,hkR,hR,?_⟩
  intro hkM
  have hL := mem_normalizer_iff_map_conj_eq.mp hkM
  have heq : Kv (v : G) = L := map_injective (MulAut.conj k).injective (hk.trans hL.symm)
  exact he (heq ▸ L.le_normalizer)

omit [IsElementaryAbelian 2 V] in
/-- In the original block branch an aligned conjugate of V cannot commute
with V: their product would be normalized by both L and the escaping K_v. -/
theorem SourceHypothesis.nonsingular_aligned_block_noncommuting
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hshort : ChapterC.IsShort L)
    (v : V) (he : ¬ Kv (v : G) ≤ M L)
    (hjoin : L ⊔ Rv T L (v : G) = LT T L)
    (g : G)
    (hK : (Kv (v : G)).map (MulAut.conj g).toMonoidHom = L)
    (hR : (Rv T L (v : G)).map (MulAut.conj g).toMonoidHom = Rv T L (v : G)) :
    ⁅V,V.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≠ ⊥ := by
  let c := (MulAut.conj g).toMonoidHom
  let d := (MulAut.conj g⁻¹).toMonoidHom
  let A := V.map d
  let W := V ⊔ A
  have hcancel (B : Subgroup G) : (B.map d).map c = B := by
    rw [map_map]
    have hh : c.comp d = MonoidHom.id G := by
      ext x
      simp [c,d,MulAut.conj_apply,mul_assoc]
    rw [hh,map_id]
  have hRi : (Rv T L (v : G)).map d = Rv T L (v : G) := by
    apply map_injective (f := c) (MulAut.conj g).injective
    rw [hcancel,hR]
  have hVR : V ≤ Rv T L (v : G) := H.chosen.le_core.trans (Q_le_Rv H.chosen v)
  have hAR : A ≤ Rv T L (v : G) := (map_mono hVR).trans_eq hRi
  have hRJ : Rv T L (v : G) ≤ LT T L := (pCoreIn_le 2 _).trans inf_le_left
  have hRN : Rv T L (v : G) ≤ normalizer (V : Set G) :=
    hRJ.trans (sup_le H.chosen.normalizes hTV)
  have hRAN : Rv T L (v : G) ≤ normalizer (A : Set G) := by
    rw [←hRi]
    exact (map_mono hRN).trans (V.le_normalizer_map d)
  have hWN : Rv T L (v : G) ≤ normalizer (W : Set G) :=
    (le_inf hRN hRAN).trans (normalizer_inf_normalizer_le_normalizer_sup V A)
  intro hc
  have hAc : A ≤ centralizer (V : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (by rw [commutator_comm]; exact hc)
  have hAQ : A ≤ Q T L := (le_inf (hAR.trans hRJ) hAc).trans_eq
    (H.join_centralizer_eq_core hTV)
  have hWQ : W ≤ Q T L := sup_le H.chosen.le_core hAQ
  have hmove := H.original_core_commutator_of_short hshort
  have hLN : L ≤ normalizer (W : Set G) := le_normalizer_iff_commutator_le_left.mpr
    (((commutator_mono hWQ le_rfl).trans_eq hmove).trans le_sup_left)
  have hVgR : V.map c ≤ Rv T L (v : G) := (map_mono hVR).trans_eq hR
  have hVgC : V.map c ≤ centralizer (V : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    have hh := congrArg (map c) hc
    rw [map_commutator,hcancel,Subgroup.map_bot] at hh
    exact hh
  have hWgQ : W.map c ≤ Q T L := by
    rw [Subgroup.map_sup,hcancel]
    exact sup_le ((le_inf (hVgR.trans hRJ) hVgC).trans_eq
      (H.join_centralizer_eq_core hTV)) H.chosen.le_core
  have hKN : Kv (v : G) ≤ normalizer (W : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    apply (map_le_map_iff_of_injective (f := c) (MulAut.conj g).injective).mp
    rw [map_commutator,hK]
    apply ((commutator_mono hWgQ le_rfl).trans_eq hmove).trans
    rw [Subgroup.map_sup,hcancel]
    exact le_sup_right
  have hWne : W ≠ ⊥ := fun h => H.chosen.ne_bot
    (bot_unique ((show V ≤ W from le_sup_left).trans h.le))
  have hN : normalizer (W : Set G) ≤ M L :=
    H.chosen.normal_subgroup_normalizer_le H.source.toHypothesis1221
      ((sup_le hVR hAR).trans hRJ) hWne
      (by change LT T L ≤ _; rw [←hjoin]; exact sup_le hLN hWN)
  exact he (hKN.trans hN)


/-- The original aligned pair has the full R_v commutator, an order-two
subgroup fixed pointwise by its conjugator. -/
theorem SourceHypothesis.nonsingular_aligned_block_commutator_line
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hshort : ChapterC.IsShort L)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Kv (v : G) ≤ M L)
    (hlt : Q T L < Rv T L (v : G))
    (g : G)
    (hK : (Kv (v : G)).map (MulAut.conj g).toMonoidHom = L)
    (hR : (Rv T L (v : G)).map (MulAut.conj g).toMonoidHom = Rv T L (v : G)) :
    ⁅V,V.map (MulAut.conj g⁻¹).toMonoidHom⁆ = ⁅V,Rv T L (v : G)⁆ ∧
      Nat.card (⁅V,Rv T L (v : G)⁆ : Subgroup G) = 2 ∧
      g ∈ centralizer (↑(⁅V,Rv T L (v : G)⁆ : Subgroup G) : Set G) := by
  have hRJ : Rv T L (v : G) ≤ LT T L := (pCoreIn_le 2 _).trans inf_le_left
  exact conjugate_commutator_card_two_and_fixed V (Q T L) (Rv T L (v : G))
    (H.chosen.le_core.trans hlt.le) (hRJ.trans (sup_le H.chosen.normalizes hTV))
    hlt.le H.chosen.core_centralizes (H.nonsingular_original_core_index D v hv hlt) g hR
    (H.nonsingular_aligned_block_noncommuting hTV hshort v he
      (H.nonsingular_original_join D v hv hlt) g hK hR)

/-- A subgroup fixed by an element outside M has no nonidentity original
global-fixed vector. This retains the central denominator of the marked module. -/
theorem SourceHypothesis.fixed_by_outside_inf_global_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (W : Subgroup G) (g : G) (hg : g ∉ M L)
    (hfix : g ∈ centralizer (W : Set G)) : W ⊓ ZV L V = ⊥ := by
  apply bot_unique
  rintro x ⟨hxW,hxZ⟩
  change x = 1
  by_contra hne
  have hXZ : zpowers x ≤ ZV L V := zpowers_le.mpr hxZ
  have hXne : zpowers x ≠ ⊥ := fun h => hne (mem_bot.mp (h ▸ mem_zpowers x))
  have hn : normalizer (zpowers x : Set G) ≤ M L :=
    H.chosen.normal_subgroup_normalizer_le H.source.toHypothesis1221
      (hXZ.trans (inf_le_left.trans (H.chosen.le_component.trans le_sup_left))) hXne
      (((D.join_centralizes_fixed H.chosen hTV).trans (centralizer_le hXZ)).trans
        (Subgroup.centralizer_le_normalizer _))
  apply hg
  apply hn
  rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
  congr 1
  change g*x*g⁻¹ = x
  rw [←hfix x hxW,mul_inv_cancel_right]

/-- The common-line reduction of source12.6.16(2), at the preferred
escaping point. The ambient Sylow premise is the source's explicit hypothesis. -/
theorem SourceHypothesis.exists_preferred_nonsingular_block_line_of_fixed
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ChapterC.IsAlternatingBlock L 8 ∧
      ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
        Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
        (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
        Lv L (w : G) < Kv (w : G) ∧ ¬ Kv (w : G) ≤ M L ∧
        V ⊓ centralizer (Kv (w : G) : Set G) = zpowers (w : G) ∧
        ¬ IsQuasisimple (Kv (w : G)) ∧
        ∀ P : Sylow 2 G, (P : Subgroup G) ≤ Gv (w : G) →
          Tv T (w : G) ≤ (P : Subgroup G) →
          ∃ g : G, (Kv (w : G)).map (MulAut.conj g).toMonoidHom = L ∧
            (Kv (w : G) ⊔ (P : Subgroup G)).map (MulAut.conj g).toMonoidHom = LT T L ∧
            (Lv L (w : G)).map (MulAut.conj g).toMonoidHom = Lv L (w : G) ∧
            (Rv T L (w : G)).map (MulAut.conj g).toMonoidHom = Rv T L (w : G) ∧
            R L (Kv (w : G)) (P : Subgroup G) (w : G) = Rv T L (w : G) ∧
            g ∉ M L ∧
            ⁅V,V.map (MulAut.conj g⁻¹).toMonoidHom⁆ = ⁅V,Rv T L (w : G)⁆ ∧
            Nat.card (⁅V,Rv T L (w : G)⁆ : Subgroup G) = 2 ∧
            g ∈ centralizer (↑(⁅V,Rv T L (w : G)⁆ : Subgroup G) : Set G) ∧
            ⁅V,Rv T L (w : G)⁆ ⊓ ZV L V = ⊥ := by
  obtain ⟨_,hb,_,_,w,hw,he,hs,hi,hlt,hnot,hline,hnq,hn,hr,hidx,hjoin,_⟩ :=
    H.exists_preferred_nonsingular_original_blocks_of_fixed D hTV hTI hz v hv he
  refine ⟨hb,w,hw,he,hs,hi,hlt,hnot,hline,hnq,fun P hPG hTP => ?_⟩
  obtain ⟨g,hgK,hgJ,hgA,hgR,hR,hgM⟩ := H.nonsingular_full_alignment_of_ambient_sylow
    D w hw hTV hz hnq hs hi hnot P hPG hTP
  obtain ⟨hcomm,hcard,hfix⟩ := H.nonsingular_aligned_block_commutator_line D hTV hb.2.1
    w hw hnot hr g hgK hgR
  exact ⟨g,hgK,hgJ,hgA,hgR,hR,hgM,hcomm,hcard,hfix,
    H.fixed_by_outside_inf_global_fixed D hTV _ g hgM hfix⟩

end CFSG.Quasithin.Chapter12.Section06
