module
public import CFSG.Quasithin.ChapterC.Section06.RankOneSource
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
/-!
# The original alternating-five branch of C.6.1

The C.5 terminal identifies its marked core with the actual O₂(H).
Its four maximum elementary subgroups have exactly two R-invariant members.
The original normalizer obstruction and the two-group normalizer condition
therefore force [N_Λ(R):R]=2. Every element outside R exchanges those cores
and gives the original Thompson span and four-member family.

Source: Aschbacher--Smith C.6.1(1),(4),(5), printed pp.164--165.
The global overgroup conclusion in (6c) is a separate endgame.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K R L : Subgroup G}

theorem alternating_family_from_original
    (c : OriginalHypotheses H M K R R) (h : AlternatingPairSetup R K L)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let Q := H.pCoreIn 2
    let D := R ⊓ centralizer (K : Set G)
    (K ⊔ ChapterB.baumann R).pCoreIn 2 = Q ∧
      (frattini D).map D.subtype = ⊥ ∧
      D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ ∧
      Q = K.pCoreIn 2 ⊔ D ∧
      ChapterB.baumann R = elementaryAbelianMaxJ R ∧
      elementaryAbelianMaxJ R = Q ⊔ Q.map (MulAut.conj x⁻¹).toMonoidHom ∧
      {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} =
        {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom} ∧
      ∃ A : Subgroup G, ∃ r : G,
        r ∈ R ⊓ K ∧ r ∉ elementaryAbelianMaxJ R ∧ Q.relIndex A = 2 ∧
        elementaryAbelianMaxSubgroups R =
          {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom,A,A.map (MulAut.conj r⁻¹).toMonoidHom} := by
  have hRK := c.R_le_H.trans c.normalizes_residual
  have hH : H = K ⊔ R := c.residual_sup_sylow.symm
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have hshort : IsShort K := h.block.2.1
  have hfull := original_core_eq_module_centralizer c hshort
  have hp := h.source_C56_single_block_7 hRK H M R c.T_le c.R_normal hRK hH hno
    (hfull.trans (congrArg (fun A : Subgroup G => A.pCoreIn 2) hH)) x hx hi hnc
  have ht := h.single_block_full_centralizer_eq hRK H M R c.T_le c.R_normal hRK hH hno x hx hi hnc
  have hcore : (K ⊔ ChapterB.baumann R).pCoreIn 2 = H.pCoreIn 2 :=
    h.core.trans (ht.1.symm.trans hfull)
  have hphi := hp.2.1
  have hJ := hp.2.2.2.2.2.2.2.1
  refine ⟨hcore,?_,?_,?_,hJ,?_,?_,?_⟩
  · have hh := hphi
    rw [hp.2.2.2.1] at hh
    exact hh
  · simpa only [hp.2.2.2.1] using hp.2.2.1
  · simpa only [←hH,←hp.1,hp.2.2.2.1] using hp.2.2.2.2.1
  · rw [←hJ,←hcore]
    exact h.core_conjugate_span x (c.R_normal hx) hnc
  · simpa only [hcore] using (h.family_structure hRK x (c.R_normal hx) hnc hphi).2
  · have hh := hp.2.2.2.2.2.2.2.2
    rw [hcore] at hh
    simpa only [hJ] using hh

theorem alternating_normalizer_from_original
    (c : OriginalHypotheses H M K R R) (h : AlternatingPairSetup R K L)
    (Λ : Subgroup G) (hΛ : IsPGroup 2 Λ) (hRΛ : R < Λ)
    (hcontrol : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R → H ≤ normalizer (W : Set G) →
      Λ ⊓ normalizer (W : Set G) = R)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    R.relIndex (Λ ⊓ normalizer (R : Set G)) = 2 ∧
      ChapterB.baumann R = elementaryAbelianMaxJ R ∧
      H.pCoreIn 2 = K.pCoreIn 2 ⊔ (R ⊓ centralizer (K : Set G)) ∧
      ∀ y ∈ Λ ⊓ normalizer (R : Set G), y ∉ R →
        elementaryAbelianMaxJ R = H.pCoreIn 2 ⊔
          (H.pCoreIn 2).map (MulAut.conj y⁻¹).toMonoidHom ∧
        ∃ A : Subgroup G, ∃ r : G,
          r ∈ R ⊓ K ∧ r ∉ elementaryAbelianMaxJ R ∧ (H.pCoreIn 2).relIndex A = 2 ∧
          elementaryAbelianMaxSubgroups R =
            {H.pCoreIn 2,(H.pCoreIn 2).map (MulAut.conj y⁻¹).toMonoidHom,
              A,A.map (MulAut.conj r⁻¹).toMonoidHom} := by
  obtain ⟨hcore,hphi,hDD,hprod,hJ,hspan,hfamily,hfour⟩ :=
    alternating_family_from_original c h hi x hx hnc
  let Q := H.pCoreIn 2
  let N₀ := Λ ⊓ normalizer (R : Set G)
  have hQR : Q ≤ R := by
    simpa only [c.sylow_image] using pCoreIn_le_sylow H c.sylow
  have hQ : Q ≠ ⊥ := by
    intro he
    have hu : sourceModule K ≤ Q := le_sup_left.trans_eq (h.product.symm.trans hcore)
    exact moduleLayer_ne_bot h.block.2.1 (bot_unique (he ▸ hu))
  have hnQ : H ≤ normalizer (Q : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hstab := hcontrol Q hQ hQR hnQ
  have hRN₀ : R ≤ N₀ := le_inf hRΛ.le R.le_normalizer
  have hpair (g : G) (hg : g ∈ normalizer (R : Set G)) :
      Q.map (MulAut.conj g).toMonoidHom = Q ∨
        Q.map (MulAut.conj g).toMonoidHom = Q.map (MulAut.conj x⁻¹).toMonoidHom := by
    let f := MulAut.conj g
    have hQfam : Q ∈ elementaryAbelianMaxSubgroups R ∧ R ≤ normalizer (Q : Set G) := by
      change Q ∈ {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)}
      rw [hfamily]
      exact Set.mem_insert _ _
    have he : R.map f.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp hg
    have hmax := (maxFamily_map_injective_iff f.toMonoidHom f.injective R Q).mpr hQfam.1
    rw [he] at hmax
    have hnormal : R ≤ normalizer (Q.map f.toMonoidHom : Set G) := by
      rw [←he]
      exact (map_mono hQfam.2).trans (le_normalizer_map f.toMonoidHom)
    have hh : Q.map f.toMonoidHom ∈
        {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} := ⟨hmax,hnormal⟩
    rw [hfamily] at hh
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hh
  let : Group.IsNilpotent Λ := hΛ.isNilpotent
  have hproper : R.subgroupOf Λ < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => hRΛ.not_ge (subgroupOf_eq_top.mp he))
  obtain ⟨z,hzn,hzr⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (R.subgroupOf Λ) hproper)
  have hzN : (z : G) ∈ normalizer (R : Set G) := by
    rwa [←subgroupOf_normalizer_eq hRΛ.le] at hzn
  have hm : Q.map (MulAut.conj (z : G)).toMonoidHom ≠ Q := by
    intro he
    exact hzr (hstab ▸ ⟨z.property,mem_normalizer_iff_map_conj_eq.mpr he⟩)
  have hiN₀ := normalizer_relIndex_eq_two_of_pair N₀ Q
    (Q.map (MulAut.conj x⁻¹).toMonoidHom) (fun g hg => hpair g hg.2)
    z ⟨z.property,hzN⟩ hm
  have hs : N₀ ⊓ normalizer (Q : Set G) = R := by
    apply le_antisymm
    · exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hstab.le
    · exact le_inf hRN₀ (hstab ▸ inf_le_right)
  refine ⟨?_,hJ,hprod,?_⟩
  · change R.relIndex N₀ = 2
    rw [←hs,inf_relIndex_left]
    exact hiN₀
  · intro y hy hyr
    have hmove : Q.map (MulAut.conj y⁻¹).toMonoidHom ≠ Q := by
      intro he
      have hn : y⁻¹ ∈ normalizer (Q : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
      have hn' : y ∈ normalizer (Q : Set G) := by
        simpa only [inv_inv] using (normalizer (Q : Set G)).inv_mem hn
      exact hyr (hstab ▸ (show y ∈ Λ ⊓ normalizer (Q : Set G) from ⟨hy.1,hn'⟩))
    have he := (hpair y⁻¹ ((normalizer (R : Set G)).inv_mem hy.2)).resolve_left hmove
    change elementaryAbelianMaxJ R = Q ⊔ Q.map (MulAut.conj y⁻¹).toMonoidHom ∧ _
    rw [he]
    exact ⟨hspan,hfour⟩

end CFSG.Quasithin.ChapterC.Section06
