module
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.ExceptionalAmbient

/-!
# Relative exceptional selection on the unchanged Baumann subgroup

In the moving branch, the unique best offender of the faithful A₇ four-space
identifies both Thompson images. Since the action kernel meets the larger
Sylow in O₂(G), its Baumann subgroup already lies in R. Thus Baum(R)=Baum(T),
and the existing A₅-preimage construction and cubic-kernel propagation apply
on precisely the prescribed Baumann subgroup. The centralizing branch uses
B.2.10 directly on R.

Source: Aschbacher--Smith C.1.24(a), pp.130--131, with O₂(G) ≤ R ≤ T.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Exceptional
open ChapterC.RankOne.SevenSource
open ChapterC.RankOne.Alternating.SevenSource
open Representation.BinaryAlternatingSevenControl
variable {G : Type*} [Group G] [Finite G]
local notation "A7" => alternatingGroup (Fin 7)

/-- The exceptional moving radical and an overlying Sylow have the same
literal Baumann subgroup; no Sylow assertion about R is needed. -/
theorem baumann_eq_sylow
    (U R : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* A7) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (hd : Module.finrank (ZMod 2) (Additive U) = 4)
    (T : Sylow 2 G) (hUR : U ≤ R) (hQR : pCore 2 G ≤ R) (hRT : R ≤ T)
    (hTK : (T : Subgroup G) ⊓ q.ker ≤ pCore 2 G)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker) :
    ChapterB.baumann R = ChapterB.baumann (T : Subgroup G) := by
  have hJT : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker := by
    intro hh
    have hl : elementaryAbelianMaxJ (T : Subgroup G) ≤ R :=
      (le_inf (sSup_le fun _ hA => hA.1) hh).trans (hTK.trans hQR)
    have he := elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) R hl hRT
    exact hJ (he.trans_le hh)
  obtain ⟨A,hAT,hA,hJA,hBA⟩ :=
    exceptional_thompson_baumann_images U q hq hk hd T (hUR.trans hRT) hJT
  have hJR : (elementaryAbelianMaxJ R).map q = A := by
    apply ChapterB.thompson_image_of_unique_maximum_image R q A hJ
    intro B hB hne
    exact best_unique_in_sylow (NormalElementaryQuotient.representation U q hq hk)
      (NormalElementaryQuotient.representation_injective U q hq hk) hd
      (T.mapSurjective (f := q) hq) (map_mono (hB.1.trans hRT)) hAT
      (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
        U q hq hk R B hUR hB hne) hA
  have hBR : ChapterB.baumann (T : Subgroup G) ≤ R := by
    intro b hb
    have hqb : q b ∈ R.map q := by
      have hh : q b ∈ (elementaryAbelianMaxJ R).map q :=
        hJR.symm ▸ (hBA ▸ mem_map_of_mem q hb)
      exact map_mono (sSup_le fun _ hA => hA.1) hh
    obtain ⟨r,hr,he⟩ := hqb
    have hbr : b * r⁻¹ ∈ R := hQR (hTK ⟨
      (T : Subgroup G).mul_mem (show b ∈ (T : Subgroup G) from hb.1)
        ((T : Subgroup G).inv_mem (hRT hr)), by
      change q (b * r⁻¹) = 1
      rw [map_mul,map_inv,he,mul_inv_cancel]⟩)
    simpa only [inv_mul_cancel_right] using R.mul_mem hbr hr
  exact (ChapterB.lemma_B_2_3_4 (T : Subgroup G) R hBR hRT).symm

private theorem alternating_twoCore_eq_bot : pCore 2 A7 = ⊥ := by
  let : IsSimpleGroup A7 := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 A7) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 2 A7 := by
      have ht : IsPGroup 2 (⊤ : Subgroup A7) := h ▸ pCore_isPGroup
      exact ht.of_surjective (Subgroup.topEquiv (G := A7)).toMonoidHom
        (Subgroup.topEquiv (G := A7)).surjective
    obtain ⟨n,hn⟩ := hp.exists_card_dvd_pow
    have hc : Nat.card A7 = 2520 := by
      rw [nat_card_alternatingGroup,Nat.card_fin]
      decide
    rw [hc] at hn
    have h3 := dvd_trans (by norm_num : 3 ∣ 2520) hn
    exact False.elim (by simpa using (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h3))

/-- C.1.24(a)'s exceptional branch for the original radical R. The A₅
preimage and the possible central cubic kernel are handled by the Sylow
construction after proving equality of the actual Baumann subgroups. -/
theorem relative_selection
    (L U R : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hL : L.IsCComponent) (hf : generalizedFitting G = pCore 2 G)
    (hfL : generalizedFitting L = pCore 2 L) (T : Sylow 2 G)
    (hprod : ∀ g:G, ∃ l∈L, ∃ t∈(T : Subgroup G), l*t=g)
    (q : G →* A7) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) (hLq : L.map q = ⊤)
    (hd : Module.finrank (ZMod 2) (Additive U) = 4)
    (hm : ⁅U,L⁆ ≠ ⊥) (hQR : pCore 2 G ≤ R) (hRT : R ≤ T) :
    (∃ D : Subgroup (ChapterB.baumann R), D.Characteristic ∧ D ≠ ⊥ ∧
      (D.map (ChapterB.baumann R).subtype).Normal) ∨ ChapterC.IsBlock L := by
  have hUR : U ≤ R :=
    (show U ≤ pCore 2 G from le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩).trans hQR
  have hi := ChapterB.lemma_B_2_10_two U R q hq hk T hQR hRT
    alternating_twoCore_eq_bot L (Or.inl ⟨hL,inferInstance⟩) hm hprod
  by_cases hJ : elementaryAbelianMaxJ R ≤ q.ker
  · have hn := (ChapterB.lemma_B_2_10_centralizing U R hUR hQR hi.2.1
      (by simpa only [ChapterB.thompsonJ_zero,hk] using hJ)).2.2.2
    have hRne : R ≠ ⊥ := by
      intro hr
      have hu : U = ⊥ := le_bot_iff.mp (hUR.trans_eq hr)
      exact hm (by rw [hu,commutator_bot_left])
    let : Nontrivial (ChapterB.baumann R) := (nontrivial_iff_ne_bot _).mpr
      (ChapterC.RankOne.SymmetricSix.baumann_ne_bot R (T.isPGroup'.to_le hRT) hRne)
    exact Or.inl ⟨⊤,inferInstance,top_ne_bot,by
      simpa only [←MonoidHom.range_eq_map,range_subtype] using hn⟩
  · have hQT : pCore 2 G ≤ T := pCore_isPGroup.le_sylow_of_normal T
    have hti := ChapterB.lemma_B_2_10_two U (T : Subgroup G) q hq hk T hQT le_rfl
      alternating_twoCore_eq_bot L (Or.inl ⟨hL,inferInstance⟩) hm hprod
    have hb := baumann_eq_sylow U R q hq hk hd T hUR hQR hRT
      (by simpa only [hk] using hti.2.1.ge) hJ
    rw [hb]
    exact normal_characteristic_or_block_of_exceptional_seven
      L U hL hf hfL T hprod q hq hk hLq hd hm
end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel.Exceptional
