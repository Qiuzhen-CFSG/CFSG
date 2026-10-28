module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondSolvableExclusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondKernelAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondThompsonAt
public import CFSG.Quasithin.ChapterF.Section06.Elementary.SolvableThompsonAction

/-!
This guarded version uses earlier structure only at the original G,T.
All literal residuals, quotient maps and original source hypotheses are retained.

# Nonsolvability of the actual second join

Apply the reduced Goldschmidt action argument to the literal pair
L₁T,Y₂T. The preceding source construction supplies locality, reducedness,
the full action kernel, L₁=[L₁,J(T)], and failure of Y₂ to normalize L₁.
All residuals and the ordinary Thompson subgroup are transported through
the same inclusion into the actual second join. Its local SQTK structure
supplies the required three-rank bound.

This excludes every solvable second join without a supplied quotient
model or a Fitting-centralizer callback. N_G(L)=LT remains a genuine earlier
source premise. The doubled-natural/chief-factor contradiction is still
needed to exclude the original solvable plane alternative.
Source: Aschbacher--Smith 13.4.7(3), printed p.903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

theorem original_plane_second_nonsolvable_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G))
    (Wplane : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hWplane : Module.finrank (ZMod 2) Wplane = 2)
    (hTplane : (T : Subgroup G) ≤ normalizer (m.naturalPreimage Wplane : Set G))
    (hBplane : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage Wplane : Set G))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G)) :
    let X := A ⊔ B
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    let Y := firstFlagNormalizer T L V ⊔ (Y₂ ⊔ (T : Subgroup G))
    ¬ Group.IsSolvable Y := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
  let P := firstFlagNormalizer T L V
  let Q := Y₂ ⊔ (T : Subgroup G)
  let Y := P ⊔ Q
  let U := conjugateSpanBy Z Y
  have hTY : (T : Subgroup G) ≤ Y := le_sup_right.trans le_sup_right
  let S := T.subtype hTY
  let Pi := P.subgroupOf Y
  let Qi := Q.subgroupOf Y
  let K₁ := (pResidual 2 Pi).map Pi.subtype
  let K₂ := (pResidual 2 Qi).map Qi.subtype
  obtain ⟨_,_,_,_,_,_,hg,hlocal,hred,_,hresQ,_⟩ := original_plane_second_amalgam_at
    h₀ h structural D m hTA hTB eA eB hne hindexL hindexA hindexB hcentral
    hs hcomm Wplane hWplane hTplane hBplane
  have hker := (original_plane_second_action_kernel_at h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane hM).2
  obtain ⟨hnotPJ,_,hmove,_⟩ := original_plane_second_thompson_at h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane
  have hnot := (original_plane_second_noncommuting_at h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
    Wplane hWplane hTplane hBplane).2.1
  have hpmap : K₁.map Y.subtype = (pResidual 2 P).map P.subtype := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le le_sup_left]
  have hqmap : K₂.map Y.subtype = Y₂ := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le le_sup_right]
    exact hresQ
  have hjmap : (elementaryAbelianMaxJ (S : Subgroup Y)).map Y.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective Y.subtype Y.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTY]
  have hJn : ¬ (elementaryAbelianMaxJ (S : Subgroup Y)).Normal := by
    intro hn
    let := hn
    have hh := (elementaryAbelianMaxJ (S : Subgroup Y)).le_normalizer_map Y.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hjmap] at hh
    exact hnotPJ (le_sup_left.trans hh)
  have hm : ⁅K₁,elementaryAbelianMaxJ (S : Subgroup Y)⁆ = K₁ := by
    apply map_injective Y.subtype_injective
    rw [map_commutator,hpmap,hjmap]
    exact hmove
  have hn : ¬ K₂ ≤ normalizer (K₁ : Set Y) := by
    intro hh
    have hh' := (map_mono (f := Y.subtype) hh).trans (K₁.le_normalizer_map Y.subtype)
    rw [hpmap,hqmap] at hh'
    exact hnot hh'
  exact ChapterF.nonsolvable_of_reduced_thompson_pair S hg
    (show (S : Subgroup Y) ≤ Qi from fun _ hx => mem_sup_right hx)
    (U.subgroupOf Y) hred hker hJn hm
    ((Chapter3.sqtk_of_mem_H h₀.qtke hlocal.1.1).stronglyQuasithin
      3 Nat.prime_three (by decide)) hn


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
