module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneAlpha
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.PlaneActionAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearThompsonAt

/-!
# Guarded enlargement above the plane radical

Small maximum images in the actual plane action give elementary
alpha(T)V and its displacement bound. Normal generation then gives
LT-invariance. The final theorem supplies the original linear-pair
application, retaining the full action kernel and guarded Chapter12 facts.
Source: Aschbacher--Smith B.2.18, C.1.37 and 13.4.7(4), pp.902--903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V B : Subgroup G}

/-- The elementary enlarged module and its displacement, derived from the
original plane's near-maximum containment with no shortness hypothesis. -/
theorem original_plane_alpha_control_of_thompson_one_bound_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2) :
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    ChapterB.thompsonAlpha (T : Subgroup G) ⊔ V ≤ ChapterB.thompsonAlpha Q ∧
      IsElementaryAbelian 2 (ChapterB.thompsonAlpha (T : Subgroup G) ⊔ V : Subgroup G) ∧
      ⁅ChapterB.thompsonAlpha Q,elementaryAbelianMaxJ (T : Subgroup G)⁆ ≤ V := by
  obtain ⟨q,hk,hker,hY,hT,hQ⟩ := exists_original_plane_action_marking_at h structural D m eL W hW hTW
  rw [←hB] at hQ
  let X := L ⊔ (T : Subgroup G)
  let S : Sylow 2 X := T.subtype le_sup_right
  let U := V.subgroupOf X
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes (((structural L h).2.2 V D).1))
  let : IsElementaryAbelian 2 U := by
    let := D.elementary
    exact IsElementaryAbelian.subgroupOf hVX
  have hUS : U ≤ (S : Subgroup X) := comap_mono D.le_sylow
  have hu : Nat.card U = 32 := (Nat.card_congr (subgroupOfEquivOfLe hVX).toEquiv).trans m.card_module
  have hr : 1 < ChapterB.twoRank (S : Subgroup X) := by
    have hb := elementary_card_le_maxOrder (S : Subgroup X) U hUS inferInstance
    rw [hu,ChapterB.maxOrder_eq_two_pow_rank] at hb
    by_contra! hn
    have hh : 2 ^ ChapterB.twoRank (S : Subgroup X) ≤ 2 ^ 1 :=
      Nat.pow_le_pow_right (by decide) hn
    omega
  have hjmap : (ChapterB.thompsonJ (S : Subgroup X) 1).map X.subtype =
      ChapterB.thompsonJ (T : Subgroup G) 1 := by
    rw [←ChapterB.thompsonJ_map_injective X.subtype X.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)]
  have hj : (ChapterB.thompsonJ (S : Subgroup X) 1).map q ≤ ChapterB.Offenders.D 6 := by
    apply (map_mono (show ChapterB.thompsonJ (S : Subgroup X) 1 ≤
        (B.pCoreIn 2).subgroupOf X from ?_)).trans hQ
    intro x hx
    exact hJ (hjmap ▸ mem_map_of_mem X.subtype hx)
  have hc := ChapterB.maximum_image_le_two_of_thompson_one_image_le_D S q hr hY hT hj
  obtain ⟨hle,hel,hmove⟩ := omegaCenter_replacement_control_of_small_images
    (S : Subgroup X) U hUS q hker hc
  have hcore : (S : Subgroup X) ⊓ centralizer (U : Set X) = pCore 2 X := by
    rw [←hker,hk,inf_eq_right.mpr (pCore_isPGroup.le_sylow_of_normal S)]
  rw [hcore] at hle hmove
  have hs : (S : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)
  have ha (R : Subgroup X) :
      (omegaOneCenterAmbient (elementaryAbelianMaxJ R)).map X.subtype =
        omegaOneCenterAmbient (elementaryAbelianMaxJ (R.map X.subtype)) := by
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective]
  have hm : ((omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup X))) ⊔ U).map X.subtype =
      ChapterB.thompsonAlpha (T : Subgroup G) ⊔ V := by
    rw [Subgroup.map_sup,ha,hs,map_subgroupOf_eq_of_le hVX]
    rfl
  refine ⟨?_,?_,?_⟩
  · have hh := map_mono (f := X.subtype) hle
    rw [hm,ha] at hh
    exact hh
  · let := hel
    exact hm ▸ IsElementaryAbelian.map X.subtype
  · have hh := map_mono (f := X.subtype) hmove
    rw [map_commutator,ha,←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
      hs,map_subgroupOf_eq_of_le hVX] at hh
    exact hh

/-- In the noncentral Thompson branch the enlarged elementary module is
normalized by the original LT, and the whole component displaces the
core's alpha subgroup only inside the original five-space. -/
theorem original_plane_alpha_normalized_of_thompson_one_bound_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2)
    (hne : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    let E := ChapterB.thompsonAlpha (T : Subgroup G) ⊔ V
    IsElementaryAbelian 2 E ∧
      L ⊔ (T : Subgroup G) ≤ normalizer (E : Set G) ∧
      ⁅ChapterB.thompsonAlpha ((L ⊔ (T : Subgroup G)).pCoreIn 2),L⁆ ≤ V := by
  obtain ⟨hle,hel,hmove⟩ := original_plane_alpha_control_of_thompson_one_bound_at
    h structural D m eL W hW hTW hB hJ
  obtain ⟨q,hk,hker,hY,_,_⟩ := exists_original_plane_action_marking_at h structural D m eL W hW hTW
  let X := L ⊔ (T : Subgroup G)
  let S : Sylow 2 X := T.subtype le_sup_right
  let U := V.subgroupOf X
  let Li := L.subgroupOf X
  let F := omegaOneCenterAmbient (elementaryAbelianMaxJ (pCore 2 X))
  let Zi := omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup X))
  let E := Zi ⊔ U
  have hLX : L ≤ X := le_sup_left
  have hVX : V ≤ X := D.le_sylow.trans le_sup_right
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.normalizes (((structural L h).2.2 V D).1))
  let : Li.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hcmp : Li.IsCComponent := h.maximal_faithful.1.1.1
  let : Group.IsPerfect Li := hcmp.perfect
  have hpL : IsPPerfect 2 Li := by
    intro N hn hquot
    let : N.Normal := hn
    by_contra hn1
    let : Nontrivial (Li ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn1
    let : Group.IsPerfect (Li ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (Li ⧸ N) := hquot.isNilpotent
    exact Group.IsPerfect.not_isSolvable (Li ⧸ N) inferInstance
  have hs : (S : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)
  have hjm : (elementaryAbelianMaxJ (S : Subgroup X)).map X.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hs]
  have ha (R : Subgroup X) :
      (omegaOneCenterAmbient (elementaryAbelianMaxJ R)).map X.subtype =
        omegaOneCenterAmbient (elementaryAbelianMaxJ (R.map X.subtype)) := by
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective]
  have hfm : F.map X.subtype = ChapterB.thompsonAlpha (X.pCoreIn 2) := ha _
  have hzm : Zi.map X.subtype = ChapterB.thompsonAlpha (T : Subgroup G) := by
    rw [ha,hs];rfl
  have hEm : E.map X.subtype = ChapterB.thompsonAlpha (T : Subgroup G) ⊔ V := by
    rw [Subgroup.map_sup,hzm,map_subgroupOf_eq_of_le hVX]
  have hFJ : ⁅F,elementaryAbelianMaxJ (S : Subgroup X)⁆ ≤ U := by
    apply (map_le_map_iff_of_injective X.subtype_injective).mp
    rw [map_commutator,hfm,hjm,map_subgroupOf_eq_of_le hVX]
    exact hmove
  let : F.Normal := by
    apply normal_iff_map_conj_eq.mpr
    intro x
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (pCore 2 X))).map
      (MulAut.conj x).toMonoidHom = _
    rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj x).injective,
      ←elementaryAbelianMaxJ_map_equiv]
    have he : (pCore 2 X).map (MulAut.conj x).toMonoidHom = pCore 2 X :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top];exact mem_top x)
    rw [he]
  have hJq : (elementaryAbelianMaxJ (S : Subgroup X)).map q ≠ ⊥ := by
    intro he
    have hh := (Subgroup.map_eq_bot_iff _).mp he
    rw [hk] at hh
    exact hne (hjm ▸ map_mono (f := X.subtype) hh)
  have hLq : Li.map q ≤ alternatingGroup (Fin 6) := by
    rw [←Equiv.Perm.twoResidual_eq_alternating]
    exact (map_mono (le_pResidual_of_isPPerfect Li hpL)).trans (map_pResidual_le 2 q)
  have hLN := Theory.SpecificGroups.SymmetricSix.perfect_le_normalClosure_of_nontrivial_image
    q (hk.symm ▸ pCore_isPGroup) hY Li (elementaryAbelianMaxJ (S : Subgroup X)) hpL hLq hJq
  have hFL : ⁅F,Li⁆ ≤ U := (commutator_mono le_rfl hLN).trans
    (commutator_normalClosure_le_of_normal F (elementaryAbelianMaxJ (S : Subgroup X)) U hFJ)
  have hZF : Zi ≤ F := by
    apply (map_le_map_iff_of_injective X.subtype_injective).mp
    rw [hzm,hfm]
    exact le_sup_left.trans hle
  have hLE : Li ≤ normalizer (E : Set X) :=
    le_normalizer_sup_of_commutator_le F Li Zi U hZF hFL
  have hSE : (S : Subgroup X) ≤ normalizer (E : Set X) := by
    apply (le_inf ?_ (show (S : Subgroup X) ≤ normalizer (U : Set X) from le_normalizer_of_normal)).trans
      (normalizer_inf_normalizer_le_normalizer_sup Zi U)
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup X))).map
      (MulAut.conj x).toMonoidHom = _
    rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj x).injective,
      ←elementaryAbelianMaxJ_map_equiv]
    have he : (S : Subgroup X).map (MulAut.conj x).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp ((S : Subgroup X).le_normalizer hx)
    rw [he]
  have hgen : Li ⊔ (S : Subgroup X) = ⊤ := by
    rw [Sylow.coe_subtype,←subgroupOf_sup hLX (show (T : Subgroup G) ≤ X from le_sup_right),subgroupOf_self]
  have hEn : E.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸ sup_le hLE hSE))
  refine ⟨hel,?_,?_⟩
  · let := hEn
    have hh := E.le_normalizer_map X.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hEm] using hh
  · have hh := map_mono (f := X.subtype) hFL
    rw [map_commutator,hfm,map_subgroupOf_eq_of_le hLX,map_subgroupOf_eq_of_le hVX] at hh
    exact hh

open Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource

/-- The actual linear pair supplies the noncentral Thompson premise of the
plane Baumann argument. No shortness or enlarged-module invariance is assumed. -/
theorem original_linear_pair_plane_alpha_at
    {A : Subgroup G}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hJ : ChapterB.thompsonJ (T : Subgroup G) 1 ≤ B.pCoreIn 2) :
    let E := ChapterB.thompsonAlpha (T : Subgroup G) ⊔ V
    IsElementaryAbelian 2 E ∧
      L ⊔ (T : Subgroup G) ≤ normalizer (E : Set G) ∧
      ⁅ChapterB.thompsonAlpha ((L ⊔ (T : Subgroup G)).pCoreIn 2),L⁆ ≤ V := by
  have hn := original_pair_linear_thompson_normal_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  exact original_plane_alpha_normalized_of_thompson_one_bound_at h structural D m eL W hW hTW hB hJ
    (thompson_not_le_original_core_of_outside_normalizer h D hout hn)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
