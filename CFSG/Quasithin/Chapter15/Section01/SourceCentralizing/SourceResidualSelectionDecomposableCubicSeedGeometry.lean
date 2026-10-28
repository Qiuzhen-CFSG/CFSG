module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableSylow
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.Projection
public import Theory.GroupTheory.IndexTwoOmegaSpan

/-!
# The original exchanged markings recover Ω₁Z(S) and its component-fixed part

The original Sylow subgroup normalizes E = C_V(J₁(T)). Its two exchanged
markings are disjoint and have the same order. When their squared order is
|E|, they generate E. The index-two omega-center theorem then gives
Ω₁Z(S) = E. The exchanged marking has trivial intersection with C_G(L),
whereas the original marking centralizes L, so C_E(L) is exactly Z₁.

The generic statement covers either exchanged-plane size. The actual
decomposable adapter uses its original sixteen-element fixed group and
four-element marking, without a quotient model or block reconstruction.

Source: Aschbacher--Smith 15.1.17--19 and 15.1.29,
printed pp.1093--1094,1103--1104.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original index-two exchanged pair exhausts the Sylow omega-center;
its part centralizing the selected component is precisely its first marking. -/
theorem CaseIComponentData.ExchangedSource.fixed_omegaCenter_and_component_fixed_of_card_square
    {T : Sylow 2 G} {M Mc V : Subgroup G} {d : CaseIComponentData T M Mc V}
    (x : d.ExchangedSource) (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hcard : Nat.card (thompsonFixed T V) = Nat.card d.Z1 * Nat.card d.Z1) :
    omegaOneCenterAmbient d.S = thompsonFixed T V ∧
      thompsonFixed T V ⊓ centralizer (d.L : Set G) = d.Z1 := by
  let := h.elementary
  let E := thompsonFixed T V
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨t,ht,htS⟩ := x.exchange_exists
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    le_normalizer_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans (normalizer_le_normalizer_centralizer _))
  have hZ2E : d.Z2 t ≤ E := by
    have he : E.map (MulAut.conj t).toMonoidHom = E :=
      mem_normalizer_iff_map_conj_eq.mp (hTE ht)
    exact (map_mono d.Z1_le_fixed).trans_eq he
  have hZ2move : d.Z2 t ≤ d.nineMovingPlane :=
    (map_mono x.marked_le_fixed).trans_eq (x.exchanges t ht htS).1
  have hdis : d.Z1 ⊓ d.Z2 t = ⊥ := bot_unique
    ((inf_le_inf x.marked_le_fixed hZ2move).trans x.planes_inf.le)
  have hZ2n : d.Z2 t ≤ normalizer (d.Z1 : Set G) :=
    hZ2E.trans (E.le_centralizer.trans ((centralizer_le d.Z1_le_fixed).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hgen : d.Z1 ⊔ d.Z2 t = E := by
    apply eq_of_le_of_card_ge (sup_le d.Z1_le_fixed hZ2E)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ hZ2n (disjoint_iff.mpr hdis)]
    have hz : Nat.card (d.Z2 t) = Nat.card d.Z1 :=
      card_map_of_injective (MulAut.conj t).injective
    rw [hz]
    exact hcard.le
  have hZ1S : d.Z1 ≤ omegaOneCenterAmbient d.S := by
    intro a ha
    have haV := d.Z1_le_fixed.trans inf_le_left ha
    have haT := ChapterB.thompsonJ_le _ _ ((mem_omegaOneCenterAmbient_iff _ _).mp
      (h.thompsonFixed_le_omega T hM (d.Z1_le_fixed ha))).1
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨⟨haT,fun z hz => (V.le_centralizer haV) z (d.Z1_le_fixed.trans inf_le_left hz)⟩,
        elemPow_eq_one_of_isElementaryAbelian a haV,fun s hs => (hs.2 a ha).symm⟩
  have hZE : centralInvolutions T ≤ E := by
    refine le_inf ?_ ?_
    · rw [hfull]
      exact le_conjugateSpanBy _ _
    · exact (centralInvolutions_le_centralizer_sylow T).trans
        (centralizer_le (ChapterB.thompsonJ_le _ _))
  have hOmega := Subgroup.omegaCenter_eq_exchanged_pair d.S (T : Subgroup G) d.Z1
    d.S_le_T x.index t ht htS hZ1S hdis (hZE.trans_eq hgen.symm)
  refine ⟨hOmega.trans hgen,?_⟩
  apply le_antisymm
  · intro a ha
    have haE : a ∈ d.Z1 ⊔ d.Z2 t := hgen.symm ▸ ha.1
    rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hZ2n] at haE
    obtain ⟨b,hb,c,hc,he⟩ := haE
    have hbC : b ∈ centralizer (d.L : Set G) :=
      (le_centralizer_iff.mp d.L_component.1) hb
    have hcC : c ∈ centralizer (d.L : Set G) := by
      have hh := (centralizer (d.L : Set G)).mul_mem
        ((centralizer (d.L : Set G)).inv_mem hbC) ha.2
      rwa [←he,inv_mul_cancel_left] at hh
    have hc1 : c = 1 := mem_bot.mp
      ((x.seed_inf_centralizer_eq_bot hM hu h t ht htS).le ⟨hc,hcC⟩)
    have he' : b = a := by simpa only [hc1,mul_one] using he
    exact he' ▸ hb
  · exact le_inf d.Z1_le_fixed (le_centralizer_iff.mp d.L_component.1)

/-- On the same actual decomposable component, E is Ω₁Z(S) and C_E(L)=Z₁.
Only the original support marking and the proved exchanged source are used. -/
theorem PreparedChosenModule.decomposable_marked_omegaCenter_and_component_fixed
    (T : Sylow 2 G) {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation)
      (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (e : CaseIComponentData T M Mc V),
      e.Z1 = DecomposableMarker.thompsonPlane T V (c.ambientFactor d s.first).space →
      e.ExchangedSource →
      omegaOneCenterAmbient e.S = thompsonFixed T V ∧
        thompsonFixed T V ⊓ centralizer (e.L : Set G) = e.Z1 := by
  let := h.elementary
  intro U c d s e heZ x
  apply x.fixed_omegaCenter_and_component_fixed_of_card_square hM hu h hfull
  rw [s.fixed_card,heZ,s.thompson_card]

end CFSG.Quasithin.Chapter15.Section01
