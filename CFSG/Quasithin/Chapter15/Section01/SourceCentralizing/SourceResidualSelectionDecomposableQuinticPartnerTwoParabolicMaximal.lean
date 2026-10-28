module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoParabolicChief

/-!
# The actual selected maximal subgroup fixes E under its residual

The escape join K has two-group action on E: its first factor has a Sylow
supplement centralizing E, and its second factor centralizes E. Therefore
O²(K) centralizes E. The actual selected parabolic has maximal subgroup
B=P∩K, so its residual also centralizes E. This does not identify B with
P∩M or assert that B normalizes V.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open NoncentralChiefRefinement
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The literal escape join normalizes E and its residual centralizes E. -/
theorem PreparedChosenModule.thompsonFixed_escape_join_residual
    (T : Sylow 2 G) {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) :
    let E := thompsonFixed T V
    let C := centralizer (centralInvolutions T:Set G)
    let K := (M⊓C)⊔((pResidual 2 C).map C.subtype⊓centralizer (E:Set G))
    (T:Subgroup G)≤K ∧ K≤normalizer (E:Set G) ∧
      (pResidual 2 K).map K.subtype≤centralizer (E:Set G) := by
  let E := thompsonFixed T V
  let C := centralizer (centralInvolutions T:Set G)
  let K := (M⊓C)⊔((pResidual 2 C).map C.subtype⊓centralizer (E:Set G))
  let A := (pResidual 2 (M⊓C:Subgroup G)).map (M⊓C).subtype⊔
    ((pResidual 2 C).map C.subtype⊓centralizer (E:Set G))
  have hTC : (T:Subgroup G)≤C := by
    intro t ht z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hTI : (T:Subgroup G)≤M⊓C := le_inf hM.1.2 hTC
  have hTJ : (T:Subgroup G)≤normalizer (ChapterB.thompsonJ (T:Subgroup G) 1:Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (ChapterB.thompsonJ (T:Subgroup G) 1).map (MulAut.conj t).toMonoidHom=_
    rw [←ChapterB.thompsonJ_map_equiv]
    exact congrArg (fun S=>ChapterB.thompsonJ S 1)
      (mem_normalizer_iff_map_conj_eq.mp ((T:Subgroup G).le_normalizer ht))
  have hTN : (T:Subgroup G)≤normalizer (E:Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      (hTJ.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hAC : A≤centralizer (E:Set G) := sup_le
    (h.seed_residual.trans (centralizer_le inf_le_left)) inf_le_right
  have hsup : (pResidual 2 (M⊓C:Subgroup G)).map (M⊓C).subtype⊔(T:Subgroup G)=M⊓C := by
    have hh := congrArg (map (M⊓C).subtype) (pResidual_sup_sylow_eq_top (T.subtype hTI))
    rwa [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI] at hh
  have hKA : K≤A⊔(T:Subgroup G) := sup_le
    (hsup.symm.le.trans (sup_le_sup le_sup_left le_rfl))
    (le_sup_right.trans le_sup_left)
  exact ⟨hTI.trans le_sup_left,hKA.trans (sup_le
    (hAC.trans (Subgroup.centralizer_le_normalizer _)) hTN),
    (embedded_pResidual_mono 2 hKA).trans
      (pResidual_join_le_centralizer 2 A T E hAC hTN T.isPGroup')⟩

/-- The same selected moving parabolic has literal maximal subgroup P∩K,
whose residual centralizes E; it retains the two noncentral chiefs on V's span. -/
theorem PreparedChosenModule.thompsonFixed_moving_parabolic_maximal_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T:Subgroup G)≤centralizer (localModule T M:Set G))
    (h : PreparedChosenModule T M V)
    (hVC : V≤(centralizer (centralInvolutions T:Set G)).pCoreIn 2)
    (hnot : ¬(pResidual 2 (centralizer (centralInvolutions T:Set G))).map
      (centralizer (centralInvolutions T:Set G)).subtype≤
        centralizer (thompsonFixed T V:Set G)) :
    let E := thompsonFixed T V
    let C := centralizer (centralInvolutions T:Set G)
    let K := (M⊓C)⊔((pResidual 2 C).map C.subtype⊓centralizer (E:Set G))
    ∃ P : Subgroup G, P≤C ∧ P∈Chapter1.HOver G (T:Set G) ∧
      ChapterB.IsMinimalParabolicOver T P ∧ IsSQTK KnownSimple.IsKnownSimple P ∧
      generalizedFitting P=pCore 2 P ∧ ¬P≤M ∧
      ¬(pResidual 2 P).map P.subtype≤centralizer (E:Set G) ∧
      (∀ Y : Subgroup G, (T:Subgroup G)≤Y → Y<P → Y≤K) ∧
      V≤P.pCoreIn 2 ∧ IsElementaryAbelian 2 (conjugateSpan P V) ∧
      (∀ s : SeriesOn ((conjugateSpan P V).subgroupOf P), s.noncentralCount=2) ∧
      let B := P⊓K
      (T:Subgroup G)≤B ∧ B⋖P ∧ B≤normalizer (E:Set G) ∧
        (pResidual 2 B).map B.subtype≤centralizer (E:Set G) := by
  let E := thompsonFixed T V
  let C := centralizer (centralInvolutions T:Set G)
  let K := (M⊓C)⊔((pResidual 2 C).map C.subtype⊓centralizer (E:Set G))
  obtain ⟨P,hPC,hP,hp,hSQ,hF,hout,hmove,hproper,hVP,he,hchief⟩ :=
    h.thompsonFixed_moving_parabolic_two_chiefs hG T hempty hM hJ hVC hnot
  obtain ⟨hTK,hKN,hKR⟩ := h.thompsonFixed_escape_join_residual T hM
  have hPK : ¬P≤K := fun hh=>hmove ((embedded_pResidual_mono 2 hh).trans hKR)
  have hlt : P⊓K<P := lt_of_le_of_ne inf_le_left (by
    intro hh
    exact hPK (hh ▸ inf_le_right))
  have hc : P⊓K⋖P := ⟨hlt,by
    intro Y hBY hYP
    exact hBY.not_ge (le_inf hYP.le (hproper Y
      ((le_inf hP.2 hTK).trans hBY.le) hYP))⟩
  exact ⟨P,hPC,hP,hp,hSQ,hF,hout,hmove,hproper,hVP,he,hchief,
    le_inf hP.2 hTK,hc,inf_le_right.trans hKN,
    (embedded_pResidual_mono 2 (inf_le_right : P⊓K≤K)).trans hKR⟩

end CFSG.Quasithin.Chapter15.Section01
