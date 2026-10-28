module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonFixed.ThompsonCenterNormalizer
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Sylow

/-!
# Thompson fusion inside the original centralizer

For the original E = C_W(J₁(T)), every C_G(Z)-conjugate stabilized by J(T)
equals E. Apply Burnside set fusion inside C_G(Z), so the resulting transporter
lies in N_G(J(T)) intersect C_G(Z), hence in M intersect C_G(Z). The seed
residual and the Sylow supplement show that this intersection preserves E.
This removes the earlier requirement that the conjugate lie in Ω₁Z(J₁(T)).

Consequently the original residual conclusion is equivalent both to J(T)
stabilizing each conjugate and to J(T) centralizing the entire conjugate span.
Failure therefore gives a conjugate not even normalized by J(T). All statements
keep the same prepared full or proper W. The ambient stabilization premise
remains open with qt-e-1514-global-thompson-residual; the source application
below and the separate Resolver adapter do not discharge it.

Source: Aschbacher--Smith, A.1.35 and 15.1.6,9,14, printed pp.30,1087--1091.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The seed residual and Sylow supplement already preserve the original
fixed subgroup inside M intersect C_G(Z). -/
theorem PreparedChosenModule.seedCentralizer_normalizes_thompsonFixed
    (T : Sylow 2 G) {M W : Subgroup G} (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M W) :
    M ⊓ centralizer (centralInvolutions T : Set G) ≤
      normalizer (thompsonFixed T W : Set G) := by
  let I := M ⊓ centralizer (centralInvolutions T : Set G)
  have hTI : (T : Subgroup G) ≤ I := le_inf hM.1.2 (by
    intro t ht z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hTN : (T : Subgroup G) ≤ normalizer (thompsonFixed T W : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have he := congrArg (map I.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTI))
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTI] at he
  exact he.symm.le.trans (sup_le
    ((h.seed_residual.trans (centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)) hTN)

/-- Fusion inside the original centralizer: a conjugate stabilized by the
ordinary Thompson subgroup equals the original chosen fixed subgroup. -/
theorem PreparedChosenModule.thompsonFixed_conjugate_eq_of_maxJ_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M W : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M W) (g : G)
    (hg : g ∈ centralizer (centralInvolutions T : Set G))
    (hn : elementaryAbelianMaxJ (T : Subgroup G) ≤
      normalizer ((thompsonFixed T W).map (MulAut.conj g).toMonoidHom : Set G)) :
    (thompsonFixed T W).map (MulAut.conj g).toMonoidHom = thompsonFixed T W := by
  let C := centralizer (centralInvolutions T : Set G)
  let E := thompsonFixed T W
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hTC : (T : Subgroup G) ≤ C := by
    intro t ht z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  let S : Sylow 2 C := T.subtype hTC
  have hET : E ≤ (T : Subgroup G) := by
    intro e he
    exact ChapterB.thompsonJ_le _ _
      (((mem_omegaOneCenterAmbient_iff _ e).mp (h.thompsonFixed_le_omega T hM he)).1)
  have hEC : E ≤ C := hET.trans hTC
  let E' := E.subgroupOf C
  let g' : C := ⟨g,hg⟩
  let F' := E'.map (MulAut.conj g').toMonoidHom
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup C)).map C.subtype = J := by
    rw [←elementaryAbelianMaxJ_map_injective C.subtype C.subtype_injective]
    exact congrArg elementaryAbelianMaxJ (map_subgroupOf_eq_of_le hTC)
  have hE'map : E'.map C.subtype = E := map_subgroupOf_eq_of_le hEC
  have hF'map : F'.map C.subtype = E.map (MulAut.conj g).toMonoidHom := by
    change (E'.map _).map _ = _
    rw [map_map]
    have he : C.subtype.comp (MulAut.conj g').toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp C.subtype := rfl
    rw [he,←map_map,hE'map]
  have hJE : J ≤ normalizer (E : Set G) :=
    (hJ.trans (centralizer_le (inf_le_left.trans h.le_local))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hJE' : elementaryAbelianMaxJ (S : Subgroup C) ≤ normalizer (E' : Set C) := by
    intro j hj
    exact le_normalizer_comap C.subtype (hJE (hJmap ▸ mem_map_of_mem C.subtype hj))
  have hJF' : elementaryAbelianMaxJ (S : Subgroup C) ≤ normalizer (F' : Set C) := by
    apply le_normalizer_iff.mpr
    intro j hj e he
    have hjG : (j : G) ∈ J := hJmap ▸ mem_map_of_mem C.subtype hj
    have heG : (e : G) ∈ E.map (MulAut.conj g).toMonoidHom :=
      hF'map ▸ mem_map_of_mem C.subtype he
    have hh := le_normalizer_iff.mp hn (j : G) hjG (e : G) heG
    rw [←hF'map] at hh
    obtain ⟨x,hx,hxe⟩ := hh
    exact (show x = j*e*j⁻¹ from Subtype.ext hxe) ▸ hx
  obtain ⟨n,hnJ,hfusion⟩ := S.weakly_closed_normalizer_controls_set_fusion
    (elementaryAbelianMaxJ (S : Subgroup C)) (sSup_le fun _ hA => hA.1)
    (maxJ_weakly_closed_normalizer S) (E' : Set C) (F' : Set C) hJE' hJF' g' rfl
  have hnJg : (n : G) ∈ normalizer (J : Set G) := by
    have hh := (elementaryAbelianMaxJ (S : Subgroup C)).le_normalizer_map C.subtype
      (mem_map_of_mem C.subtype hnJ)
    rwa [hJmap] at hh
  have hnM := (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1 hnJg
  have hnE : (n : G) ∈ normalizer (E : Set G) := h.seedCentralizer_normalizes_thompsonFixed T hM ⟨hnM,n.property⟩
  have hnE' : n ∈ normalizer (E' : Set C) := le_normalizer_comap C.subtype hnE
  have heq : E'.map (MulAut.conj n).toMonoidHom = F' := SetLike.coe_injective hfusion
  have hstable : E'.map (MulAut.conj n).toMonoidHom = E' :=
    mem_normalizer_iff_map_conj_eq.mp hnE'
  have heq' : F' = E' := heq.symm.trans hstable
  change E.map (MulAut.conj g).toMonoidHom = E
  rw [←hF'map,heq',hE'map]

/-- Residual centralization is equivalent to ordinary Thompson stabilization
of every conjugate of the original fixed subgroup. -/
theorem PreparedChosenModule.thompsonFixed_residual_iff_conjugates_maxJ_normalized
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M W : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M W) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T W : Set G) ↔
    ∀ g ∈ centralizer (centralInvolutions T : Set G),
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        normalizer ((thompsonFixed T W).map (MulAut.conj g).toMonoidHom : Set G) := by
  rw [h.thompsonFixed_residual_iff_normalizes hG T hM hJ]
  constructor
  · intro hn g hg
    have he : (thompsonFixed T W).map (MulAut.conj g).toMonoidHom = thompsonFixed T W :=
      mem_normalizer_iff_map_conj_eq.mp (hn hg)
    rw [he]
    exact (hJ.trans (centralizer_le (inf_le_left.trans h.le_local))).trans
      (Subgroup.centralizer_le_normalizer _)
  · intro hn g hg
    exact mem_normalizer_iff_map_conj_eq.mpr
      (h.thompsonFixed_conjugate_eq_of_maxJ_normalizes hG T hM hJ g hg (hn g hg))

/-- The entire conjugate span need only centralize the ordinary Thompson
subgroup; no prior containment in the Sylow or its omega-center is required. -/
theorem PreparedChosenModule.thompsonFixed_residual_iff_span_centralizes_maxJ
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M W : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M W) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T W : Set G) ↔
    conjugateSpanBy (thompsonFixed T W) (centralizer (centralInvolutions T : Set G)) ≤
      centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  constructor
  · intro hres
    have hn := (h.thompsonFixed_residual_iff_normalizes hG T hM hJ).mp hres
    exact (conjugateSpanBy_le le_rfl hn).trans
      (le_centralizer_iff.mp (hJ.trans (centralizer_le (inf_le_left.trans h.le_local))))
  · intro hspan
    apply (h.thompsonFixed_residual_iff_conjugates_maxJ_normalized hG T hM hJ).mpr
    intro g hg
    have hmap : (thompsonFixed T W).map (MulAut.conj g).toMonoidHom ≤
        conjugateSpanBy (thompsonFixed T W) (centralizer (centralInvolutions T : Set G)) :=
      (map_mono (le_conjugateSpanBy _ _)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_conjugateSpanBy _ _) hg))
    exact (le_centralizer_iff.mp (hmap.trans hspan)).trans
      (Subgroup.centralizer_le_normalizer _)

/-- A failure forces a conjugate which is not even stabilized by J(T).
This is stronger than merely leaving the Thompson omega-center. -/
theorem PreparedChosenModule.thompsonFixed_failure_conjugate_not_maxJ_normalized
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M W : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M W)
    (hnot : ¬ (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T W : Set G)) :
    ∃ g ∈ centralizer (centralInvolutions T : Set G),
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
        normalizer ((thompsonFixed T W).map (MulAut.conj g).toMonoidHom : Set G) := by
  classical
  have hn := mt (h.thompsonFixed_residual_iff_conjugates_maxJ_normalized hG T hM hJ).mpr hnot
  push Not at hn
  exact hn

/-- Apply the relative fusion criterion to every normalizer and residual
clause of original 15.1.14, with the same W and singleton partner Mc. -/
theorem PreparedChosenModule.thompsonFixed_source_clauses_of_conjugates_maxJ_normalized
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc W : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M W)
    (hconj : ∀ g ∈ centralizer (centralInvolutions T : Set G),
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        normalizer ((thompsonFixed T W).map (MulAut.conj g).toMonoidHom : Set G)) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
        (centralizer (centralInvolutions T : Set G)).subtype ≤
      centralizer (thompsonFixed T W : Set G) ∧
    M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
        normalizer (thompsonFixed T W : Set G) ∧
      normalizer (thompsonFixed T W : Set G) ≤ Mc ∧
      normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc := by
  have hres := (h.thompsonFixed_residual_iff_conjugates_maxJ_normalized hG T hM hJ).mpr hconj
  exact ⟨hres,h.thompsonFixed_normalizers hG T hM hJ hu hres⟩

end CFSG.Quasithin.Chapter15.Section01
