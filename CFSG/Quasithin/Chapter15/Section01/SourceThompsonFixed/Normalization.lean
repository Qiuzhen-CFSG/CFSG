module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonPrepared
public import Theory.GroupTheory.PResidual.ThompsonNormalizer


/-!
# Normalization and the original Thompson fixed residual

For W = C_V(J₁(T)), source15.1.9 places N_G(J(T)) in M and J(T)
centralizes W. If C = C_G(Ω₁Z(T)) normalizes W, Thompson Frattini and
the original seed residual centralizer force O²(C) to centralize W.
The converse follows from the Sylow supplement. This proves an exact
normalization criterion and applies it to the normalizer conclusions
of15.1.14(2--3), retaining the chosen V and all literal subgroup maps.

The complete small-chief actions also prove normalization by every original
H-star local. The passage from those locals to all of C remains distinct;
no global normalization or H-star selection principle is asserted here.

Source: Aschbacher--Smith15.1.9 and15.1.12--14, printed pp.1089--1091.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original residual conclusion follows from normalization of the same chosen fixed subgroup. -/
theorem PreparedChosenModule.thompsonFixed_residual_of_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hn : centralizer (centralInvolutions T : Set G) ≤
      normalizer (thompsonFixed T V : Set G)) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G) := by
  let C := centralizer (centralInvolutions T : Set G)
  have hTC : (T : Subgroup G) ≤ C := by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm
  have hWT : thompsonFixed T V ≤ (T : Subgroup G) := by
    intro w hw
    exact ChapterB.thompsonJ_le _ _
      (((mem_omegaOneCenterAmbient_iff _ w).mp (h.thompsonFixed_le_omega T hM hw)).1)
  exact embedded_pResidual_le_centralizer_of_thompson_normalizer T C M _ hTC hM.1.2
    (hWT.trans hTC) hn
    (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
    (hJ.trans (centralizer_le (inf_le_left.trans h.le_local)))
    (h.seed_residual.trans (centralizer_le inf_le_left))

/-- Under the prepared source hypotheses, global residual centralization is equivalent to normalization. -/
theorem PreparedChosenModule.thompsonFixed_residual_iff_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) :
    (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G) ↔
    centralizer (centralInvolutions T : Set G) ≤ normalizer (thompsonFixed T V : Set G) := by
  refine ⟨?_,h.thompsonFixed_residual_of_normalizes hG T hM hJ⟩
  intro hres
  let C := centralizer (centralInvolutions T : Set G)
  have hTC : (T : Subgroup G) ≤ C := by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm
  have hTJ : (T : Subgroup G) ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (ChapterB.thompsonJ (T : Subgroup G) 1).map (MulAut.conj t).toMonoidHom = _
    rw [←ChapterB.thompsonJ_map_equiv]
    exact congrArg (fun S => ChapterB.thompsonJ S 1)
      (mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht))
  have hTN : (T : Subgroup G) ≤ normalizer (thompsonFixed T V : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      (hTJ.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have he := congrArg (map C.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTC))
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTC] at he
  exact he.symm.le.trans (sup_le (hres.trans (Subgroup.centralizer_le_normalizer _)) hTN)

/-- The actual source15.1.14(2--3) consumer, using normalization for its first clause. -/
theorem PreparedChosenModule.thompsonFixed_normalizers_of_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hn : centralizer (centralInvolutions T : Set G) ≤ normalizer (thompsonFixed T V : Set G)) :
    M ⊓ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤
        normalizer (thompsonFixed T V : Set G) ∧
      normalizer (thompsonFixed T V : Set G) ≤ Mc ∧
      normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) ≤ M ⊓ Mc :=
  h.thompsonFixed_normalizers hG T hM hJ hu
    (h.thompsonFixed_residual_of_normalizes hG T hM hJ hn)

/-- The proved small-chief actions normalize the chosen fixed subgroup in every original H-star local. -/
theorem PreparedChosenModule.source_thompsonFixed_local_normalizers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) :
    ∀ H ∈ Chapter3.HStar (T : Subgroup G) M, H ≤ normalizer (thompsonFixed T V : Set G) := by
  have hTJ : (T : Subgroup G) ≤ normalizer (ChapterB.thompsonJ (T : Subgroup G) 1 : Set G) := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (ChapterB.thompsonJ (T : Subgroup G) 1).map (MulAut.conj t).toMonoidHom = _
    rw [←ChapterB.thompsonJ_map_equiv]
    exact congrArg (fun S => ChapterB.thompsonJ S 1)
      (mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht))
  have hTN : (T : Subgroup G) ≤ normalizer (thompsonFixed T V : Set G) :=
    (le_inf (hM.1.2.trans h.normalized)
      (hTJ.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  intro H hH
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hSmap : ((T.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype =
      (T : Subgroup G) := map_subgroupOf_eq_of_le hTH
  have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,hSmap] at he
  exact he.symm.le.trans (sup_le
    ((h.source_thompsonFixed_local_residuals hG T hempty hM hJ H hH).trans
      (Subgroup.centralizer_le_normalizer _)) hTN)

end CFSG.Quasithin.Chapter15.Section01
