module
public import CFSG.Quasithin.Chapter14.Section02.RankTwoLocal
public import CFSG.Quasithin.ChapterG.Section02.Binary.CoreIntersection
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import CFSG.Quasithin.ChapterG.Section02.Binary.FourAction
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
/-!
# The opposite elementary subgroup for the original selected overgroup

The original Chapter 14 prefix supplies the actual binary natural data
whenever U=⟨V^H⟩ is nonabelian. The rank-two source gives the full LT action;
its exact kernel and its residual L-action give compatible G.2.3 coordinates.
If U had trivial star image it would centralize V, forcing U abelian. The
orbit span of the point supplies the required moving conjugator.

The literal G.2.3 opposite image E in H/O₂(H) is elementary. Its order gives
an elementary subgroup A≤U with |U:A|=2|E|. This removes the local-geometry
premises in the original 14.2.16 normal Bender branch and the 14.2.20(1)
index-five branch, while retaining their separate recognition obligations.

Source: Aschbacher–Smith 14.2.4–6, printed p.982, and G.2.2–3,
printed pp.332–334.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The actual original flag and moving conjugator for a nonabelian local closure. -/
theorem source_binary_geometric_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H)) :
    let D : ChapterG.Section02.Setup G :=
      { V := rankTwoSeed T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
        T := T, H := H }
    D.Hypothesis ∧ D.V = D.VL ∧ D.star D.U ≠ ⊥ ∧
      ∃ g ∈ D.L, g ∉ D.G₁ := by
  let D : ChapterG.Section02.Setup G :=
    { V := rankTwoSeed T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  let r := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨he, F, hp, _, _, hlocal⟩ := source_lemma_14_2_6 hG T hempty hM hu hmany hcard e
  obtain ⟨_, hg, _⟩ := hlocal H hH
  have h : D.Hypothesis := by simpa only [hp] using hg
  have hL : D.L ≤ normalizer (D.V : Set G) := r.L_normalizes_seed
  have hspan : D.V = D.VL := by
    apply le_antisymm ?_ (conjugateSpanBy_le h.point_le hL)
    obtain ⟨z, hz, hz1⟩ := D.V₁.bot_or_exists_ne_one.resolve_left h.point_ne_bot
    intro v hv
    by_cases hv1 : v = 1
    · exact hv1.symm ▸ (D.VL.one_mem)
    obtain ⟨l, hl, hlv⟩ := r.nonidentity_transitive z v (h.point_le hz) hv hz1 hv1
    exact subset_closure ⟨l, hl, z, hz, hlv⟩
  have hnstar : D.star D.U ≠ ⊥ := by
    intro hb
    have hUT := h.U_normal_in_T.1
    have hUL : D.U ≤ D.LT := hUT.trans le_sup_right
    have hk : D.U.subgroupOf D.LT ≤ pCore 2 D.LT := by
      have hm := (Subgroup.map_eq_bot_iff _).mp hb
      simpa only [QuotientGroup.ker_mk'] using hm
    have hUC : D.U ≤ centralizer (D.V : Set G) := by
      intro u hu
      have huQ := mem_map_of_mem D.LT.subtype (hk (show
        (⟨u, hUL hu⟩ : D.LT) ∈ D.U.subgroupOf D.LT from hu))
      have hQC : D.LT.pCoreIn 2 = D.LT ⊓ centralizer (D.V : Set G) := r.centralizer.symm
      exact (hQC.le huQ).2
    apply hne
    rw [← rankTwoSeed_eq_localModule]
    exact (conjugateSpanBy_commutative_iff D.V D.H).mpr (le_centralizer_iff.mp hUC)
  refine ⟨h, hspan, hnstar, ?_⟩
  by_contra hg
  have hLN : D.L ≤ D.G₁ := by
    intro g hgL
    by_contra hgN
    exact hg ⟨g, hgL, hgN⟩
  have hs : D.VL ≤ D.V₁ := conjugateSpanBy_le le_rfl hLN
  exact h.quotient_nonzero (le_antisymm h.point_le (hspan.le.trans hs))

theorem source_nonabelian_binary_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H)) :
    let D : ChapterG.Section02.Setup G :=
      { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
        T := T, H := H }
    D.Hypothesis ∧ Nonempty D.BinaryNaturalData ∧ ∃ g ∈ D.L, g ∉ D.G₁ := by
  let D : ChapterG.Section02.Setup G :=
    { V := rankTwoSeed T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  let r := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨h, hs, hn, hg⟩ := source_binary_geometric_inputs hG T hempty hM hu hmany hcard e H hH hne
  have hc : Nat.card D.V = 4 := rankTwoSeed_card r
  have hp : Nat.card D.V₁ = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hdata : Nonempty D.BinaryNaturalData := ⟨
    ChapterG.Section02.Setup.binaryNaturalData_of_four_action h r.L_normalizes_seed hc hs
      r.full_LT_action r.literal_action_kernel r.L_action_range hp hn⟩
  simpa only [D, rankTwoSeed_eq_localModule] using (show
    D.Hypothesis ∧ Nonempty D.BinaryNaturalData ∧ ∃ g ∈ D.L, g ∉ D.G₁ from ⟨h,hdata,hg⟩)


theorem source_nonabelian_elementary_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H)) :
    ∃ E : Subgroup (H ⧸ pCore 2 H), IsElementaryAbelian 2 E ∧
      ∃ A : Subgroup G, A ≤ conjugateSpanBy (localModule T M) H ∧
        IsElementaryAbelian 2 A ∧
        A.relIndex (conjugateSpanBy (localModule T M) H) = 2 * Nat.card E := by
  let D : ChapterG.Section02.Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨h, ⟨b⟩, g, hgL, hgN⟩ :=
    source_nonabelian_binary_data hG T hempty hM hu hmany hcard e H hH hne
  have hUT := h.U_normal_in_T.1
  have hf := h.frattini_U_le_point
  have hUQ := h.U_le_core
  have hc := h.commutator_U_core_le_point
  obtain ⟨_, helem, _⟩ := ChapterG.Section02.Setup.binary_source_core_intersection_and_index
    h b hUT hf hUQ hc g hgL hgN
  obtain ⟨hE, hindex⟩ := ChapterG.Section02.Setup.binary_source_opposite_image
    h b hUT hf hUQ hc g hgL hgN
  exact ⟨_, hE, D.S₂ g, inf_le_left, helem, hindex⟩

end CFSG.Quasithin.Chapter14.Section02
