module
public import CFSG.Quasithin.ChapterG.Section10.NormalAxis
public import CFSG.Quasithin.ChapterG.Section10.Components.Movement
public import Theory.Representation.PerfectInvolutionExtension

/-!
# Marked-point containment in the normal component orbit

If a moved normal constituent avoids the marked point, the axis count makes
it Lagrangian. The displacement of each element of X has dimension at most
two, so every conjugate constituent, of dimension at least three, is X-stable.
Every complementary conjugate must then contain the marked point. The trivial
intersection property leaves exactly two conjugates; the odd-index point
centralizer cannot fix just one member of that two-element orbit.

Selecting a constituent inside any nonzero HX-invariant space gives G.10.10;
combined with the forward stabilizer implication this proves G.10.11.
This uses the already proved G.10.5 ambient irreducibility and perfectness of
the actual normal component orbit, without classifying solvable four-spaces.
Source: Aschbacher--Smith G.10.4(2), G.10.10--11, printed pp.358--360.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- The marked point lies in every large moved normal constituent stabilized by X. -/
theorem point_mem_normal_constituent (hi : ρ.IsIrreducible)
    (H : Subgroup G) [H.Normal]
    (I : Subrepresentation (ρ.comp H.subtype)) (hI : I.toRepresentation.IsIrreducible)
    (hdim : 3 ≤ finrank (ZMod 2) I.toSubmodule)
    (hs : X ≤ subspaceStabilizer ρ I.toSubmodule)
    (hm : ¬ I.toSubmodule ≤ fixedSpace ρ X) : v ∈ I.toSubmodule := by
  by_contra hv
  let K := H ⊔ X
  have hHI : H ≤ subspaceStabilizer ρ I.toSubmodule :=
    le_subspaceStabilizer ρ I.toSubmodule (fun g hg u hu => I.apply_mem_toSubmodule ⟨g,hg⟩ hu)
  have hKI : K ≤ subspaceStabilizer ρ I.toSubmodule := sup_le hHI hs
  let J : Subrepresentation (ρ.comp K.subtype) :=
    ⟨I.toSubmodule, fun g u hu => (hKI g.property u).2 hu⟩
  have hIa : IsAtom I := (Subrepresentation.irreducible_iff_isAtom I).mp hI
  have hJ : IsIrreducible J.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom J).mpr
    rw [isAtom_iff_le_of_ge]
    refine ⟨fun he => hIa.ne_bot (Subrepresentation.toSubmodule_injective
      (congrArg (fun D : Subrepresentation (ρ.comp K.subtype) => D.toSubmodule) he)), ?_⟩
    intro D hD0 hDJ
    let D' : Subrepresentation (ρ.comp H.subtype) :=
      ⟨D.toSubmodule, fun g u hu => D.apply_mem_toSubmodule ⟨g,(le_sup_left : H ≤ K) g.property⟩ hu⟩
    have hD'0 : D' ≠ ⊥ := fun he => hD0 (Subrepresentation.toSubmodule_injective
      (congrArg (fun A : Subrepresentation (ρ.comp H.subtype) => A.toSubmodule) he))
    have he : D' = I := (hIa.le_iff_eq hD'0).mp hDJ
    exact (congrArg Subrepresentation.toSubmodule he).ge
  let := hJ
  obtain ⟨horth,hd⟩ := h.lagrangian_of_large_moved_space K le_sup_right J hv hm hdim
  have hr (x : X) := h.displacement_rank_le_two_of_moved_space I.toSubmodule hs hv hm x
  let c := conjugateSubrepresentationOrderIso ρ H
  have hca (g : G) : IsAtom (c g I) := ((c g).isAtom_iff I).mpr hIa
  have hcd (g : G) : finrank (ZMod 2) (c g I).toSubmodule = finrank (ZMod 2) I.toSubmodule := by
    rw [conjugateSubrepresentationOrderIso_toSubmodule]
    exact finrank_map_action ρ I.toSubmodule g
  have hcx (g : G) : X ≤ subspaceStabilizer ρ (c g I).toSubmodule := by
    intro x hx
    apply (subspace_map_eq_iff ρ _ x).mp
    apply map_constituent_eq_self_of_displacement_lt ρ H x (c g I)
      ((Subrepresentation.irreducible_iff_isAtom _).mpr (hca g))
    have hh := hr ⟨x,hx⟩
    change finrank (ZMod 2) (LinearMap.range (ρ x - LinearMap.id)) ≤ 2 at hh
    rw [hcd]
    omega
  have hother (g : G) (hne : c g I ≠ I) : v ∈ (c g I).toSubmodule := by
    have hdis : Disjoint I.toSubmodule (c g I).toSubmodule := by
      rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule (hIa.disjoint_of_ne (hca g) hne.symm).eq_bot
    have hcompl : IsCompl I.toSubmodule (c g I).toSubmodule := by
      refine ⟨hdis,codisjoint_iff.mpr ?_⟩
      apply Submodule.eq_top_of_finrank_eq
      have he := Submodule.finrank_sup_add_finrank_inf_eq I.toSubmodule (c g I).toSubmodule
      rw [hdis.eq_bot,finrank_bot,add_zero,hcd] at he
      change finrank (ZMod 2) V = 2 * finrank (ZMod 2) I.toSubmodule at hd
      omega
    exact h.point_mem_complement_of_large_moved_lagrangian I.toSubmodule
      (c g I).toSubmodule hs hv hm hdim horth hcompl (hcx g)
  obtain ⟨a,ha⟩ : ∃ a : G, c a I ≠ I := by
    by_contra! hall
    let A : Subrepresentation ρ := ⟨I.toSubmodule, by
      intro g u hu
      have he := congrArg Subrepresentation.toSubmodule (hall g)
      rw [conjugateSubrepresentationOrderIso_toSubmodule] at he
      exact he ▸ (Submodule.mem_map_of_mem hu)⟩
    have hA0 : A ≠ ⊥ := fun he => hIa.ne_bot (Subrepresentation.toSubmodule_injective
      (congrArg (fun D : Subrepresentation ρ => D.toSubmodule) he))
    have ht := (hi.eq_bot_or_eq_top A).resolve_left hA0
    exact hv (show v ∈ A.toSubmodule from ht ▸ Submodule.mem_top)
  have hva := hother a ha
  have htwo (g : G) : c g I = I ∨ c g I = c a I := by
    by_cases hg : c g I = I
    · exact Or.inl hg
    right
    by_contra hn
    have hdis := (hca g).disjoint_of_ne (hca a) hn
    have hz : v ∈ (c g I ⊓ c a I).toSubmodule := ⟨hother g hg,hva⟩
    rw [hdis.eq_bot] at hz
    exact h.point_ne_zero hz
  have hswap (g : G) (hg : c g I = c a I) : c g (c a I) = I := by
    have hh := htwo (g*a)
    rw [conjugateSubrepresentationOrderIso_mul] at hh
    rcases hh with hh | hh
    · exact hh
    · exact (ha ((c g).injective (hh.trans hg.symm))).elim
  let N := subspaceStabilizer ρ I.toSubmodule
  have hmem (g : G) : g ∈ N ↔ c g I = I := by
    rw [← subspace_map_eq_iff]
    rw [← conjugateSubrepresentationOrderIso_toSubmodule ρ H g I]
    exact ⟨fun he => Subrepresentation.toSubmodule_injective he,
      fun he => congrArg (fun D : Subrepresentation (ρ.comp H.subtype) => D.toSubmodule) he⟩
  have hind : N.index = 2 := by
    apply index_eq_two_iff_exists_notMem_and.mpr
    refine ⟨a,fun ha' => ha ((hmem a).mp ha'),fun g => ?_⟩
    rcases htwo g with hg | hg
    · exact Or.inr ((hmem g).mpr hg)
    · left
      apply (hmem (g*a)).mpr
      rw [conjugateSubrepresentationOrderIso_mul]
      exact hswap g hg
  have hpoint : pointCentralizer ρ v ≤ N := by
    intro g hg
    apply (hmem g).mpr
    rcases htwo g with hgI | hgI
    · exact hgI
    · have hm : ρ g v ∈ (c g (c a I)).toSubmodule := by
        rw [conjugateSubrepresentationOrderIso_toSubmodule]
        exact Submodule.mem_map_of_mem hva
      rw [hswap g hgI] at hm
      exact (hv (hg ▸ hm)).elim
  have hdiv := index_dvd_of_le hpoint
  rw [hind] at hdiv
  exact h.odd_index.not_two_dvd_nat hdiv

/-- G.10.10: every nonzero HX-invariant space contains the marked point. -/
theorem point_mem_normal_component_subspace (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (S : Sylow 2 G) (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hind : (normalizer (L : Set G)).index ≤ 2)
    (U : Submodule (ZMod 2) V) (hU : componentOrbit L ⊤ ≤ subspaceStabilizer ρ U)
    (hXU : X ≤ subspaceStabilizer ρ U) (hU0 : U ≠ ⊥) : v ∈ U := by
  by_contra hv
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hi := h.irreducible_of_not_solvable hn
  have hnker : ¬ H ≤ ρ.ker := by
    intro hk
    apply hL.componentOrbit_top_ne_bot
    apply le_bot_iff.mp
    intro g hg
    apply mem_bot.mpr
    apply h.faithful
    exact (hk hg).trans (map_one ρ).symm
  let R : Subrepresentation (ρ.comp H.subtype) :=
    ⟨U,fun g u hu => (hU g.property u).2 hu⟩
  have hR0 : R ≠ ⊥ := fun he => hU0 (congrArg Subrepresentation.toSubmodule he)
  obtain ⟨I,hIa,hIR⟩ := (eq_bot_or_exists_atom_le R).resolve_left hR0
  have hI : I.toRepresentation.IsIrreducible := (Subrepresentation.irreducible_iff_isAtom I).mpr hIa
  have hdim := PerfectInvolutionExtension.constituent_dimension ρ hi H hnker I hI
  have hmove := h.normal_component_subspace_not_fixed hn hL hm S hnX hind U hU hU0
  have hXI : X ≤ subspaceStabilizer ρ I.toSubmodule := by
    intro x hx
    apply (subspace_map_eq_iff ρ _ x).mp
    apply map_constituent_eq_self_of_displacement_lt ρ H x I hI
    have hr := h.displacement_rank_le_two_of_moved_space U hXU hv hmove ⟨x,hx⟩
    change finrank (ZMod 2) (LinearMap.range (ρ x - LinearMap.id)) ≤ 2 at hr
    omega
  have hHI : componentOrbit L ⊤ ≤ subspaceStabilizer ρ I.toSubmodule :=
    le_subspaceStabilizer ρ I.toSubmodule (fun g hg u hu => I.apply_mem_toSubmodule ⟨g,hg⟩ hu)
  have hI0 : I.toSubmodule ≠ ⊥ := fun he => hIa.ne_bot (Subrepresentation.toSubmodule_injective he)
  have hmoveI := h.normal_component_subspace_not_fixed hn hL hm S hnX hind
    I.toSubmodule hHI hI0
  exact hv (hIR (h.point_mem_normal_constituent hi H I hI hdim hXI hmoveI))

/-- G.10.11 for the selected normal component orbit, in both directions. -/
theorem point_mem_iff_stabilizes_component_constituent (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (S : Sylow 2 G) (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hind : (normalizer (L : Set G)).index ≤ 2)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ (componentOrbit L ⊤) I) :
    v ∈ I ↔ X ≤ subspaceStabilizer ρ I := by
  let := componentOrbit_top_normal L
  exact ⟨h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn)
      (componentOrbit L ⊤) hI,
    fun hx => h.point_mem_normal_component_subspace hn hL hm S hnX hind I hI.choose hx (hI.ne_bot ρ)⟩

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
