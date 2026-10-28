module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry.Endpoints
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry.MiddleGeneration
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry.MiddleRadical
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry.SylowDerivedCenter

/-!
# Invariant binary flag pairs

Without Dynkin action, `exists_invariant_endpoint_pair` constructs the two
end-node flags from the genuine local hypotheses and proves their invariance,
Sylow containment and generation. In degree five, `middle_generate` proves
that the {1,4} and {2,3} flags generate once their nested spaces are supplied.

The component Sylow intersection is preserved by N_S(L), which also fixes
the involution projection. `exists_invariant_middle_pair_of_derivedCenter`
constructs the complete {1,4}, {2,3} pair once Z(T′) is identified with the
rectangular translation group Hom(V/W₃,W₂). Its normalizer is the middle flag
stabilizer; characteristicity gives invariance and Sylow maximality gives the
projection membership needed for generation.

`exists_invariant_middle_pair` discharges the rectangular equality using the
actual degree-five Sylow calculation. `exists_invariant_flag_pair` assembles
the source cases: endpoint flags without Dynkin action, and the {1,4}, {2,3}
pair in the remaining degree-five case. Both stabilizers contain S ∩ L and
generate L. Invariance is required only under N_S(L), retaining permutations
of components by other elements of S.

Source: Aschbacher–Smith 2.3.9(7), printed pp.525–526, with the invariant
parabolic convention in the proof of E.2.2, printed p.216.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup
variable {G : Type*} [Group G] {L : Subgroup G}

/-- The component intersection is fixed by conjugation from its normalizer in S. -/
theorem component_intersection_fixed_by_normalizer (S₀ : Subgroup G)
    {s : G} (hs : s ∈ S₀) (hsL : s ∈ normalizer (L : Set G)) :
    (S₀.subgroupOf L).map (L.normalizerMonoidHom ⟨s, hsL⟩).toMonoidHom =
      S₀.subgroupOf L := by
  let α := L.normalizerMonoidHom ⟨s, hsL⟩
  have hα (x : L) : (α x : G) = s * (x : G) * s⁻¹ := rfl
  have hαi (x : L) : (α.symm x : G) = s⁻¹ * (x : G) * s := by
    calc
      (α.symm x : G) = s⁻¹ * (s * (α.symm x : G) * s⁻¹) * s := by group
      _ = s⁻¹ * (x : G) * s := by rw [← hα, α.apply_symm_apply]
  change (S₀.subgroupOf L).map α.toMonoidHom = _
  ext x
  rw [mem_map_equiv]
  change (α.symm x : G) ∈ S₀ ↔ (x : G) ∈ S₀
  rw [hαi, S₀.mul_mem_cancel_right hs, S₀.mul_mem_cancel_left (S₀.inv_mem hs)]

variable {H M : Subgroup G} {S : Sylow 2 H} {z : G} {n : ℕ} [NeZero n]

/-- The intrinsic normalizer action fixes the source's involution projection. -/
theorem projection_fixed_by_normalizer (h : LocalSetup H L M S z)
    (e : L ≃* PSL n) {t : L} (ht : IsConjugationProjection L z t)
    {s : G} (hs : s ∈ (S : Subgroup H).map H.subtype)
    (hsL : s ∈ normalizer (L : Set G)) :
    L.normalizerMonoidHom ⟨s, hsL⟩ t = t := by
  apply Subtype.ext
  change s * (t : G) * s⁻¹ = (t : G)
  rw [projection_centralizes_normalizer h e ht hs hsL, mul_inv_cancel_right]

/-- The characteristic subgroup calculation supplies the graph-invariant middle
flag. The rectangular matrix equality is the only extra input; Sylow
maximality supplies the projection membership, and characteristicity gives invariance. -/
theorem exists_invariant_middle_pair_of_derivedCenter
    (h : LocalSetup H L M S z) (e : L ≃* PSL 5) {t : L}
    (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2)
    (T : Sylow 2 L)
    (hT : (T : Subgroup L) = ((S : Subgroup H).map H.subtype).subgroupOf L)
    (W₂ W₃ : Space 5) (h₂ : Module.finrank (ZMod 2) W₂ = 2)
    (h₃ : Module.finrank (ZMod 2) W₃ = 3) (h₂₃ : W₂ ≤ W₃)
    (hQ : derivedCenter (T : Subgroup L) = subspaceRadical e W₂ ⊓ subspaceRadical e W₃) :
    ∃ F₁ F₂ : Flag 5,
      ExcludedFlagShape F₁ ∧ ExcludedFlagShape F₂ ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F₁ ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F₂ ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F₁ ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F₂ ∧
      flagStabilizer e F₁ ⊔ flagStabilizer e F₂ = ⊤ := by
  have htT := projection_mem_center_component_sylow h e ht ht2 T hT
  obtain ⟨c⟩ := projection_transvectionCoordinates h (Or.inr rfl) e ht ht2
  let F₁ := c.flag (by decide)
  let F₂ := middleFlag W₂ W₃ h₂ h₃ h₂₃
  have hW₂ : W₂ ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at h₂
    omega
  have hW₃ : W₃ ≠ ⊤ := by
    intro he
    rw [he, finrank_top, Module.finrank_fin_fun] at h₃
    omega
  have hK₂ : flagStabilizer e F₂ = normalizer (derivedCenter (T : Subgroup L) : Set L) := by
    rw [hQ, normalizer_subspaceRadical_inf e hW₂ hW₃ h₂₃]
    exact middleFlag_stabilizer e W₂ W₃ h₂ h₃ h₂₃
  have hTK₂ : (T : Subgroup L) ≤ flagStabilizer e F₂ := by
    rw [hK₂]
    exact le_normalizer_derivedCenter (T : Subgroup L)
  have hRnorm : (T : Subgroup L) ≤ normalizer (subspaceRadical e W₃ : Set L) :=
    hTK₂.trans (flagStabilizer_normalizes_subspaceRadical e F₂ (by simp [F₂, middleFlag]))
  have hRT : subspaceRadical e W₃ ≤ (T : Subgroup L) := by
    have he := T.is_maximal' (T.isPGroup'.to_sup_of_normal_right'
      (subspaceRadical_isPGroup e W₃) hRnorm) le_sup_left
    exact he ▸ le_sup_right
  have hW₃0 : W₃ ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at h₃
    omega
  have htW₃ : t ∈ subspaceRadical e W₃ :=
    centralizer_subspaceRadical_le e hW₃0 hW₃
      (mem_centralizer_iff.mpr (fun x hx => htT.2 x (hRT hx)))
  have h₃h : W₃ ≤ c.hyperplane := c.le_hyperplane_of_mem_radical htW₃
  refine ⟨F₁, F₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl (by simpa using c.flag_types (by decide))))⟩
  · exact Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (middleFlag_types W₂ W₃ h₂ h₃ h₂₃)))⟩
  · exact c.flag_invariant (by decide) h ht
  · apply flagInvariant_of_stabilizer_maps
    intro s hs hsL
    rw [hK₂, map_equiv_normalizer_eq, derivedCenter_map]
    have hm := component_intersection_fixed_by_normalizer
      ((S : Subgroup H).map H.subtype) hs hsL
    rw [← hT] at hm
    rw [hm]
  · rw [← hT, ← c.centralizer_eq_flag]
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((projection_mem_center_component_sylow h e ht ht2 T hT).2 x hx)
  · rw [← hT, hK₂]
    exact le_normalizer_derivedCenter (T : Subgroup L)
  · exact c.middle_generate W₂ W₃ h₂ h₃ h₂₃ h₃h

/-- The actual degree-five Sylow derived-center calculation constructs the
invariant {1,4}, {2,3} pair, including when the Dynkin action is nontrivial. -/
theorem exists_invariant_middle_pair
    (h : LocalSetup H L M S z) (e : L ≃* PSL 5) {t : L}
    (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    ∃ F₁ F₂ : Flag 5,
      ExcludedFlagShape F₁ ∧ ExcludedFlagShape F₂ ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F₁ ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F₂ ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F₁ ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F₂ ∧
      flagStabilizer e F₁ ⊔ flagStabilizer e F₂ = ⊤ := by
  obtain ⟨T, hT⟩ := exists_component_sylow h
  obtain ⟨W₂, W₃, h₂, h₃, h₂₃, hQ⟩ := exists_middle_pair_of_five_sylow e T
  exact exists_invariant_middle_pair_of_derivedCenter h e ht ht2 T hT
    W₂ W₃ h₂ h₃ h₂₃ hQ

/-- The generating invariant parabolic flags used to exclude the binary cases
in 2.3.9(7): degree five, or degree four with trivial Dynkin action. The two
end-node flags suffice without Dynkin action; degree five also admits the
{1,4}, {2,3} pair. Only the component normalizer in S acts on each stabilizer. -/
theorem exists_invariant_flag_pair
    (h : LocalSetup H L M S z) (e : L ≃* PSL n)
    (hn : n = 5 ∨ n = 4 ∧
      ¬ NontrivialDynkinAction e ((S : Subgroup H).map H.subtype))
    {t : L} (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    ∃ F₁ F₂ : Flag n,
      ExcludedFlagShape F₁ ∧ ExcludedFlagShape F₂ ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F₁ ∧
      FlagInvariant e ((S : Subgroup H).map H.subtype) F₂ ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F₁ ∧
      ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F₂ ∧
      flagStabilizer e F₁ ⊔ flagStabilizer e F₂ = ⊤ := by
  by_cases hd : ¬ NontrivialDynkinAction e ((S : Subgroup H).map H.subtype)
  · exact exists_invariant_endpoint_pair h
      (hn.elim Or.inr (fun h₄ => Or.inl h₄.1)) e ht ht2 hd
  · rcases hn with rfl | ⟨_, h₄⟩
    · exact exists_invariant_middle_pair h e ht ht2
    · exact (hd h₄).elim

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
