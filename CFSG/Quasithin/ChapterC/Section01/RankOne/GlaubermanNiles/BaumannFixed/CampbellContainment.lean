module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellSetup
public import Theory.GroupTheory.ElementaryThompsonReplacement

/-!
# Campbell containment from the natural-module fixed-point bound

For `Q = O₂(G)` and `E = Ω₁(Z(Q))`, the unconditional containments
`[S,V] ≤ F` and `V ≤ E ≤ F` reduce all marked containments to `F ≤ J(S)`.
A maximum elementary subgroup of `S` lying in `Q` makes the entire maximum
family of `Q` a subfamily of that of `S`, hence `J(Q) ≤ J(S)`.

The replacement `(A ∩ Q)E` supplies such a subgroup from the fixed-point
index bound used at the start of Campbell II.4.1. The source of that bound
is II.3.2: the natural action on the quotient of the normal closure of
`Ω₁(Z(S))`, together with `S = AQ`. It remains an explicit mathematical
premise here; these conditional results do not prove II.3.2. Failure of
factorization does independently force a maximum elementary subgroup
outside `Q`, as proved below.

Source: Neville Ray Campbell, *Pushing up in Finite Groups* (1979),
Chapter II §§2–4, especially printed pp.24–25,
https://thesis.caltech.edu/17847/.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles.Campbell

open Theory.GroupTheory Stellmacher
open scoped Pointwise

variable {T : Type*} [Group T] {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem omega_le (Q : Subgroup G) : omegaOneCenterAmbient Q ≤ Q :=
  fun x hx => ((mem_omegaOneCenterAmbient_iff Q x).mp hx).1

omit [Finite G] in
private theorem omega_centralizes (Q : Subgroup G) :
    omegaOneCenterAmbient Q ≤ Subgroup.centralizer (Q : Set G) :=
  fun x hx => Subgroup.mem_centralizer_iff.mpr
    ((mem_omegaOneCenterAmbient_iff Q x).mp hx).2.2

omit [Finite G] in
/-- The omega-center of the two-core is normal. -/
theorem omegaCore_normal : (omegaOneCenterAmbient (pCore 2 G)).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  change (omegaOneCenterAmbient (pCore 2 G)).map (MulAut.conj g).toMonoidHom = _
  rw [← omegaOneCenterAmbient_map_injective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective]
  have hQ : (pCore 2 G).map (MulAut.conj g).toMonoidHom = pCore 2 G := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    rw [Subgroup.normalizer_eq_top]
    trivial
  rw [hQ]

/-- A central elementary subgroup of `Q` centralizes `J(Q)`, hence lies in `F`. -/
theorem omegaCore_le_F : omegaOneCenterAmbient (pCore 2 G) ≤ F G := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (pCore 2 G)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  apply elementary_centralizer_maxJ_le_omegaCenter (pCore 2 G) _ (omega_le _)
  have hJQ : elementaryAbelianMaxJ (pCore 2 G) ≤ pCore 2 G :=
    sSup_le fun _ hA => hA.1
  exact (omega_centralizes _).trans (Subgroup.centralizer_le hJQ)

omit [Finite G] in
/-- The defining commutator of `V` lies in the normal omega-center. -/
theorem V_le_omegaCore : V G ≤ omegaOneCenterAmbient (pCore 2 G) := by
  let : (omegaOneCenterAmbient (pCore 2 G)).Normal := omegaCore_normal
  change ⁅(⊤ : Subgroup G), omegaOneCenterAmbient (pCore 2 G)⁆ ≤ _
  exact @Subgroup.commutator_le_right G _ (⊤ : Subgroup G) _ omegaCore_normal

/-- The Campbell commutator subgroup always lies in `F`. -/
theorem V_le_F : V G ≤ F G := V_le_omegaCore.trans omegaCore_le_F

/-- The Sylow commutator with `V` also lies in `F`. -/
theorem sylow_commutator_V_le_F (d : Embedding T G) :
    ⁅(d.sylow : Subgroup G), V G⁆ ≤ F G :=
  (Subgroup.commutator_mono le_top V_le_omegaCore).trans V_le_F

/-- The fixed-point index consequence of Campbell II.3.2 needed by II.4.1.
This is an explicit source input, not a field of `Embedding`. -/
def Embedding.OmegaFixedIndexBound (d : Embedding T G) : Prop :=
  ∀ A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup G),
    ¬ A ≤ pCore 2 G →
    (pCore 2 G).relIndex A ≤
      (Subgroup.centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (pCore 2 G))

omit [Finite G] in
private theorem core_thompson_normal : (J (pCore 2 G)).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  change (elementaryAbelianMaxJ (pCore 2 G)).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv]
  have hQ : (pCore 2 G).map (MulAut.conj g).toMonoidHom = pCore 2 G := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    rw [Subgroup.normalizer_eq_top]
    trivial
  rw [hQ]
  rfl

/-- If `J(S)` lay in the core, it would equal the normal `J(Q)`, contradicting
failure of the literal setwise factorization. -/
theorem Embedding.thompson_not_le_pCore (d : Embedding T G)
    (hf : d.FactorizationFails) : ¬ J (d.sylow : Subgroup G) ≤ pCore 2 G := by
  intro hJQ
  have hQS : pCore 2 G ≤ (d.sylow : Subgroup G) :=
    pCore_isPGroup.le_sylow_of_normal d.sylow
  have hs := elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ hQS
  have ht := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le _ _ hJQ
  have he := le_antisymm hs.1 ht.1
  have hJ : J (pCore 2 G) = J (d.sylow : Subgroup G) :=
    le_antisymm (hs.2 he) (ht.2 he.symm)
  let : d.marking.range.Normal := by
    rw [d.range_eq, ← hJ]
    exact core_thompson_normal
  apply hf
  rw [Subgroup.normalizer_eq_top]
  apply Set.eq_univ_of_forall
  intro g
  exact ⟨1, Subgroup.one_mem _, g, Subgroup.mem_top _, one_mul g⟩

/-- Failure of factorization supplies an elementary maximum outside the core,
as required for the source natural-module theorem. -/
theorem Embedding.exists_maxElementary_not_le_pCore (d : Embedding T G)
    (hf : d.FactorizationFails) :
    ∃ A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup G), ¬ A ≤ pCore 2 G := by
  by_contra h
  push Not at h
  exact d.thompson_not_le_pCore hf (sSup_le fun A hA => h A hA)

/-- Campbell II.4.1: the replacement gives a maximum elementary subgroup
of the Sylow group lying in the two-core. -/
theorem Embedding.exists_maxElementary_le_pCore_of_fixedIndex (d : Embedding T G)
    (hb : d.OmegaFixedIndexBound) :
    ∃ B ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup G), B ≤ pCore 2 G := by
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty (d.sylow : Subgroup G)
  by_cases hAQ : A ≤ pCore 2 G
  · exact ⟨A, hA, hAQ⟩
  · let : IsElementaryAbelian 2 (omegaOneCenterAmbient (pCore 2 G)) :=
      omegaOneCenterAmbient_elementaryAbelian _
    exact ⟨(A ⊓ pCore 2 G) ⊔ omegaOneCenterAmbient (pCore 2 G),
      maxElementary_inf_sup_mem_of_fixedIndex _ _ _ _ (pCore_isPGroup.le_sylow_of_normal d.sylow)
        (omega_le _) (omega_centralizes _) hA (hb A hA hAQ),
      sup_le inf_le_right (omega_le _)⟩

/-- Campbell II.4.1(v), conditional on the preceding natural-module index bound. -/
theorem Embedding.core_maxFamily_subset_of_fixedIndex (d : Embedding T G)
    (hb : d.OmegaFixedIndexBound) :
    elementaryAbelianMaxSubgroups (pCore 2 G) ⊆
      elementaryAbelianMaxSubgroups (d.sylow : Subgroup G) := by
  obtain ⟨B, hB, hBQ⟩ := d.exists_maxElementary_le_pCore_of_fixedIndex hb
  intro A hA
  exact ⟨hA.1.trans (pCore_isPGroup.le_sylow_of_normal d.sylow), hA.2.1,
    fun C hCS hCe => (hB.2.2 C hCS hCe).trans (hA.2.2 B hBQ hB.2.1)⟩

/-- All three containments on the literal marking, with only the source
fixed-point index consequence still to be supplied. -/
theorem Embedding.marked_containments_of_fixedIndex (d : Embedding T G)
    (hb : d.OmegaFixedIndexBound) :
    F G ≤ d.marking.range ∧ V G ≤ d.marking.range ∧
      ⁅(d.sylow : Subgroup G), V G⁆ ≤ d.marking.range := by
  have hJ : J (pCore 2 G) ≤ J (d.sylow : Subgroup G) :=
    sSup_le fun A hA => le_sSup (d.core_maxFamily_subset_of_fixedIndex hb hA)
  have hF : F G ≤ d.marking.range := by
    rw [d.range_eq]
    exact (omega_le _).trans hJ
  exact ⟨hF, V_le_F.trans hF, (sylow_commutator_V_le_F d).trans hF⟩

end CFSG.Quasithin.ChapterC.GlaubermanNiles.Campbell

end
