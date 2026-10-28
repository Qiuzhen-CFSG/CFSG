module
public import CFSG.Quasithin.Chapter3.Section02.InternalFromReducedSeed
public import Theory.GroupTheory.ReducedNormal.SubspaceGroupConsequences
public import Theory.GroupTheory.ReducedNormal.SubspaceQuotientConsequences

/-!
# The original orbit module under both source actor alternatives

Embed the original seed into the reduced module of M and apply the
proved internal D.3.3–4 action. Transport the commutator and fixed-space
identities, TI conclusion, and semisimplicity to the original subgroups.
The quotient representation below acts on the literal quotient V_M/C_{V_M}(X);
its displayed conjugation formula identifies this action without a model choice.

Both the component-orbit and the odd-prime actor alternatives are retained.
Source: Aschbacher–Smith, Lemma 3.2.2(3–5), combined manuscript
of 1 March 2004, printed p.579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
  [(X.subgroupOf M).Normal]
  (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
  (hX : pResidual 2 (X.subgroupOf M) = ⊤)
  (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
    le_normalizer_of_normal)
  (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
  (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
    (X.subgroupOf (X ⊔ (T : Subgroup G))) I)

local notation "V₀" => ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I
local notation "V_M" => componentOrbit V₀ M
local notation "V_T" => componentOrbit V₀ (T : Subgroup G)

include hXM hTM hG hM hX hc hI

theorem source_reduced_seed_orbit_elementary : IsElementaryAbelian 2 V_M := by
  obtain ⟨J, hJ, hi⟩ := source_reduced_seed_internal T X M hXM hTM hG hM hX hc I hI
  have hm := ReducedNormal.subspaceImage_orbitSpan M M le_rfl J
  rw [subgroupOf_self, hJ] at hm
  exact hm ▸ ReducedNormal.subspaceImage_elementary M (orbitSpan _ ⊤ J)

theorem source_reduced_seed_orbit_eq_commutator : V_M = ⁅V_M, X⁆ := by
  obtain ⟨J, hJ, hi⟩ := source_reduced_seed_internal T X M hXM hTM hG hM hX hc I hI
  have he := ReducedNormal.seedOrbit_eq_commutator M X hXM hi.seed
  rwa [hJ] at he

theorem source_reduced_seed_centralizer_orbits :
    V_M ⊓ centralizer (X : Set G) = componentOrbit (V₀ ⊓ centralizer (X : Set G)) M ∧
      V_M ⊓ centralizer (X : Set G) = componentOrbit (V_T ⊓ centralizer (X : Set G)) M := by
  obtain ⟨J, hJ, hi⟩ := source_reduced_seed_internal T X M hXM hTM hG hM hX hc I hI
  have he := ReducedNormal.seedOrbit_inf_centralizer M X hXM hi.seed
  rw [hJ] at he
  refine ⟨he, le_antisymm ?_ ?_⟩
  · rw [he]
    exact iSup_le fun g => (map_mono (inf_le_inf_right _ (le_componentOrbit V₀ T))).trans
      (le_iSup (fun g : M => (V_T ⊓ centralizer (X : Set G)).map
        (MulAut.conj (g : G)).toMonoidHom) g)
  · have hTVM : V_T ≤ V_M := iSup_le fun t => le_iSup_of_le
      (⟨t.val, hTM t.property⟩ : M) le_rfl
    have hMX : M ≤ normalizer (X : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hXM).mp inferInstance
    apply iSup_conjugates_le_of_le_normalizer _ _ _ (inf_le_inf_right _ hTVM)
    exact (le_inf (le_normalizer_componentOrbit V₀ M)
      (hMX.trans (normalizer_le_normalizer_centralizer X))).trans
        inf_normalizer_le_normalizer_inf

theorem source_reduced_seed_ti (hzero : V₀ ⊓ centralizer (X : Set G) = ⊥) (g : M) :
    V₀ ⊓ (V₀).map (MulAut.conj (g : G)).toMonoidHom = ⊥ ∨
      (V₀).map (MulAut.conj (g : G)).toMonoidHom = V₀ := by
  obtain ⟨J, hJ, hi⟩ := source_reduced_seed_internal T X M hXM hTM hG hM hX hc I hI
  have he := ReducedNormal.seed_ti_of_centralizer_eq_bot M X hXM hi.seed
    (by rwa [hJ]) g
  rwa [hJ] at he

theorem source_reduced_seed_quotient_consequences :
    letI := source_reduced_seed_orbit_elementary T X M hXM hTM hG hM hX hc I hI
    ∃ σ : Representation (ZMod 2) M
        (Additive (V_M ⧸ (centralizer (X : Set G)).subgroupOf V_M)),
      Representation.IsSemisimpleRepresentation (σ.comp (X.subgroupOf M).subtype) ∧
      (∀ A B : Subrepresentation (σ.comp (X.subgroupOf M).subtype),
        Representation.IsIrreducible A.toRepresentation →
        Representation.IsIrreducible B.toRepresentation →
        ∃ g : M, (homogeneousPart A ⊤).map (σ g) = homogeneousPart B ⊤) ∧
      (∀ (g : M) (v : V_M),
        σ g (Additive.ofMul (QuotientGroup.mk'
          ((centralizer (X : Set G)).subgroupOf V_M) v)) =
          Additive.ofMul (QuotientGroup.mk' ((centralizer (X : Set G)).subgroupOf V_M)
            ⟨(g : G) * (v : G) * (g : G)⁻¹,
              (mem_normalizer_iff.mp (le_normalizer_componentOrbit V₀ M g.property) v).mp
                v.property⟩)) := by
  let := source_reduced_seed_orbit_elementary T X M hXM hTM hG hM hX hc I hI
  obtain ⟨J, hJ, hi⟩ := source_reduced_seed_internal T X M hXM hTM hG hM hX hc I hI
  have hm := ReducedNormal.subspaceImage_orbitSpan M M le_rfl J
  rw [subgroupOf_self, hJ] at hm
  exact ReducedNormal.exists_actual_quotient_consequences M
    (orbitSpan (ReducedNormal.representation M) ⊤ J) (orbitSpan_invariant _ ⊤ J)
    X hXM hi.seed rfl V_M hm (le_normalizer_componentOrbit V₀ M)

end CFSG.Quasithin.Chapter3.Section02
