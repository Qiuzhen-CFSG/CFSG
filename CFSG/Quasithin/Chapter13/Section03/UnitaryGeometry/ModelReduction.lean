module

public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.IsotropicReduction
public import Theory.Representation.G2BinaryNondegeneratePlane.Movement

/-!
# Literal natural-module consumer of the isotropic reduction

Pull the proved alternating G₂ form through the actual chart of the original
chosen elementary abelian group. Nondegenerate planes correspond to actual
order-four subgroups under the subgroup/vector-space correspondence. The
original E.6 hypotheses then give the genuine rank lower bound and an attained
escaping isotropic three-space when r=3.

Source: Aschbacher–Smith, Lemma 13.3.12(2–3), printed p.890. The preceding
nonisotropic E₄ centralizer bound remains explicit here; the C.2 component and
chief-factor argument must supply it in the final source assembly.
-/

@[expose] public noncomputable section
open Module Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open Atlas.G2.Natural.BinaryNondegeneratePlane
variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G} [IsElementaryAbelian 2 V]

def markedForm (E : Additive V ≃ₗ[ZMod 2] W) : LinearMap.BilinForm (ZMod 2) (Additive V) :=
  LinearMap.BilinForm.congr E.symm form
omit [Finite G] in
theorem markedForm_alternating (E : Additive V ≃ₗ[ZMod 2] W) : (markedForm E).IsAlt :=
  fun x => form_alternating (E x)
omit [Finite G] in
theorem markedForm_nondegenerate (E : Additive V ≃ₗ[ZMod 2] W) : (markedForm E).Nondegenerate :=
  form_nondegenerate.congr E.symm
omit [Finite G] in
theorem ambientGroup_le_module (P : Submodule (ZMod 2) (Additive V)) : ambientGroup P≤V := by
  rintro x ⟨v,_,rfl⟩
  exact v.property

theorem ambientGroup_card (P : Submodule (ZMod 2) (Additive V)) :
    Nat.card (ambientGroup P)=2^finrank (ZMod 2) P := by
  rw [ambientGroup,Subgroup.card_map_of_injective V.subtype_injective]
  have he : Nat.card (subgroupSpace.symm P)=Nat.card P := rfl
  rw [he,Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod]

theorem plane_centralizers_of_four_subgroups
    (E : Additive V ≃ₗ[ZMod 2] W)
    (hFour : ∀l : Subgroup G,l≤V → Nat.card l=4 →
      ((markedForm E).restrict (ambientSpace (V:=V) l)).Nondegenerate → centralizer (l:Set G)≤M) :
    ∀P : Submodule (ZMod 2) (Additive V),finrank (ZMod 2) P=2 →
      ((markedForm E).restrict P).Nondegenerate → centralizer (ambientGroup P:Set G)≤M := by
  intro P hd hn
  apply hFour (ambientGroup P) (ambientGroup_le_module P)
  · rw [ambientGroup_card,hd]
    decide
  · rwa [ambientSpace_ambientGroup]

theorem natural_source_rank_reduction
    {K₀ : GroupClass} {T : Sylow 2 G}
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (E : Additive V ≃ₗ[ZMod 2] W)
    (hFour : ∀l : Subgroup G,l≤V → Nat.card l=4 →
      ((markedForm E).restrict (ambientSpace (V:=V) l)).Nondegenerate → centralizer (l:Set G)≤M) :
    3≤ChapterE.globalR V := by
  exact three_le_globalR_of_plane_centralizers h (markedForm E)
    (markedForm_alternating E) (markedForm_nondegenerate E)
    (E.finrank_eq.trans (by simp)) (plane_centralizers_of_four_subgroups E hFour)

theorem natural_source_three_space_reduction
    {K₀ : GroupClass} {T : Sylow 2 G}
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (E : Additive V ≃ₗ[ZMod 2] W)
    (hFour : ∀l : Subgroup G,l≤V → Nat.card l=4 →
      ((markedForm E).restrict (ambientSpace (V:=V) l)).Nondegenerate → centralizer (l:Set G)≤M)
    (hr : ChapterE.globalR V=3) :
    ∃U : Subgroup G,U≤V ∧ finrank (ZMod 2) (ambientSpace (V:=V) U)=3 ∧
      (∀x∈ambientSpace (V:=V) U,∀y∈ambientSpace (V:=V) U,markedForm E x y=0) ∧
      ¬centralizer (U:Set G)≤M :=
  exists_escaping_isotropic_three_space h (markedForm E) (markedForm_alternating E)
    (E.finrank_eq.trans (by simp)) (plane_centralizers_of_four_subgroups E hFour) hr
end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
