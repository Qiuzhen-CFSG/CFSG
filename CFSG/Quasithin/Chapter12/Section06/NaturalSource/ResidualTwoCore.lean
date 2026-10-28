module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ResidualPairAction
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.GroupTheory.BaerSuzukiLocal

/-!
# The literal residual section centralizer and its Baer--Suzuki obstruction

The source centralizer C_H(L₁/O₂(L₁)) is the subgroup of H normalizing
L₁ and acting trivially on its intrinsic two-core quotient. The original
V lies in it: V normalizes the residual, and [V,L₁] lies in the normal
two-subgroup V intersect L₁.

If V is outside this centralizer's two-core, relative Baer--Suzuki supplies
an actual conjugator in that same subgroup. The earlier marked pair
classification reduces this witness to D₁₀, with the product of the
original two generators of order five. ResidualPairAction applies to this
same conjugator and supplies the commuting faithful E₉ on both singular
four-spaces. The orthogonal exclusion, and hence the two-core assertion
itself, remain to be proved.

Source: Aschbacher--Smith, proof of 12.6.26, printed pp.831--832.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
variable {G : Type*} [Group G] (E : Nonabelian.Setup G)
/-- The literal relative section centralizer C_H(L₁/O₂(L₁)), including
normalization of L₁ and triviality of the induced quotient action. -/
@[expose] noncomputable def residualCentralizer (H : Subgroup G) : Subgroup G :=
  H ⊓ commutatorPreimage (normalizer (E.L₁ : Set G)) E.L₁ (E.L₁.pCoreIn 2)

/-- Membership is exactly trivial action on the original intrinsic quotient. -/
theorem mem_residualCentralizer (H : Subgroup G) (g : G) :
    g ∈ E.residualCentralizer H ↔ g ∈ H ∧
      ∃ hg : g ∈ normalizer (E.L₁ : Set G),
        pCoreNormalizerAction 2 E.L₁ ⟨g,hg⟩ = 1 := by
  have hn : normalizer (E.L₁ : Set G) ≤ normalizer (E.L₁.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image E.L₁ (pCore 2 E.L₁)
  rw [residualCentralizer,mem_inf,Subgroup.mem_commutatorPreimage_iff _ _ _ hn]
  constructor
  · rintro ⟨hg,hn,hc⟩
    refine ⟨hg,hn,(pCoreNormalizerAction_eq_one_iff 2 E.L₁ ⟨g,hn⟩).mpr ?_⟩
    intro x
    have hh := hc x x.property
    have he : E.L₁.normalizerMonoidHom ⟨g,hn⟩ x / x ∈ (E.L₁.pCoreIn 2).subgroupOf E.L₁ := by
      simpa only [mem_subgroupOf, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        normalizerMonoidHom_apply_apply_coe, commutatorElement_def] using hh
    rwa [show (E.L₁.pCoreIn 2).subgroupOf E.L₁ = pCore 2 E.L₁ from
      comap_map_eq_self_of_injective E.L₁.subtype_injective _] at he
  · rintro ⟨hg,hn,hc⟩
    refine ⟨hg,hn,fun x hx => ?_⟩
    have hh := (pCoreNormalizerAction_eq_one_iff 2 E.L₁ ⟨g,hn⟩).mp hc ⟨x,hx⟩
    simpa only [pCoreIn, div_eq_mul_inv, map_mul, map_inv, coe_subtype,
      normalizerMonoidHom_apply_apply_coe, commutatorElement_def] using
      mem_map_of_mem E.L₁.subtype hh
end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original V acts trivially on L₁/O₂(L₁); the action kernel
L₁ intersect O₂(L) is not identified with this quotient kernel. -/
theorem SourceHypothesis.original_module_le_residualCentralizer
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    V ≤ (D.fullSetup hZ T z).residualCentralizer H := by
  let E := D.fullSetup hZ T z
  let C := L ⊓ E.Gz
  have hVC : V ≤ C := le_inf
    (S.chosen.le_componentCore.trans (pCoreIn_le 2 L))
    (le_centralizer_iff.mpr (E.V₁_le_V₅.trans E.V₅_le |>.trans (le_centralizer V)))
  have hCN : C ≤ normalizer (E.L₁ : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))
  have hRL : E.L₁ ≤ L := (map_subtype_le _).trans inf_le_left
  have hRN : E.L₁ ≤ normalizer (V : Set G) := hRL.trans S.chosen.normalizes
  have hcore : V ⊓ E.L₁ ≤ E.L₁.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left)
      inf_le_right ((le_inf hRN E.L₁.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hcomm : ⁅V,E.L₁⁆ ≤ E.L₁.pCoreIn 2 :=
    (le_inf (le_normalizer_iff_commutator_le_left.mp hRN)
      (le_normalizer_iff_commutator_le_right.mp (hVC.trans hCN))).trans hcore
  exact le_inf (S.chosen.le_sylow.trans (fun x hx => hH.1.2 (Or.inr hx)))
    (le_commutatorPreimage (hVC.trans hCN) hcomm)

/-- Failure of the source's relative two-core bound produces an actual
conjugator in that same section centralizer, with a dihedral-ten pair and
the original rotation of order five. -/
theorem SourceHypothesis.original_residualCentralizer_obstruction
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hnH : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (hcore : ¬ V ≤ ((D.fullSetup hZ T z).residualCentralizer H).pCoreIn 2) :
    ∃ g ∈ (D.fullSetup hZ T z).residualCentralizer H,
      ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ∧
      let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
      ∃ (hIH : I ≤ H) (v : V), v.val ∉ (D.fullSetup hZ T z).V₅ ∧
        Nonempty (Nonabelian.Setup.star H I ≃* DihedralGroup 5) ∧
        orderOf (QuotientGroup.mk' (pCore 2 H) (inclusion hIH ⟨v.val,mem_sup_left v.property⟩) *
          QuotientGroup.mk' (pCore 2 H) (inclusion hIH ⟨(MulAut.conj g) v.val,
            mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom v.property)⟩))=5 := by
  let E := D.fullSetup hZ T z
  obtain ⟨g,hg,_,hn⟩ := exists_noncentralizing_conjugate_sup_not_isPGroup
    (E.residualCentralizer H) V (S.original_module_le_residualCentralizer D hZ z hH)
    (IsElementaryAbelian.isPGroup 2 V) hcore
  obtain ⟨hgH,hgL,_⟩ := (E.mem_residualCentralizer H g).mp hg
  exact ⟨g,hg,hn,S.original_normalizing_pair_dihedral_five D hZ z hz hTV hTz hbound hns
    hH hnH g hgH hgL hn⟩
end CFSG.Quasithin.Chapter12.Section06
