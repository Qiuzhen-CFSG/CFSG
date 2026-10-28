module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.F9Kernel
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullAction
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointQuotient
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.CommutatorLifting
public import CFSG.Quasithin.ChapterF.Section09.SeedNormalizer
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer

/-!
# Conditional F.9.1 application on the original six-space

The original chosen module and its actual fixed-space quotient supply the
full coordinates. Local uniqueness, characteristic two and the index-two
perpendicular kernel argument prove F.9.1(a),(c),(d). The original FSU
module proves reducedness and C_T(V)=O₂(LT), and the extended permutation
action proves normalization of V₅ by L₁T.

The earlier conditional interfaces are retained. The final application
constructs both point-quotient irreducibility and commutator lifting, the
latter using preservation of the form and singular-line displacement.
It also constructs the perpendicular centralizer equality, the four
abelian equivalences of 12.6.25 and the initial star-quotient conclusions
of 12.6.26. Only the stated earlier-source inputs remain in this F.9
application; the abelian-span theorem and 12.6.34 are still unproved.

Source: Aschbacher--Smith, 12.6.24(7), printed pp.830--831, and
Hypothesis F.9.1, printed pp.317--318.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Conditional literal F.9 application retaining explicit irreducibility
and commutator lifting; the kernel, reducedness,
local normalization, characteristic two and generated-core conditions
are constructed from the original source setup. -/
theorem SourceHypothesis.original_f9_of_local_geometry
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hirr : ∀ W : Subgroup G, (D.fullSetup hZ T z).V₁ ≤ W →
      W ≤ (D.fullSetup hZ T z).V₅ →
      (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤ normalizer (W : Set G) →
      W = (D.fullSetup hZ T z).V₁ ∨ W = (D.fullSetup hZ T z).V₅)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hlift : ∀ g ∈ H,
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom →
      ⁅(D.fullSetup hZ T z).V₅,V.map (MulAut.conj g).toMonoidHom⁆ ≤ (D.fullSetup hZ T z).V₁ →
      ⁅((D.fullSetup hZ T z).V₅).map (MulAut.conj g).toMonoidHom,V⁆ ≤ (D.fullSetup hZ T z).V₁ →
      ⁅(D.fullSetup hZ T z).V₅,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
        ⁅((D.fullSetup hZ T z).V₅).map (MulAut.conj g).toMonoidHom,V⁆ = ⊥) :
    ((D.fullSetup hZ T z).f9 H).Hypothesis := by
  let E := D.fullSetup hZ T z
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have horbit : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hTV)
      (le_componentOrbit V T)
  have hred := (S.chosen.fundamentalSetup S.source.toHypothesis1221).module_reduced hu
  rw [S.chosen.fundamentalSetup_module,horbit] at hred
  have hcent := (S.chosen.fundamentalSetup S.source.toHypothesis1221).sylow_centralizer_module hu
  rw [S.chosen.fundamentalSetup_module,horbit] at hcent
  refine {
    elementary := S.chosen.elementary
    residual := S.local_residual_characteristic.1
    normalizes_L := S.chosen.sylow_normalizes_component
    characteristic_L := S.local_residual_characteristic.2
    V_le_LT := S.chosen.le_sylow.trans le_sup_right
    reduced := ?_
    sylow_centralizer := ?_
    point_card := E.point_card hz
    normalizes_point := hTz
    point_lt := E.point_lt_perpendicular hz
    plus_le := E.V₅_le
    H_centralizes := hH.2.1
    local_le := sup_le (fun x hx => hH.1.2 (Or.inl hx))
      (fun x hx => hH.1.2 (Or.inr hx))
    characteristic_H := S.point_local_characteristic D hZ z hH
    kernel_core := S.original_point_kernel D hZ z hz hTV hbound hH
    local_normalizes := S.original_local_normalizes_perpendicular D hZ z hz hTV hTz
    irreducible := hirr
    normalizer_control := le_inf inf_le_left
      (inf_le_right.trans (E.G₅_le_normalizer (E.perpendicular_card hz) hbound))
    generated_core := S.point_join_core_eq_bot D hZ z hH
    commutator_lifting := hlift }
  · change IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G)))
    change IsPReduced 2 (V.subgroupOf
      (Chapter3.Section02.localOrbit T L ⊔ (T : Subgroup G))) at hred
    rwa [S.chosen.localOrbit_eq] at hred
  · change (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2
    simpa only [Chapter3.Section02.localJoin,S.chosen.localOrbit_eq] using hcent
/-- The literal F.9 application with point-quotient irreducibility proved
from the original Sylow action. Its only remaining local input is the
commutator lifting of F.9.1(e); earlier-source hypotheses stay explicit. -/
theorem SourceHypothesis.original_f9_of_commutator_lifting
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hlift : ∀ g ∈ H,
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom →
      ⁅(D.fullSetup hZ T z).V₅,V.map (MulAut.conj g).toMonoidHom⁆ ≤ (D.fullSetup hZ T z).V₁ →
      ⁅((D.fullSetup hZ T z).V₅).map (MulAut.conj g).toMonoidHom,V⁆ ≤ (D.fullSetup hZ T z).V₁ →
      ⁅(D.fullSetup hZ T z).V₅,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
        ⁅((D.fullSetup hZ T z).V₅).map (MulAut.conj g).toMonoidHom,V⁆ = ⊥) :
    ((D.fullSetup hZ T z).f9 H).Hypothesis :=
  S.original_f9_of_local_geometry D hZ z hz hTV hTz hbound
    (S.original_point_quotient_irreducible D hZ z hz hTz) hH hlift

/-- Literal F.9.1 from the earlier fixed-space and intersection conclusions.
Irreducibility, the normal-core condition and commutator lifting are proved. -/
theorem SourceHypothesis.original_f9_of_earlier_geometry
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ((D.fullSetup hZ T z).f9 H).Hypothesis :=
  S.original_f9_of_commutator_lifting D hZ z hz hTV hTz hbound hH
    (S.original_commutator_lifting D hZ z hz hTV hTz hH)

/-- All four source conditions of 12.6.25 are equivalent on the original
conjugate spans. The abelian conclusion 12.6.26 remains to be established. -/
theorem SourceHypothesis.original_abelian_criteria
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    (IsMulCommutative ((D.fullSetup hZ T z).UH H) ↔ V ≤ H.pCoreIn 2) ∧
    (V ≤ H.pCoreIn 2 ↔ V ≤ centralizer ((D.fullSetup hZ T z).UH H : Set G)) ∧
    (IsMulCommutative ((D.fullSetup hZ T z).UH H) ↔
      IsMulCommutative ((D.fullSetup hZ T z).VH H)) :=
  (D.fullSetup hZ T z).lemma_12_6_25
    (S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH)
    (S.original_perpendicular_centralizer D hZ z hz hTV hTz hbound)

/-- Original 12.6.24(2),(8): the point span lies in the intrinsic two-core,
which is exactly the kernel on that span modulo the same point line. -/
theorem SourceHypothesis.original_span_core_and_kernel
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
    (D.fullSetup hZ T z).UH H ≤ H.pCoreIn 2 ∧
      H.pCoreIn 2 = h.kernel ((D.fullSetup hZ T z).UH H) :=
  (D.fullSetup hZ T z).span_core_and_kernel
    (S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH)

/-- The opening F.9.5 deductions in 12.6.26, before the odd-core and
component exclusions. The star image uses H's intrinsic two-core. -/
theorem SourceHypothesis.original_nonabelian_geometry
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    ¬ IsMulCommutative ((D.fullSetup hZ T z).UH H) ∧
      Nat.card (Nonabelian.Setup.star H V) = 2 ∧
      V ⊓ H.pCoreIn 2 = (D.fullSetup hZ T z).V₅ ∧
      (D.fullSetup hZ T z).V₅ =
        (D.fullSetup hZ T z).V₁ ⊔ ⁅(D.fullSetup hZ T z).UH H,V⁆ ∧
      (centralizer (Nonabelian.Setup.star H V :
        Set (H ⧸ pCore 2 H))).comap (QuotientGroup.mk' (pCore 2 H)) =
        (normalizer (V : Set G)).subgroupOf H := by
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hC := S.original_perpendicular_centralizer D hZ z hz hTV hTz hbound
  obtain ⟨hu,hv,_⟩ := E.nonabelian_inputs h hC hn
  have hi := E.perpendicular_index hz
  exact ⟨hu,h.star_module_card_two hi hv,h.seed_eq_intersection_of_not_le_core hi hv,
    h.seed_eq_point_sup_commutator hi hv,h.star_centralizer_preimage hi hv⟩

end CFSG.Quasithin.Chapter12.Section06
