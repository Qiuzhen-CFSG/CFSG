module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OriginalOvergroupFF
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.IntrinsicOvergroupCore

/-!
# Original tensor FF application with intrinsic cubic action

The actual original component supplies its own cubic action on the tensor
line. This discharges every separate Cartan and cubic hypothesis in the
original old-residual FF application. Source 9.3.6–9.3.7; the earlier old
quotient, stabilizer Sylow, nonzero core and line-centralization inputs remain.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem old_residual_overgroup_core_and_ff_intrinsic
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤ D.fullModule)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G)) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      letI := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N)) := by
  obtain ⟨d,hdL,hd3,hdn,hdc⟩ := m.exists_tensorLine_cubic
  have hLH : L ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_left
  exact m.old_residual_overgroup_core_and_ff hn houtside hcomm hH eK hSyl M₀
    (zpowers d) hcore hgen (zpowers_le.mpr (hLH hdL)) (zpowers_le.mpr hdn)
    d (mem_zpowers d) hd3 hdc hKU hmove
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
