module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceQuaternion
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.Intrinsic

/-!
# The selected original A₅ block in13.5.15

The proved core collapse identifies the actual K-core with V. Transport
its representative-level natural five-point coordinates through that
identification and apply the intrinsic block constructor. The original
K and its quotient map are retained. The final theorem chooses the pair
from the original normal A₆ source hypotheses and includes its quaternion
local core, discharging the block substitution without a fixed-T marking.

Source: Aschbacher–Smith,13.5.14(4),13.5.15(3,5), printed pp.919–920.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceFiveBlock
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
open SourceFiveModule
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

theorem alternatingBlock
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (g : D.L) (hK : NormalBranch.K D g.val≤D.L)
    (hp : IsPPerfect 2 (NormalBranch.K D g.val)) (a : alternatingGroup (Fin 6))
    (hi : ((NormalBranch.K D g.val).subgroupOf D.L).map (localMap d)=
      FivePair.five.map (MulAut.conj a.val).toMonoidHom)
    (hS : (NormalBranch.K D g.val).pCoreIn 2=D.V) :
    ChapterC.IsAlternatingBlock (NormalBranch.K D g.val) 5 := by
  let J := NormalBranch.K D g.val
  let eS : pCore 2 J≃*D.V :=
    ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).trans (MulEquiv.subgroupCongr hS)
  let eV := eS.trans (moduleEquiv d a)
  apply ChapterC.isAlternatingBlock_five_of_core_coordinates hp (quotientEquiv d hK a hi e) eV
  intro k v
  have he : eS ((pCore 2 J).normalizerMonoidHom
      ⟨k,(pCore 2 J).normalizer_eq_top ▸ mem_top k⟩ v) =
      D.V.normalizerMonoidHom ⟨k.val,d.normalizes_V (mem_sup_left (hK k.property))⟩ (eS v) := by
    apply Subtype.ext
    rfl
  change (moduleEquiv d a (eS _)).toAdd=_
  rw [he]
  exact moduleEquiv_equivariant d hK a hi e k (eS v)

include d in
theorem exists_original_block (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus=⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
    (hU : ¬IsMulCommutative D.UH) :
    ∃g:D.L,g.val∉D.Gz ∧ g.val∈NormalBranch.K D g.val ∧
      NormalBranch.K D g.val≤D.L ∧ D.L₁≤NormalBranch.K D g.val ∧
      blockResidual D g.val=NormalBranch.K D g.val ∧
      ChapterC.IsAlternatingBlock (NormalBranch.K D g.val) 5 ∧
      (NormalBranch.K D g.val).pCoreIn 2=D.V ∧ D.L₁.pCoreIn 2=D.UH ∧
      Nonempty (D.UH≃*QuaternionCentralProduct.Model) := by
  obtain ⟨a,g,hgn,hg,hK,hL,hp,hr,_,hi,hS⟩ :=
    SourceCoreCollapse.exists_original_collapsed_pair d h e hseed hn hU
  obtain ⟨hc,_,_,he,_⟩ := SourceQuaternion.source13_5_15_five d h e hseed hn hU
  exact ⟨g,hgn,hg,hK,hL,hr,alternatingBlock d e g hK hp a hi hS,hS,hc,he⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceFiveBlock
end
