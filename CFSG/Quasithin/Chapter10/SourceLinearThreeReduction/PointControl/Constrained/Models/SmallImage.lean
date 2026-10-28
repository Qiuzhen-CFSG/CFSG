module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Action
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Scalar
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.CComponent.RadicalKernel

/-!
# The smaller component in the literal constrained quotient

If the original two-core quotient is centerless, its quasisimplicity makes
it simple. The actual smaller action image is nonzero, so its normal kernel
is solvable and lies in the two-core. Quotienting that image by its own
two-core consequently recovers the original simple quotient, with the
literal action map retained. This supplies the kernel input to the torus
lifting argument; no centralization by O₂(L) on VI is assumed.
Source: Aschbacher--Smith, 10.2.9, printed p.751.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

/-- The smaller image preserves the actual centerless two-core quotient. -/
theorem Context.small_image_twoCore (c : Context D t v I) (a : ActionFacts c)
    (hz : center (L ⧸ pCore 2 L) = ⊥) :
    letI := c.reduced.normal
    let K := L.subgroupOf (pointJoin T v I)
    let q := actionMk (internalModule D v I)
    IsPGroup 2 (q.subgroupMap K).ker ∧
      Nonempty (((K.map q) ⧸ pCore 2 (K.map q)) ≃* (L ⧸ pCore 2 L)) := by
  let := D.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup

  let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ S
  let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I).subgroupOf H
  let := c.reduced.normal
  let K := L.subgroupOf H
  let f := (actionMk U).subgroupMap K
  have hLH : L ≤ H := c.escaping.strict.le.trans le_sup_left
  let k : K ≃* L := subgroupOfEquivOfLe hLH
  have hL : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self] using D.maximal.1.1.subgroupOf_of_le
      (show L ≤ L from le_rfl) (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
  have hK : (⊤ : Subgroup K).IsCComponent := by
    simpa only [map_top_of_surjective k.symm.toMonoidHom k.symm.surjective] using hL.map_equiv k.symm
  let := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup K) ≃* K).toMonoidHom) topEquiv.surjective
  let eK : (K ⧸ pCore 2 K) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ k (pCore_map_iso 2 k)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := eK.isSimpleGroup
  have hproper : f.ker ≠ ⊤ := by
    intro he
    have hz : K.map (actionMk U) = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      rintro _ ⟨a,ha,rfl⟩
      have hm : (⟨a,ha⟩ : K) ∈ f.ker := he ▸ mem_top _
      exact congrArg Subtype.val (show f ⟨a,ha⟩ = 1 from hm)
    exact a.small_nontrivial hz
  have hkle : f.ker ≤ pCore 2 K := by
    rw [← PerfectCoreTwoExtension.radical_eq_core]
    exact kernel_le_solvableRadical_of_top_isCComponent hK f hproper
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.of_injective
    (inclusion hkle) (inclusion_injective hkle)
  exact ⟨hk,⟨(f.pCoreQuotientEquiv ((actionMk U).subgroupMap_surjective K) hk).symm.trans eK⟩⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
