module

public import CFSG.Quasithin.ChapterA.Section04.Defs
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Subnormal
public import Theory.GroupTheory.ReducedNormal.MovedWitness
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# Chief-factor reduction and a minimal reduced witness

A.4.8(2) is proved in the actual quotient XS/C_XS(V(X)), with X* the
image of X. The source chief-factor conditions concern the chief intervals
above O₂(X). Pullback of chief intervals and coprime action give centrality
of O₂(X*); absence of all two-chief intervals gives its triviality.

For the difficult direction of A.4.11, a normal elementary abelian U moved
by a subnormal two-perfect X contains a reduced normal subgroup V still
moved by X, provided O₂(X) centralizes U and the noncentral chief-factor
condition holds. The reusable proof chooses V minimal and applies Thompson
A × B to the core of its actual conjugation image. The final theorem uses
U = Ω₁(Z(O₂(M))) and discharges normality, elementary structure and the
original core's centralizing action. A.4.9 supplies its remaining movedness
hypothesis in the full A.4.11 assembly and in the source XT application.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.4.8(2), A.4.11(1) implies (2), printed pp.59–61 (PDF pp.70–72).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section04
variable {G : Type*} [Group G]

/-- The intrinsic module lies in X, so its restriction to XS loses no elements. -/
theorem intrinsicModule_le_self (X : Subgroup G) : intrinsicSignalizerModule X ≤ X :=
  signalizerModule_le_left X _ ((map_subtype_le _).trans X.le_normalizer)

/-- The quotient uses exactly the relative centralizer C_XS(V(X)). -/
theorem intrinsicModule_join_centralizer_eq (X S : Subgroup G) :
    centralizer ((intrinsicSignalizerModule X).subgroupOf (X ⊔ S) : Set ↥(X ⊔ S)) =
      (centralizer (intrinsicSignalizerModule X : Set G)).subgroupOf (X ⊔ S) := by
  ext x
  constructor
  · intro hx v hv
    exact congrArg Subtype.val (hx
      (⟨v, mem_sup_left ((intrinsicModule_le_self X) hv)⟩ : ↥(X ⊔ S)) hv)
  · intro hx v hv
    exact Subtype.ext (hx v.val hv)

/-- The source module V(X), viewed inside XS, is normal in XS. -/
theorem intrinsicModule_normal_in_join (X M S : Subgroup G)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hX : IsPPerfect 2 X) (hS : IsTwoSignalizer X M S) :
    ((intrinsicSignalizerModule X).subgroupOf (X ⊔ S)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact sup_le (X.le_normalizer.trans (normalizer_le_normalizer_intrinsicModule X))
    ((signalizer_le_normalizer X M S hXM hsub hX hS).trans
      (normalizer_le_normalizer_intrinsicModule X))

/-- A.4.8(2), in the literal quotient XS/C_XS(V(X)). The range below is X*.
Both source clauses hold; the extra R and containment hypotheses of A.4.8
are unnecessary for this part. -/
theorem source_lemma_A_4_8_2 [Finite G] (X M S : Subgroup G)
    (hXM : X ≤ M) (hsub : (X.subgroupOf M).IsSubnormal)
    (hX : IsPPerfect 2 X) (hS : IsTwoSignalizer X M S) :
    let V := (intrinsicSignalizerModule X).subgroupOf (X ⊔ S)
    let : V.Normal := intrinsicModule_normal_in_join X M S hXM hsub hX hS
    let q := QuotientGroup.mk' (centralizer (V : Set ↥(X ⊔ S)))
    let f := q.comp (inclusion (show X ≤ X ⊔ S from le_sup_left))
    (HasCentralPChiefFactorsAbove 2 (pCore 2 X) → pCore 2 f.range ≤ center f.range) ∧
    (HasNoPChiefFactorsAbove 2 (pCore 2 X) → pCore 2 f.range = ⊥) := by
  dsimp only
  let V := (intrinsicSignalizerModule X).subgroupOf (X ⊔ S)
  let : V.Normal := intrinsicModule_normal_in_join X M S hXM hsub hX hS
  let q := QuotientGroup.mk' (centralizer (V : Set ↥(X ⊔ S)))
  let f := q.comp (inclusion (show X ≤ X ⊔ S from le_sup_left))
  have hkill : pCore 2 X ≤ f.rangeRestrict.ker := by
    intro x hx
    apply Subtype.ext
    change q (inclusion (show X ≤ X ⊔ S from le_sup_left) x) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    intro v hv
    apply Subtype.ext
    exact intrinsicCore_le_centralizer_intrinsicModule X
      (mem_map_of_mem X.subtype hx) v.val hv
  exact ⟨fun hc => pCore_image_le_center_of_chiefFactors hX hc
      f.rangeRestrict f.rangeRestrict_surjective hkill,
    fun hc => pCore_image_eq_bot_of_chiefFactors hc
      f.rangeRestrict f.rangeRestrict_surjective hkill⟩

/-- The difficult direction of A.4.11 from its explicit initial module U.
No reducedness, fixed-point conclusion or reduced witness is assumed. -/
theorem exists_reduced_witness_of_moved [Finite G] (X U : Subgroup G)
    (hsub : X.IsSubnormal) (hX : IsPPerfect 2 X)
    (hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 X))
    [U.Normal] [IsElementaryAbelian 2 U]
    (hmoved : ⁅U, X⁆ ≠ ⊥)
    (hkill : (pCore 2 X).map X.subtype ≤ centralizer (U : Set G)) :
    ∃ V : Subgroup G, V ≤ U ∧ IsPReduced 2 V ∧ ⁅V, X⁆ ≠ ⊥ :=
  exists_isPReduced_le_of_moved X U hsub hX hchief hkill hmoved

/-- The source choice U = Ω₁(Z(O₂(M))) gives both a reduced witness inside U
and nontrivial action on the maximal reduced subgroup R₂(M). This is the
minimal-witness input used for XT in the Xi-minus source argument. -/
theorem reduced_witness_of_omegaCenter_moved [Finite G] (X : Subgroup G)
    (hsub : X.IsSubnormal) (hX : IsPPerfect 2 X)
    (hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 X))
    (hmoved : ⁅omegaOneCenterAmbient (pCore 2 G), X⁆ ≠ ⊥) :
    (∃ V : Subgroup G, V ≤ omegaOneCenterAmbient (pCore 2 G) ∧
      IsPReduced 2 V ∧ ⁅V, X⁆ ≠ ⊥) ∧ ⁅reducedTwoSubgroup G, X⁆ ≠ ⊥ := by
  let U := omegaOneCenterAmbient (pCore 2 G)
  let : IsElementaryAbelian 2 U := omegaOneCenterAmbient_elementaryAbelian _
  let : U.Normal := normalizer_eq_top_iff.mp (top_unique
    ((le_normalizer_of_normal : (⊤ : Subgroup G) ≤ normalizer (pCore 2 G : Set G)).trans
      (normalizer_le_normalizer_omegaCenter (pCore 2 G))))
  have hcore : (pCore 2 X).map X.subtype ≤ pCore 2 G := by
    have hh := pCoreAmbient_mono_of_isSubnormalIn X ⊤ 2 le_top hsub.subgroupOf
    change (pCore 2 X).map X.subtype ≤
      (pCore 2 (⊤ : Subgroup G)).map (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom at hh
    rwa [pCore_map_iso] at hh
  have hkill : (pCore 2 X).map X.subtype ≤ centralizer (U : Set G) := by
    intro x hx u hu
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hu).2.2 x (hcore hx) |>.symm
  exact ⟨exists_reduced_witness_of_moved X U hsub hX hchief hmoved hkill,
    reducedPSubgroup_commutator_ne_bot_of_moved X U hsub hX hchief hkill hmoved⟩
end CFSG.Quasithin.ChapterA.Section04
