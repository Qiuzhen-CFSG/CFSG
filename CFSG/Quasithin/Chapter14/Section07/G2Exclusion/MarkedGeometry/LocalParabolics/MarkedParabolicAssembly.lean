module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.FamilyAction
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The full-group marked parabolic application

The natural/Weyl identification intertwines the actual starred action and
preserves the specified line and pencil span. Its injectivity identifies the
line stabilizer, and its equivariance identifies the pointwise centralizer of
the pencil span. The index-three lift then gives M₁=N_H(V)=L₁T and its literal
starred image. The earlier product formula QQ_H=O₂(L₁T) transfers the radical.
Finally the root-fusion argument in `ThreeOffenderOrbit` proves that the three
H*-conjugates of this very centralizer in R₁* form a single M₁-orbit.

The group equivalence here is with the full G₂(2), as required by 14.7.57(3).
The generic lift for the derived-group case remains in `ParabolicLift`.
Precise earlier B.4.6 premises, with Chapter 14's M₁* corresponding to B.4.6's
P₂, are explicit inputs owned by `qt-b-04-g2`. The marked line/span and actual
action identification are the 14.7.54–55 inputs retained by the parent
`qt-14-07-g2-marked-geometry`. No clause of 14.7.57 is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.57,
printed pp.1066–1067, and the proof of B.4.6(13), printed p.90.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.MarkedParabolicAssembly

open Subgroup
open scoped Pointwise
open Atlas.G2
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit


variable {H Q : Type*} [Group H] [Group Q]

/-- The actual image of a model subspace in the source quotient. -/
def transportedSubspace (m : BinaryG2Module) (E : Multiplicative m.Space ≃* Q)
    (W : Submodule (ZMod 2) m.Space) : Subgroup Q :=
  W.toAddSubgroup.toSubgroup.map E.toMonoidHom

private theorem transportedSubspace_injective (m : BinaryG2Module)
    (E : Multiplicative m.Space ≃* Q) : Function.Injective (transportedSubspace m E) := by
  intro W W' h
  exact Submodule.toAddSubgroup_injective
    (AddSubgroup.toSubgroup.injective (Subgroup.map_injective E.injective h))

/-- The line correspondence intertwines the literal source automorphisms. -/
theorem transported_line_action (m : BinaryG2Module)
    (e : H ≃* Model (ZMod 2)) (E : Multiplicative m.Space ≃* Q)
    (τ : H →* MulAut Q)
    (hE : ∀ g : H, ∀ w : m.Space, τ g (E (.ofAdd w)) =
      E (.ofAdd (m.action (e g) w)))
    (L : ZeroProductLine (ZMod 2)) (g : H) :
    (transportedSubspace m E (m.singularMap.line L)).map (τ g).toMonoidHom =
      transportedSubspace m E (m.singularMap.line (e g • L)) := by
  rw [m.singularMap.line_equivariant m.action m.equivariant]
  ext q
  constructor
  · rintro ⟨x,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨.ofAdd (m.action (e g) v.toAdd), ⟨v.toAdd,hv,rfl⟩, (hE g v.toAdd).symm⟩
  · rintro ⟨v,⟨w,hw,he⟩,rfl⟩
    refine ⟨E (.ofAdd w),⟨.ofAdd w,hw,rfl⟩,?_⟩
    change τ g (E (.ofAdd w)) = E v
    rw [hE]
    exact congrArg E (congrArg Multiplicative.ofAdd he)

/-- The subgroup stabilizer is the marked geometric line parabolic. -/
theorem transported_line_stabilizer (m : BinaryG2Module)
    (e : H ≃* Model (ZMod 2)) (E : Multiplicative m.Space ≃* Q)
    (τ : H →* MulAut Q)
    (hE : ∀ g : H, ∀ w : m.Space, τ g (E (.ofAdd w)) =
      E (.ofAdd (m.action (e g) w)))
    (L : ZeroProductLine (ZMod 2)) :
    (MulAction.stabilizer (MulAut Q)
      (transportedSubspace m E (m.singularMap.line L))).comap τ =
      (MulAction.stabilizer (Model (ZMod 2)) L).comap e.toMonoidHom := by
  ext g
  change τ g ∈ MulAction.stabilizer _ _ ↔ e g ∈ MulAction.stabilizer _ L
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  change (transportedSubspace m E (m.singularMap.line L)).map (τ g).toMonoidHom = _ ↔ _
  rw [transported_line_action m e E τ hE]
  exact (transportedSubspace_injective m E).eq_iff.trans m.singularMap.line_injective.eq_iff

/-- The pointwise centralizer of the source pencil span is the marked A*. -/
theorem transported_pointwise_centralizer (m : BinaryG2Module)
    (e : (H ⧸ pCore 2 H) ≃* Model (ZMod 2)) (E : Multiplicative m.Space ≃* Q)
    (τ : (H ⧸ pCore 2 H) →* MulAut Q)
    (hE : ∀ g, ∀ w : m.Space, τ g (E (.ofAdd w)) =
      E (.ofAdd (m.action (e g) w)))
    (p : SingularPoints (ZMod 2)) :
    (fixingSubgroup (MulAut Q)
      (transportedSubspace m E (m.pencilSpan p) : Set Q)).comap τ =
      markedOffender m e p := by
  ext g
  simp only [mem_comap, mem_fixingSubgroup_iff]
  change (∀ v ∈ transportedSubspace m E (m.pencilSpan p), τ g v = v) ↔
    g ∈ Representation.BinaryOffender.subspaceKernel
      (m.action.comp e.toMonoidHom) (m.pencilSpan p) ⊤
  constructor
  · intro hg
    refine ⟨mem_top _, ?_⟩
    intro w hw
    have he := hg (E (.ofAdd w)) ⟨.ofAdd w,hw,rfl⟩
    rw [hE] at he
    exact E.injective he
  · intro hg v hv
    obtain ⟨w,hw,rfl⟩ := hv
    change τ g (E (.ofAdd w.toAdd)) = E (.ofAdd w.toAdd)
    rw [hE]
    exact congrArg (fun x => E (.ofAdd x)) (hg.2 w.toAdd hw)

/-- The marked line stabilizer pulled back along the actual full-group equivalence. -/
abbrev markedLineParabolic (e : (H ⧸ pCore 2 H) ≃* Model (ZMod 2))
    (L : ZeroProductLine (ZMod 2)) : Subgroup (H ⧸ pCore 2 H) :=
  (MulAction.stabilizer (Model (ZMod 2)) L).comap e.toMonoidHom

variable {G : Type*} [Group G] [Finite G]

/-- Assemble all three clauses of 14.7.57 in the full-group case from the
earlier local product, marked module, and B.4.6 premises. The centralizer
and every conjugating element are expressed in the original starred action. -/
theorem source_full_marked_parabolic_deductions
    (H U Z V : Subgroup G) [(Z.subgroupOf U).Normal]
    (hHU : H ≤ normalizer U) (hVU : V ≤ U) (hZV : Z ≤ V)
    (m : BinaryG2Module) (e : (H ⧸ pCore 2 H) ≃* Model (ZMod 2))
    (E : Multiplicative m.Space ≃* (U ⧸ Z.subgroupOf U))
    (τ : (H ⧸ pCore 2 H) →* MulAut (U ⧸ Z.subgroupOf U))
    (hact : ∀ h : H, ∀ u : U,
      τ (QuotientGroup.mk' (pCore 2 H) h) (QuotientGroup.mk' (Z.subgroupOf U) u) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(h : G) * (u : G) * (h : G)⁻¹,
            (mem_normalizer_iff.mp (hHU h.property) u).mp u.property⟩)
    (hE : ∀ g, ∀ w : m.Space, τ g (E (.ofAdd w)) =
      E (.ofAdd (m.action (e g) w)))
    (p : SingularPoints (ZMod 2)) (L : ZeroProductLine (ZMod 2))
    (hmark : (V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) =
      transportedSubspace m E (m.singularMap.line L))
    (U₃ : Subgroup (U ⧸ Z.subgroupOf U))
    (hU₃ : U₃ = transportedSubspace m E (m.pencilSpan p))
    (Q L₁ T Y : Subgroup H) (Ppoint : Subgroup (H ⧸ pCore 2 H))
    (hpoint : (Y ⊔ T).map (QuotientGroup.mk' (pCore 2 H)) = Ppoint)
    (hker : pCore 2 H ≤ T)
    (hLP : L₁.map (QuotientGroup.mk' (pCore 2 H)) ≤ markedLineParabolic e L)
    (hTP : T.map (QuotientGroup.mk' (pCore 2 H)) ≤ markedLineParabolic e L)
    (hindex : (T.map (QuotientGroup.mk' (pCore 2 H))).relIndex
      (markedLineParabolic e L) = 3)
    (hne : ¬ L₁.map (QuotientGroup.mk' (pCore 2 H)) ≤
      T.map (QuotientGroup.mk' (pCore 2 H)))
    (hminimal : markedLineParabolic e L ∈
      nonNormalUniqueMaximalOvergroups (T.map (QuotientGroup.mk' (pCore 2 H))))
    (hdistinct : markedLineParabolic e L ≠ Ppoint)
    (hproduct : Q ⊔ pCore 2 H = (L₁ ⊔ T).pCoreIn 2)
    (d : B46Premises (m.action.comp e.toMonoidHom) (m.pencilSpan p)
      (markedLineParabolic e L)) :
    let π := QuotientGroup.mk' (pCore 2 H)
    let M₁ := (normalizer V).subgroupOf H
    let R₁ := M₁.pCoreIn 2
    let A := (fixingSubgroup (MulAut (U ⧸ Z.subgroupOf U))
      (U₃ : Set (U ⧸ Z.subgroupOf U))).comap τ
    M₁ = L₁ ⊔ T ∧
    M₁.map π = markedLineParabolic e L ∧
    M₁.map π ∈ nonNormalUniqueMaximalOvergroups (T.map π) ∧
    M₁.map π ≠ (Y ⊔ T).map π ∧
    Q ⊔ pCore 2 H = R₁ ∧
    Q.map π = R₁.map π ∧
    R₁.map π = (M₁.map π).pCoreIn 2 ∧
    conjugatesIn A (R₁.map π) = conjugateLineFamily A (M₁.map π) ∧
    (conjugatesIn A (R₁.map π)).ncard = 3 ∧
    ∀ B ∈ conjugatesIn A (R₁.map π), ∃ x : M₁, conjugate A (π x) = B := by
  let π := QuotientGroup.mk' (pCore 2 H)
  have hP : markedLineParabolic e L =
      (MulAction.stabilizer (MulAut (U ⧸ Z.subgroupOf U))
        ((V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)))).comap τ := by
    rw [hmark]
    exact (transported_line_stabilizer m e E τ hE L).symm
  have hk : π.ker ≤ T := by
    rw [QuotientGroup.ker_mk']
    exact hker
  have hn := source_marked_normalizer H U Z V hHU hVU hZV π
    (QuotientGroup.mk'_surjective _) τ hact L₁ T Y (markedLineParabolic e L)
    Ppoint hP hpoint hk hLP hTP hindex hne hminimal hdistinct
  have hM : ((normalizer V).subgroupOf H).map π = markedLineParabolic e L := by
    rw [relative_line_normalizer H U Z V hHU hVU hZV π τ hact, ← hP]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hrad := source_starred_radical Q L₁ T hproduct
  have ho := source_three_offender_conjugates m e p L
    ((normalizer V).subgroupOf H) hM d
  have hA : (fixingSubgroup (MulAut (U ⧸ Z.subgroupOf U))
      (U₃ : Set (U ⧸ Z.subgroupOf U))).comap τ = markedOffender m e p := by
    rw [hU₃]
    exact transported_pointwise_centralizer m e E τ hE p
  dsimp only
  rw [hA]
  refine ⟨hn.1,hM,?_,?_,?_,?_,?_,ho.1,ho.2.1,ho.2.2⟩
  · rw [hn.1]
    exact hn.2.1
  · rw [hn.1]
    exact hn.2.2
  · rw [hn.1]
    exact hproduct
  · rw [hn.1]
    exact hrad.1
  · rw [hn.1]
    exact hrad.1.symm.trans hrad.2

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.MarkedParabolicAssembly
