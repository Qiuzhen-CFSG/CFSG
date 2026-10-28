module
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.AmbientTransport

/-!
# Marked parabolics on the assembled quotient pencil

The marked line supplied by 14.7.55 determines its stabilizer through the
actual starred action. The index-three lift and the earlier QQ_H identity
give 14.7.57(1),(2) for either actor. When the actor is the full G₂(2),
the B.4.6 root-fusion deduction gives the three A*-conjugates in its
line radical. A* is the centralizer of the literal quotient pencil span.

Source: Aschbacher–Smith, 14.7.57, printed pp.1066–1067; B.4.6(13), p.90.
The explicit earlier B.4.6 premises are supplied by qt-b-04-g2.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.ParabolicAssembly
open Subgroup
open scoped Pointwise
open Atlas.G2 Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open MarkedPencil LocalParabolics LocalParabolics.ThreeOffenderOrbit
open LocalParabolics.MarkedParabolicAssembly AmbientTransport

private theorem line_action {D Q : Type*} [Group D] [Group Q]
    (m : BinaryG2Module) (i : D →* Model (ZMod 2))
    (E : Multiplicative m.Space ≃* Q) (τ : D →* MulAut Q)
    (hE : ∀ g w, τ g (E (.ofAdd w)) = E (.ofAdd (m.action (i g) w)))
    (L : ZeroProductLine (ZMod 2)) (g : D) :
    ((transportGeometry m.singularMap.geometry E).line L).map (τ g).toMonoidHom =
      (transportGeometry m.singularMap.geometry E).line (i g • L) := by
  change (transportedSubspace m E (m.singularMap.line L)).map _ =
    transportedSubspace m E (m.singularMap.line (i g • L))
  rw [m.singularMap.line_equivariant m.action m.equivariant]
  ext q
  constructor
  · rintro ⟨x,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨.ofAdd (m.action (i g) v.toAdd),⟨v.toAdd,hv,rfl⟩,(hE g v.toAdd).symm⟩
  · rintro ⟨v,⟨w,hw,he⟩,rfl⟩
    refine ⟨E (.ofAdd w),⟨.ofAdd w,hw,rfl⟩,?_⟩
    change τ g (E (.ofAdd w)) = E v
    rw [hE]
    exact congrArg E (congrArg Multiplicative.ofAdd he)

private theorem line_stabilizer {D Q : Type*} [Group D] [Group Q]
    (m : BinaryG2Module) (i : D →* Model (ZMod 2))
    (E : Multiplicative m.Space ≃* Q) (τ : D →* MulAut Q)
    (hE : ∀ g w, τ g (E (.ofAdd w)) = E (.ofAdd (m.action (i g) w)))
    (L : ZeroProductLine (ZMod 2)) :
    (MulAction.stabilizer (MulAut Q) ((transportGeometry m.singularMap.geometry E).line L)).comap τ =
      (MulAction.stabilizer (Model (ZMod 2)) L).comap i := by
  ext g
  change τ g ∈ MulAction.stabilizer _ _ ↔ i g ∈ MulAction.stabilizer _ _
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  change ((transportGeometry m.singularMap.geometry E).line L).map (τ g).toMonoidHom = _ ↔ _
  rw [line_action m i E τ hE]
  exact (transportGeometry m.singularMap.geometry E).line.injective.eq_iff

private theorem full_span_orbit {H Q : Type*} [Group H] [Finite H] [Group Q]
    (m : BinaryG2Module) (e : (H ⧸ pCore 2 H) ≃* Model (ZMod 2))
    (E : Multiplicative m.Space ≃* Q) (τ : (H ⧸ pCore 2 H) →* MulAut Q)
    (hE : ∀ g w, τ g (E (.ofAdd w)) = E (.ofAdd (m.action (e g) w)))
    (p : SingularPoints (ZMod 2)) (L : ZeroProductLine (ZMod 2))
    (M : Subgroup H)
    (hM : M.map (QuotientGroup.mk' (pCore 2 H)) = markedLineParabolic e L)
    (d : B46Premises (m.action.comp e.toMonoidHom) (m.pencilSpan p) (markedLineParabolic e L)) :
    let π := QuotientGroup.mk' (pCore 2 H)
    let A := (fixingSubgroup (MulAut Q)
      (quotientPencilSpan (transportGeometry m.singularMap.geometry E)
        ((transportGeometry m.singularMap.geometry E).point p) : Set Q)).comap τ
    conjugatesIn A (M.pCoreIn 2 |>.map π) = conjugateLineFamily A (M.map π) ∧
    (conjugatesIn A (M.pCoreIn 2 |>.map π)).ncard = 3 ∧
    ∀ B ∈ conjugatesIn A (M.pCoreIn 2 |>.map π), ∃ x : M, conjugate A (π x) = B := by
  have hA : (fixingSubgroup (MulAut Q)
      (quotientPencilSpan (transportGeometry m.singularMap.geometry E)
        ((transportGeometry m.singularMap.geometry E).point p) : Set Q)).comap τ =
      markedOffender m e p := by
    rw [quotientPencilSpan_eq]
    exact transported_pointwise_centralizer m e E τ hE p
  dsimp only
  rw [hA]
  exact source_three_offender_conjugates m e p L M hM d

variable {G : Type*} [Group G] [Finite G]

/-- All clauses of 14.7.57 for the marked line constructed in 14.7.55.
The final orbit assertion applies precisely when the starred actor is
identified with the full group. No marked-line or span identity is assumed;
they are obtained from the preceding assembled pencil output. -/
theorem source_marked_parabolics
    (H U Z V V₂ Y T : Subgroup G) [(Z.subgroupOf U).Normal]
    (hHU : H ≤ normalizer U) (hVU : V ≤ U) (hZV : Z ≤ V)
    (m : BinaryG2Module) (E : Multiplicative m.Space ≃* (U ⧸ Z.subgroupOf U))
    (action : Y →* MulAut (U ⧸ Z.subgroupOf U)) (p : SingularPoints (ZMod 2))
    (a : AmbientPencilConclusions U Z V V₂ Y T m E action p)
    (i : (H ⧸ pCore 2 H) →* Model (ZMod 2))
    (τ : (H ⧸ pCore 2 H) →* MulAut (U ⧸ Z.subgroupOf U))
    (hact : ∀ h : H, ∀ u : U,
      τ (QuotientGroup.mk' (pCore 2 H) h) (QuotientGroup.mk' (Z.subgroupOf U) u) =
        QuotientGroup.mk' (Z.subgroupOf U)
          ⟨(h : G) * (u : G) * (h : G)⁻¹,
            (mem_normalizer_iff.mp (hHU h.property) u).mp u.property⟩)
    (hE : ∀ g w, τ g (E (.ofAdd w)) = E (.ofAdd (m.action (i g) w))) :
    ∃ line : ZeroProductLine (ZMod 2),
      (V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) =
        (transportGeometry m.singularMap.geometry E).line line ∧
      let π := QuotientGroup.mk' (pCore 2 H)
      let P := (MulAction.stabilizer (Model (ZMod 2)) line).comap i
      let T₀ := T.subgroupOf H
      let Y₀ := Y.subgroupOf H
      ∀ (Q L₁ : Subgroup H) (Ppoint : Subgroup (H ⧸ pCore 2 H)),
      (Y₀ ⊔ T₀).map π = Ppoint → pCore 2 H ≤ T₀ →
      L₁.map π ≤ P → T₀.map π ≤ P → (T₀.map π).relIndex P = 3 →
      ¬ L₁.map π ≤ T₀.map π →
      P ∈ nonNormalUniqueMaximalOvergroups (T₀.map π) → P ≠ Ppoint →
      Q ⊔ pCore 2 H = (L₁ ⊔ T₀).pCoreIn 2 →
      let M₁ := (normalizer V).subgroupOf H
      let R₁ := M₁.pCoreIn 2
      let S := quotientPencilSpan (transportGeometry m.singularMap.geometry E)
        ((transportGeometry m.singularMap.geometry E).point p)
      let A := (fixingSubgroup (MulAut (U ⧸ Z.subgroupOf U))
        (S : Set (U ⧸ Z.subgroupOf U))).comap τ
      M₁ = L₁ ⊔ T₀ ∧ M₁.map π = P ∧
      M₁.map π ∈ nonNormalUniqueMaximalOvergroups (T₀.map π) ∧
      M₁.map π ≠ (Y₀ ⊔ T₀).map π ∧
      Q ⊔ pCore 2 H = R₁ ∧ Q.map π = R₁.map π ∧
      R₁.map π = (M₁.map π).pCoreIn 2 ∧
      ∀ e : (H ⧸ pCore 2 H) ≃* Model (ZMod 2), (∀ g, e g = i g) →
        B46Premises (m.action.comp e.toMonoidHom) (m.pencilSpan p) P →
        conjugatesIn A (R₁.map π) = conjugateLineFamily A (M₁.map π) ∧
        (conjugatesIn A (R₁.map π)).ncard = 3 ∧
        ∀ B ∈ conjugatesIn A (R₁.map π), ∃ x : M₁, conjugate A (π x) = B := by
  obtain ⟨line,hmark,_,_⟩ := a.line
  refine ⟨line,hmark,?_⟩
  dsimp only
  intro Q L₁ Ppoint hpoint hker hLP hTP hindex hne hminimal hdistinct hproduct
  let T₀ := T.subgroupOf H
  let Y₀ := Y.subgroupOf H
  let π := QuotientGroup.mk' (pCore 2 H)
  let P := (MulAction.stabilizer (Model (ZMod 2)) line).comap i
  have hP : P = (MulAction.stabilizer (MulAut (U ⧸ Z.subgroupOf U))
      ((V.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)))).comap τ := by
    rw [hmark]
    exact (line_stabilizer m i E τ hE line).symm
  have hn := source_marked_normalizer H U Z V hHU hVU hZV π
    (QuotientGroup.mk'_surjective _) τ hact L₁ T₀ Y₀ P Ppoint hP hpoint
    (by rwa [QuotientGroup.ker_mk']) hLP hTP hindex hne hminimal hdistinct
  have hM : ((normalizer V).subgroupOf H).map π = P := by
    rw [relative_line_normalizer H U Z V hHU hVU hZV π τ hact, ← hP]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hrad := source_starred_radical Q L₁ T₀ hproduct
  refine ⟨hn.1,hM,?_,?_,?_,?_,?_,?_⟩
  · rw [hn.1]; exact hn.2.1
  · rw [hn.1]; exact hn.2.2
  · rw [hn.1]; exact hproduct
  · rw [hn.1]; exact hrad.1
  · rw [hn.1]; exact hrad.1.symm.trans hrad.2
  · generalize hMdef : (normalizer V).subgroupOf H = M at hM ⊢
    intro e he d
    have hPe : P = markedLineParabolic e line := by
      have hi : i = e.toMonoidHom := MonoidHom.ext (fun g => (he g).symm)
      change (MulAction.stabilizer (Model (ZMod 2)) line).comap i =
        (MulAction.stabilizer (Model (ZMod 2)) line).comap e.toMonoidHom
      rw [hi]
    have hMe : M.map π = markedLineParabolic e line := hM.trans hPe
    have hEe : ∀ g w, τ g (E (.ofAdd w)) = E (.ofAdd (m.action (e g) w)) := by
      intro g w
      rw [he]
      exact hE g w
    have d' : B46Premises (m.action.comp e.toMonoidHom) (m.pencilSpan p)
        (markedLineParabolic e line) := by
      rwa [← hPe]
    exact full_span_orbit (H := H) (Q := U ⧸ Z.subgroupOf U) m e E τ hEe p line M hMe d'


end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.ParabolicAssembly
