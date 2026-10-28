module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.Transport

/-!
# Hamming weight and the actual residual product

The vector map retains the original subgroup `V`. The three factors in
`Y = Y_E Y_F O₂(Y)` each preserve Hamming weight on it: the first by the
explicit scalar-action premise, the second by its actual inclusion in `G₀`,
and the last by centralization. No non-scalar image of `Y_F` is assumed.

Source: Aschbacher–Smith, printed pp.1121–1122 and 1154–1155.
-/

@[expose] public section

open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
variable {G : Type*} [Group G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}
  [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]
  {hC : IsPGroup 2 (centralizer (V.subgroupOf G₀ : Set G₀))}
  {hcore : pCore 2 G₀ ≤ centralizer (V.subgroupOf G₀ : Set G₀)}
  (c : HexacodeCoordinates (V.subgroupOf G₀) hC hcore)
  (cfg : SourceConfiguration G₀ M V d)

/-- A vector of the original source subgroup in the supplied code coordinates. -/
noncomputable def sourceVector (v : V) : Atlas.Codes.hexacode :=
  c.vectors (Additive.ofMul ⟨⟨v.val, cfg.vector_le v.property⟩, le_normalClosure v.property⟩)

theorem ambientVector_sourceVector (v : V) : ambientVector c (sourceVector c cfg v) = v := by
  simp [sourceVector, ambientVector]

theorem sourceVector_injective : Function.Injective (sourceVector c cfg) := by
  intro u v h
  apply Subtype.ext
  simpa only [ambientVector_sourceVector] using congrArg (ambientVector c) h

theorem sourceVector_mem (v : V) : sourceVector c cfg v ∈ vectorImage c V := by
  rw [mem_vectorImage, ambientVector_sourceVector]
  exact v.property

theorem sourceVector_surjective : ∀ w ∈ vectorImage c V, ∃ v : V, sourceVector c cfg v = w := by
  intro w hw
  refine ⟨⟨ambientVector c w, (mem_vectorImage c V w).mp hw⟩, ?_⟩
  apply ambientVector_injective c
  exact ambientVector_sourceVector c cfg _

theorem sourceVector_one : sourceVector c cfg 1 = 0 := by
  exact c.vectors.map_zero

theorem sourceVector_weight_conjugate (hYE : ScalarActionOn c cfg.YE)
    (y : G) (hy : y ∈ cfg.Y) (v : V) :
    hammingNorm (sourceVector c cfg
      (V.normalizerMonoidHom ⟨y, d.normalizes (cfg.residual_le hy)⟩ v)).val =
      hammingNorm (sourceVector c cfg v).val := by
  have hp : y ∈ (cfg.YE : Set G) * (cfg.YF : Set G) * (cfg.Y.pCoreIn 2 : Set G) := by
    rw [← cfg.residual_product]
    exact hy
  obtain ⟨ef, ⟨e, he, f, hf, rfl⟩, q, hq, rfl⟩ := hp
  obtain ⟨k, hk⟩ := hYE e he
  let f₀ : G₀ := ⟨f, cfg.second_residual_le hf⟩
  have hqv : q * (v : G) = (v : G) * q := by
    have hqR := cfg.residual_core_le hq
    rw [cfg.centralizer_eq] at hqR
    exact (hqR v v.property).symm
  have ha : sourceVector c cfg
      (V.normalizerMonoidHom ⟨e * f * q, d.normalizes (cfg.residual_le hy)⟩ v) =
      Representation.Hexacode.action (Atlas.Codes.hexZ ^ k.val)
        (Representation.Hexacode.action (actorHom c f₀) (sourceVector c cfg v)) := by
    apply ambientVector_injective c
    rw [ambientVector_sourceVector, ← hk, ambientVector_action, ambientVector_sourceVector]
    change e * f * q * (v : G) * (e * f * q)⁻¹ = e * (f * (v : G) * f⁻¹) * e⁻¹
    calc
      _ = e * f * (q * (v : G)) * q⁻¹ * f⁻¹ * e⁻¹ := by group
      _ = _ := by rw [hqv]; group
  rw [ha]
  exact (Atlas.Codes.Monomial.act_weight _ _).trans (Atlas.Codes.Monomial.act_weight _ _)
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
