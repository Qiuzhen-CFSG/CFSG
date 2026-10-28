module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.FixedGeometry
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.PointCores
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Reduction of B.5.1(6) to two concrete incident-pair calculations

The marked centralizer equivalence identifies intrinsic two-cores, their
ambient images, and their quotients. Excluding offenders from the concrete
incident radical excludes best offenders from the original SL centralizer's
core, since the latter maps into that radical.

The final theorem is explicitly conditional on the incident stabilizer's
extraspecial core and quotient calculation and on its radical offender
exclusion. It supplies the Sylow geometry and all transport, but does not
assert that these two remaining model calculations have been established.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(6),
printed pp.99 and 103; the offender cases are B.4.9(2iii–iv), printed p.92.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryNaturalDual BinaryNaturalDual.VectorStabilizers
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer

/-- The centralizer identification retains the specified SL-to-linear map. -/
noncomputable def centralizerEquiv {d : ℕ}
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)))
    (x : Space d) (f : Module.Dual (ZMod 2) (Space d))
    (hfix : fixedSpace (slAction d) T =
      (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f})) :
    subspaceKernel (slAction d) (fixedSpace (slAction d) T) ⊤ ≃*
      pairStabilizer x f :=
  ((slEquivLinear d).subgroupMap _).trans
    (MulEquiv.subgroupCongr (centralizer_map T x f hfix))

/-- Intrinsic two-cores correspond under the marked centralizer equivalence. -/
noncomputable def centralizerCoreEquiv {d : ℕ}
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)))
    (x : Space d) (f : Module.Dual (ZMod 2) (Space d))
    (hfix : fixedSpace (slAction d) T =
      (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f})) :
    pCore 2 (subspaceKernel (slAction d) (fixedSpace (slAction d) T) ⊤) ≃*
      pCore 2 (pairStabilizer x f) :=
  ((centralizerEquiv T x f hfix).subgroupMap _).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 (centralizerEquiv T x f hfix)))

/-- The ambient images of the two-cores use the same original group map. -/
theorem centralizerCore_map {d : ℕ}
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)))
    (x : Space d) (f : Module.Dual (ZMod 2) (Space d))
    (hfix : fixedSpace (slAction d) T =
      (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f})) :
    ((subspaceKernel (slAction d) (fixedSpace (slAction d) T) ⊤).pCoreIn 2).map
      (slEquivLinear d).toMonoidHom = (pairStabilizer x f).pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 _ _ (slEquivLinear d).injective,
    centralizer_map T x f hfix]

/-- Exclusion from the literal flag radical suffices for the source's ambient core. -/
theorem no_offenders_of_radical_exclusion {d : ℕ}
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin d) (ZMod 2)))
    (x : Space d) (f : Module.Dual (ZMod 2) (Space d))
    (hf : f ≠ 0) (hfx : f x = 0)
    (hfix : fixedSpace (slAction d) T =
      (Submodule.span (ZMod 2) {x}).prod (Submodule.span (ZMod 2) {f}))
    (hex : ∀ A : Subgroup (LinearGroup d), IsOffender naturalDualRepresentation A →
      ¬ A ≤ PointCores.incidentRadical x f) :
    ∀ A, IsBestOffender (slAction d) A →
      ¬ A ≤ (subspaceKernel (slAction d) (fixedSpace (slAction d) T) ⊤).pCoreIn 2 := by
  intro A hA hle
  have hAo : IsOffender naturalDualRepresentation
      (A.map (slEquivLinear d).toMonoidHom) :=
    (hA.isOffender (slAction d)).map_equivariant (slAction d)
    (naturalDualRepresentation (V := Space d)) (slEquivLinear d).toMonoidHom (slEquivLinear d).injective
    (LinearEquiv.refl (ZMod 2) (CoordinateSpace d)) (fun g v => action_apply d g v)
  apply hex _ hAo
  have hmap := Subgroup.map_mono (f := (slEquivLinear d).toMonoidHom) hle
  rw [centralizerCore_map T x f hfix] at hmap
  exact hmap.trans (PointCores.incident_core_le hf hfx)

/-- Conditional assembly of B.5.1(6) from the two independent incident-pair
calculations. The Sylow geometry and every change of actor are discharged here. -/
theorem sylowFixedCentralizer_of_incident_calculations {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hc : ∀ (x : Space d) (f : Module.Dual (ZMod 2) (Space d)),
      x ≠ 0 → f ≠ 0 → f x = 0 →
      IsExtraspecial 2 (pCore 2 (pairStabilizer x f)) ∧
      Nat.card (pCore 2 (pairStabilizer x f)) = 2 ^ (1 + 2 * (d - 2)) ∧
      Nonempty ((pairStabilizer x f ⧸ pCore 2 (pairStabilizer x f)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin (d - 2)) (ZMod 2)))
    (ho : ∀ (x : Space d) (f : Module.Dual (ZMod 2) (Space d)),
      x ≠ 0 → f ≠ 0 → f x = 0 →
      ∀ A : Subgroup (LinearGroup d), IsOffender naturalDualRepresentation A →
        ¬ A ≤ PointCores.incidentRadical x f)
    (T : Sylow 2 (Matrix.SpecialLinearGroup (Fin d) (ZMod 2))) :
    Nonempty (SylowFixedCentralizer (slAction d) ⊤ d T) := by
  obtain ⟨x, f, hx, hf, hfx, hfix⟩ := exists_fixed_pair (by omega : 2 ≤ d) T
  obtain ⟨he, hcard, ⟨eqv⟩⟩ := hc x f hx hf hfx
  let e := centralizerEquiv T x f hfix
  let ec := centralizerCoreEquiv T x f hfix
  refine ⟨{ extraspecial := he.of_mulEquiv ec.symm
            core_order := (Nat.card_congr ec.toEquiv).trans hcard
            quotientEquiv := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans eqv
            no_offenders := ?_ }⟩
  exact no_offenders_of_radical_exclusion T x f hf hfx hfix (ho x f hx hf hfx)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer
