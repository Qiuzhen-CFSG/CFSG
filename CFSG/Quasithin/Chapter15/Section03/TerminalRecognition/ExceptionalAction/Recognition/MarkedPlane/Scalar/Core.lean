module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.Transport
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion


/-!
# The external residual's two-core on the normal-closure module

The conjugator defining `Y_F` normalizes `V`. Thus the source bound on
`O₂(Y_F)` implies that `O₂(Y_E)` centralizes `V`. Since `G₀` normalizes
`Y_E`, it normalizes this characteristic two-core and its centralizer.
The centralizer consequently contains the whole `G₀`-normal closure of
`V`. In hexacode coordinates every element of the two-core acts trivially
by actual ambient conjugation, including elements outside `G₀`.

These results supply the kernel bound for constructing the external
`Y_E/O₂(Y_E)` action; they do not yet identify that action with scalars.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, the
construction preceding 15.3.68 on printed p.1154 and the local core bound
in the final proof of 15.3.1 on printed p.1155.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
variable {G : Type*} [Group G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}

namespace SourceConfiguration
variable (cfg : SourceConfiguration G₀ M V d)

/-- Relative normalization of the residual also preserves its two-core. -/
theorem first_residual_core_normalized :
    G₀ ≤ normalizer (cfg.YE.pCoreIn 2 : Set G) :=
  cfg.first_residual_normalized.trans
    (normalizer_le_normalizer_characteristic_image cfg.YE (pCore 2 cfg.YE))

/-- Conjugate the known bound for `O₂(Y_F)` back to `O₂(Y_E)`. -/
theorem first_residual_core_centralizes_vector :
    cfg.YE.pCoreIn 2 ≤ centralizer (V : Set G) := by
  let f : G ≃* G := MulAut.conj cfg.s⁻¹
  have hK : (cfg.YE.pCoreIn 2).map f.toMonoidHom = cfg.YF.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 cfg.YE f.toMonoidHom f.injective]
    rw [cfg.conjugate_residual_eq]
  have hs : cfg.s⁻¹ ∈ normalizer (V : Set G) :=
    d.normalizes (M.inv_mem (cfg.sylow_le cfg.conjugator_mem.1))
  have hF : cfg.YF.pCoreIn 2 ≤ centralizer (V : Set G) := by
    rw [← cfg.centralizer_eq]
    exact le_sup_right.trans cfg.local_core_bound
  intro y hy v hv
  apply f.injective
  have hyF : f y ∈ cfg.YF.pCoreIn 2 := hK ▸ mem_map_of_mem f.toMonoidHom hy
  have hvF : f v ∈ V := (mem_normalizer_iff.mp hs v).mp hv
  simpa only [map_mul] using hF hyF (f v) hvF
end SourceConfiguration

/-- The normal closure of the source vector group, viewed in the ambient group. -/
abbrev ambientClosure (G₀ V : Subgroup G) : Subgroup G :=
  (moduleClosure (V.subgroupOf G₀)).map G₀.subtype

/-- The two-core fixes every conjugate generating the actual module. -/
theorem first_residual_core_centralizes_closure (cfg : SourceConfiguration G₀ M V d) :
    cfg.YE.pCoreIn 2 ≤ centralizer (ambientClosure G₀ V : Set G) := by
  have hN : G₀ ≤ normalizer (centralizer (cfg.YE.pCoreIn 2 : Set G) : Set G) :=
    cfg.first_residual_core_normalized.trans
      (normalizer_le_normalizer_centralizer (cfg.YE.pCoreIn 2))
  let _ : ((centralizer (cfg.YE.pCoreIn 2 : Set G)).subgroupOf G₀).Normal :=
    normal_subgroupOf_of_le_normalizer hN
  have hV : V ≤ centralizer (cfg.YE.pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp cfg.first_residual_core_centralizes_vector
  have hW : moduleClosure (V.subgroupOf G₀) ≤
      (centralizer (cfg.YE.pCoreIn 2 : Set G)).subgroupOf G₀ :=
    normalClosure_le_normal (fun _ hv => hV hv)
  apply le_centralizer_iff.mpr
  rintro w ⟨v, hv, rfl⟩
  exact hW hv

variable [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]
  {hC : IsPGroup 2 (centralizer (V.subgroupOf G₀ : Set G₀))}
  {hcore : pCore 2 G₀ ≤ centralizer (V.subgroupOf G₀ : Set G₀)}
  (c : HexacodeCoordinates (V.subgroupOf G₀) hC hcore)

/-- Every coordinate vector belongs to the same ambient normal closure. -/
theorem ambientVector_mem_closure (w : Atlas.Codes.hexacode) :
    ambientVector c w ∈ ambientClosure G₀ V :=
  mem_map_of_mem G₀.subtype (c.vectors.symm w).toMul.property

/-- The two-core acts trivially on the entire module by ambient conjugation. -/
theorem first_residual_core_fixes_coordinates (cfg : SourceConfiguration G₀ M V d)
    {y : G} (hy : y ∈ cfg.YE.pCoreIn 2) (w : Atlas.Codes.hexacode) :
    y * ambientVector c w * y⁻¹ = ambientVector c w := by
  exact mul_inv_eq_iff_eq_mul.mpr
    ((first_residual_core_centralizes_closure cfg hy) _ (ambientVector_mem_closure c w)).symm

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
