module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Inputs
public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup

/-!
# The finite group input for binary G₂ rank-three generation

The required calculation is on the actual split-octonion automorphism group:
an elementary subgroup of order eight and one derived conjugate of one of
its elements generate over the commutator subgroup. Keeping the conjugator
in the commutator lets the witness lift through every faithful representation,
without assuming that every abstract automorphism lifts to the representation.

Sylow conjugacy reduces coverage to the marked positive-root group of order
64. These are explicit finite-group premises; this module does not assert
their unconditional validity. The representation lift is in `Generation`.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.3,
manuscript pp.10--11, especially the outer-involution generation step on p.11.
The actual root and Sylow conventions are inherited from the licensed ATLAS
port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup

/-- Concrete group generation, with a conjugator in the actual derived group. -/
def ModelRankThreeGeneration : Prop :=
  ∀ E : Subgroup (Atlas.G2.Model (ZMod 2)), IsElementaryAbelian 2 E → Nat.card E = 8 →
    ∃ a ∈ E, ∃ g : Derived,
      commutator (Atlas.G2.Model (ZMod 2)) ≤ E ⊔ zpowers (g.val * a * g.val⁻¹)

/-- The same calculation restricted to the marked positive-root Sylow group. -/
def SylowRankThreeGeneration : Prop :=
  ∀ E : Subgroup (Atlas.G2.Model (ZMod 2)),
    E ≤ unipotent → IsElementaryAbelian 2 E → Nat.card E = 8 →
    ∃ a ∈ E, ∃ g : Derived,
      commutator (Atlas.G2.Model (ZMod 2)) ≤ E ⊔ zpowers (g.val * a * g.val⁻¹)

/-- Sylow conjugacy reduces the concrete generation problem to the order-64
positive-root group; the conjugator remains in the actual commutator subgroup. -/
theorem modelRankThreeGeneration_of_sylow (h : SylowRankThreeGeneration) :
    ModelRankThreeGeneration := by
  intro E hE hc
  let : IsElementaryAbelian 2 E := hE
  obtain ⟨P, hEP⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (Model (ZMod 2)) P (sylow (F := ZMod 2))
  let c := (MulAut.conj x).toMonoidHom
  let E' := E.map c
  have hE' : E' ≤ unipotent := by
    have hp : (P : Subgroup (Model (ZMod 2))).map c = unipotent :=
      congrArg (fun Q : Sylow 2 (Model (ZMod 2)) => (Q : Subgroup (Model (ZMod 2)))) hx
    exact (map_mono hEP).trans hp.le
  have he' : IsElementaryAbelian 2 E' := IsElementaryAbelian.map c
  have hc' : Nat.card E' = 8 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hc]
  obtain ⟨a', ha', g', hgen⟩ := h E' hE' he' hc'
  obtain ⟨a, ha, rfl⟩ := ha'
  let g : Derived := ⟨x⁻¹ * g'.val * x,
    by
      simpa using (inferInstance : (commutator (Model (ZMod 2))).Normal).conj_mem
        g'.val g'.property x⁻¹⟩
  refine ⟨a, ha, g, ?_⟩
  apply (map_le_map_iff_of_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective).mp
  have hD : (commutator (Model (ZMod 2))).map c = commutator (Model (ZMod 2)) :=
    Subgroup.Normal.map_conj_eq _ x
  change (commutator (Model (ZMod 2))).map c ≤ (E ⊔ zpowers (g.val * a * g.val⁻¹)).map c
  rw [hD, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hg : c (g.val * a * g.val⁻¹) = g'.val * c a * g'.val⁻¹ := by
    change x * ((x⁻¹ * g'.val * x) * a * (x⁻¹ * g'.val * x)⁻¹) * x⁻¹ =
      g'.val * (x * a * x⁻¹) * g'.val⁻¹
    group
  change commutator (Model (ZMod 2)) ≤ E' ⊔ zpowers (c (g.val * a * g.val⁻¹))
  rw [hg]
  exact hgen


end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction
