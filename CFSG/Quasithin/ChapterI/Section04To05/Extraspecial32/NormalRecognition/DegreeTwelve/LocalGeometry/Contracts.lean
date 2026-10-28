module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.Interfaces
public import Theory.GroupTheory.TwoInvolutionClassOrder

/-!
# Inputs to the local geometry and order calculation

These contracts separate three source arguments: selection of the conjugate
core and its marked involution, fusion and mixed-pair counting in `C_G(z)`,
and recognition and counting in the second involution centralizer.
They are intermediate conclusions, not additional source hypotheses.

The counts use the actual ambient conjugacy classes and the canonical
half-order power of the product. The centralizer alternatives include actual
group isomorphisms; neither alternative assumes the ambient order.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.2–2.8 and 4.1–4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve

open Subgroup Theory.GroupTheory.TwoInvolutionClassOrder

variable {G : Type*} [Group G] {z : G}

/-- The selected local configuration before choosing the second involution.
In particular, proving `intersection_ne_fusion` requires the source's 2.8
argument; nonnormality of `F` alone does not imply that an arbitrary `E`
differs from `F`. The inverter acts on the original chosen Sylow subgroup. -/
public structure SelectedFusionData [Finite G] (h : Hypotheses z) where
  g : G
  fused_mem : g * z * g⁻¹ ∈ coreInG z
  fused_ne : g * z * g⁻¹ ≠ z
  intersection_elementary : IsElementaryAbelian 2 (coreIntersection z g)
  intersection_card : Nat.card (coreIntersection z g) = 8
  intersection_ne_fusion : coreIntersection z g ≠ fusionCore z
  u : G
  u_order : orderOf u = 2
  u_centralizes : u ∈ Centralizer z
  u_conjugate_core : u ∈ conjugateCore z g
  u_not_core : u ∉ coreInG z
  u_fused : IsConj z u
  u_inverts_X : ∀ x : h.X,
    u * ((x : Centralizer z) : G) * u⁻¹ = ((x : Centralizer z) : G)⁻¹

/-- The two-class assertion of 2.7 and the common centralizer count of 4.3.
The source's `a(z)` is precisely the Thompson mixed-pair count used here. -/
public structure LocalInvolutionCensus (z t : G) : Prop where
  classes : ∀ a : G, orderOf a = 2 → IsConj z a ∨ IsConj t a
  count_at_z : kappa z t z = 240

/-- The two possibilities in 4.2, with the mixed-pair counts at the second
involution. Each isomorphism concerns the literal ambient centralizer. -/
@[expose] public def SecondCentralizerAlternative (z t : G) : Prop :=
  (Nonempty (Centralizer t ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∧
      kappa z t t = 3) ∨
  (Nonempty (Centralizer t ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 5))) ∧
      kappa z t t = 195)

end CFSG.Quasithin.Extraspecial32.DegreeTwelve
