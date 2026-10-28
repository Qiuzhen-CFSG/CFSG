module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RankOneCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LocalActions

/-!
# The panel radical from a naturally marked rank-one quotient

Suppose the faithful endpoint quotient is marked in a finite group whose
full Borel is a Sylow two-normalizer, of index one plus the Sylow order.
The preceding root-coordinate theorem identifies the source simple root
with that entire Sylow subgroup. Every element of the source remainder
therefore has the same quotient image as a simple-root element. Their
difference lies in the panel kernel, and both it and the remainder lie in
the reflected Borel. Disjointness forces the root element to be trivial.
Thus the remainder lies in the actual panel kernel, and the whole endpoint
normalizes it. Neither simplicity nor perfectness of the model is used.

Source: Fong--Seitz I (1973), (2B), pp.7--9, and its use in (3G) and (6H).
The Ree MixedBounds consumer supplies the natural linear and Suzuki panel
degrees, including both binary models, before applying the root intervals.
This does not construct the preceding natural rank-one marking.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X M : Type*} [Group X] [Group M] [Finite M] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* M) (T : Sylow 2 M)
  (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set M))

include μ hB in
theorem remainder_le_panelKernel_of_marking
    (hdegree : (normalizer (T : Set M)).index = 1 + Nat.card T) :
    simpleRemainder Q split i ≤ embeddedPanelKernel Q i := by
  let f : Endpoint Q i →* M := μ.toMonoidHom.comp (QuotientGroup.mk' (panelKernel Q i))
  let U : Subgroup (Endpoint Q i) := split.U.subgroupOf (Endpoint Q i)
  have htwo : IsPGroup 2 (U.map f) := split.isTwo.comap_subtype.map f
  have hn : U.map f ≤ normalizer (T : Set M) := by
    rintro y ⟨u,hu,rfl⟩
    rw [← hB]
    exact mem_map_of_mem μ.toMonoidHom
      (mem_map_of_mem (QuotientGroup.mk' (panelKernel Q i)) (split.U_le hu))
  have hUT : U.map f ≤ T := by
    have he := htwo.inf_normalizer_sylow T
    rw [inf_of_le_left hn] at he
    exact le_of_inf_eq he.symm
  intro x hx
  let xP : Endpoint Q i := ⟨x,Q.tits.B_le_standardParabolic _ (split.U_le hx.1)⟩
  have hfx : f xP ∈ T := hUT (mem_map_of_mem f hx.1)
  obtain ⟨r,hr⟩ := (modelRootEquiv Q split i μ T hB hdegree).surjective ⟨f xP,hfx⟩
  have he : rootProjection Q split i r = QuotientGroup.mk' (panelKernel Q i) xP := by
    apply μ.injective
    exact (modelRootEquiv_apply Q split i μ T hB hdegree r).symm.trans (congrArg Subtype.val hr)
  have hk : rootInEndpoint Q split i r * xP⁻¹ ∈ panelKernel Q i := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (panelKernel Q i) (rootInEndpoint Q split i r * xP⁻¹) = 1
    rw [map_mul, map_inv]
    change rootProjection Q split i r * (QuotientGroup.mk' (panelKernel Q i) xP)⁻¹ = 1
    rw [he, mul_inv_cancel]
  have hk' : (r : X ⧸ Q.D)*x⁻¹ ∈ embeddedPanelKernel Q i :=
    mem_map_of_mem (Endpoint Q i).subtype hk
  have hxB : x ∈ borelConjugate (Q.simple i) :=
    (comap_mono split.U_le) hx.2
  have hrB : (r : X ⧸ Q.D) ∈ borelConjugate (Q.simple i) := by
    have hh := (borelConjugate (Q.simple i)).mul_mem
      (embeddedPanelKernel_le_reflectedBorel Q i hk') hxB
    simpa only [inv_mul_cancel_right] using hh
  have hr1 : r = 1 := Subtype.ext
    (disjoint_def.mp (simpleRoot_disjoint_conjugateBorel Q split i) r.property hrB)
  have hx1 : QuotientGroup.mk' (panelKernel Q i) xP = 1 := by
    rw [← he, hr1, map_one]
  exact mem_map_of_mem (Endpoint Q i).subtype ((QuotientGroup.eq_one_iff xP).mp hx1)

include μ hB in
theorem remainder_parabolic_normalizes_of_marking
    (hdegree : (normalizer (T : Set M)).index = 1 + Nat.card T) :
    Endpoint Q i ≤ normalizer (simpleRemainder Q split i : Set (X ⧸ Q.D)) :=
  HexagonStructure.remainder_parabolic_normalizes Q split i
    (remainder_le_panelKernel_of_marking Q split i μ T hB hdegree)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
