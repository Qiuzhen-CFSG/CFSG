module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedCoreInvolutions
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.PlaneOverlaps
public import Theory.Mathieu.M22.Properties.OuterHexadRadical

/-!
# The original cocode image in the hexad design action

A two-subgroup meets the full cubic kernel only in Q: its image in the
central quotient is disjoint from the order-three kernel. For the actual
cocode subgroup of order 2048 with Q-intersection of order 128, its image
therefore has order sixteen. Relative normality in the full hexad overlap
places that image in the native hexad two-core, which also has order
sixteen. This identifies the literal image with the pointwise translations.

The Intersection module uses this equality to prove transversality of the
invariant elementary preimage, removing the extra premise in Todd splitting.
Source: Aschbacher--Segev (4.8), Invent. Math. 105 (1991), p.599,
DOI 10.1007/BF01232280.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
open Subgroup LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu M22ValueBound.Concrete
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- A two-subgroup meets the full cubic kernel only in Q. -/
theorem two_subgroup_inf_cubic
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (U : Subgroup (centralizer z)) (hU : IsPGroup 2 U) :
    U ⊓ CubicLift.subgroup e = U ⊓ core z := by
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1,?_⟩
    let q := QuotientGroup.mk' (core z)
    have h3 : IsPGroup 3 e.projection.ker :=
      IsPGroup.of_card (n := 1) (by rw [e.kernel_card]; norm_num)
    have hz := disjoint_def.mp ((hU.map q).disjoint_of_coprime h3 (by decide))
      (mem_map_of_mem q hx.1) hx.2
    exact (QuotientGroup.eq_one_iff x).mp hz
  · exact inf_le_inf_left _ (CubicLift.core_le e)

/-- The original elementary cocode image is exactly the native hexad translation group. -/
theorem cocode_design_image
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
    (U H : Subgroup (centralizer z)) (hU : IsPGroup 2 U)
    (hUc : Nat.card U=2048) (hIc : Nat.card (U ⊓ core z : Subgroup (centralizer z))=128)
    (hUH : U ≤ H) (hHU : H ≤ normalizer (U : Set (centralizer z)))
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hH : H=(designStabilizer B).comap (CubicLift.projection e)) :
    U.map (designAutEquiv.symm.toMonoidHom.comp (CubicLift.projection e)) =
      (m22HexadPointwiseKernel B).map inclusion := by
  let f := designAutEquiv.symm.toMonoidHom.comp (CubicLift.projection e)
  let R := MulAction.stabilizer m22DesignAut B
  have hf : Function.Surjective f := designAutEquiv.symm.surjective.comp (CubicLift.projection_surjective e)
  have hker : f.ker=CubicLift.subgroup e :=
    MonoidHom.ker_comp_of_injective _ _ designAutEquiv.symm.injective
  have hHf : H=R.comap f := by
    rw [hH]
    ext x
    change CubicLift.projection e x ∈ (MulAction.stabilizer m22DesignAut B).map m22DesignAutToAut ↔
      designAutEquiv.symm (CubicLift.projection e x) ∈ R
    constructor
    · rintro ⟨u,hu,he⟩
      change designAutEquiv u=CubicLift.projection e x at he
      rw [←he,MulEquiv.symm_apply_apply]
      exact hu
    · intro hx
      exact ⟨designAutEquiv.symm (CubicLift.projection e x),hx,designAutEquiv.apply_symm_apply _⟩
  have hmap : H.map f=R := by
    rw [hHf,map_comap_eq_self]
    rw [MonoidHom.range_eq_top.mpr hf]
    exact le_top
  have hle : U.map f ≤ R := hmap ▸ map_mono hUH
  have hnorm : R ≤ normalizer (U.map f : Set m22DesignAut) := by
    rw [←hmap]
    exact (map_mono hHU).trans (U.le_normalizer_map f)
  have hcore := le_pCoreIn_of_normalizes (hU.map f) hle hnorm
  rw [M22OuterHexad.radical_eq hB R (by
    rintro x ⟨u,hu,rfl⟩
    exact hu) le_rfl] at hcore
  apply eq_of_le_of_card_ge hcore
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map U f
  rw [hker,two_subgroup_inf_cubic e U hU,hIc,hUc] at hc
  rw [card_map_of_injective inclusion_injective,m22HexadPointwiseKernel_card hB]
  omega

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
end
