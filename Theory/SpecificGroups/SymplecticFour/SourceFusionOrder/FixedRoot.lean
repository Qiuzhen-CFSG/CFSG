module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.FixedFlag
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Lattice
public import Theory.FieldTheory.ScalarTwistedFixedPoints
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport

/-!
# The binary fixed long root of an outer flag involution

For a field of order four, the fixed coefficient field of a field involution
has order two. Its long root therefore has exactly one nonidentity fixed
element. The previously established Borel descent transports this statement
to every outer involution preserving the original flag, retaining the literal
point-local center. The Chapter 6 application uses its uniqueness to force
original ambient fusion from a root involution into the outer Sylow coset.

Source: Aschbacher--Smith F.4.37, printed p.293 of refs/quasithin.pdf,
the exceptional Sp4(4) paragraph. This is the fixed-root calculation, not
the subsequent A6/D8 exclusion or an ambient order comparison.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open DiagramAutomorphisms Representation.OneCohomology.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem fixed_parameter_binary (hF : Nat.card F=4)
    (σ : F ≃+* F) (ho : orderOf σ=2) (x : F) (hx : σ x=x) : x=0 ∨ x=1 := by
  have hs : Function.Involutive σ := by
    intro t
    have hh : σ^2=1 := by simpa only [ho] using pow_orderOf_eq_one σ
    exact congrArg (fun a : F ≃+* F => a t) hh
  have hn : σ≠RingEquiv.refl F := by
    intro hh
    have hh' : σ=1 := hh
    rw [hh',orderOf_one] at ho
    omega
  have hc := FiniteField.card_involution_fixed_sq σ hs hn
  have hK : Nat.card (FixedBy.subfield F σ)=2 := by rw [hF] at hc; nlinarith
  let e := Binary.fieldEquivZModTwo (FixedBy.subfield F σ) hK
  have he : ∀ t : ZMod 2, t=0 ∨ t=1 := by decide
  rcases he (e ⟨x,hx⟩) with he | he
  · left
    exact congrArg Subtype.val (e.injective (he.trans (map_zero e).symm))
  · right
    exact congrArg Subtype.val (e.injective (he.trans (map_one e).symm))

omit [Finite F] [CharP F 2] in
private theorem field_root_zero (σ : F ≃+* F) (t : F) :
    fieldAutomorphism σ (rootElement 0 t)=rootElement 0 (σ t) := by
  apply Subtype.ext
  change (rootMatrix 0 t).map σ = rootMatrix 0 (σ t)
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.fromBlocks,Matrix.single]

/-- Over field order four, an outer flag involution fixes exactly one
nonidentity element of the actual long-root center. -/
theorem outer_fixed_root_unique (hF : Nat.card F=4)
    (a : MulAut (Sp F)) (hao : orderOf a=2)
    (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hi : a ∉ MulAut.innerSubgroup (Sp F)) :
    ∃ z : Sp F, z≠1 ∧ z ∈ (center (pointLocal (F := F))).map pointLocal.subtype ∧
      a z=z ∧ ∀ x ∈ (center (pointLocal (F := F))).map pointLocal.subtype,
        a x=x → x=1 ∨ x=z := by
  have hF' : Nat.card F=2^2 := hF
  obtain ⟨σ,hσ,c,hc⟩ := outer_flag_involution_normal_form hF' (by decide) a hao ha hi
  let e := MulAut.conj c.val
  have hR : (center (pointLocal (F := F))).map pointLocal.subtype=RootSubgroup.group 0 :=
    PointRadicalAction.center_eq_root hF' (by decide)
  have hcN : c.val ∈ normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) := by
    rw [RootNormalizerResidual.normalizer_zero_eq]
    exact c.property.1
  have heR (x : Sp F) : x ∈ RootSubgroup.group 0 ↔ e x ∈ RootSubgroup.group 0 := hcN x
  have hact (x : Sp F) : a (e x)=e (fieldAutomorphism σ x) := by
    rw [hc]
    change (e * fieldAutomorphism σ * e⁻¹) (e x)=_
    simp only [MulAut.mul_apply,MulAut.inv_apply,e.symm_apply_apply]
  let z := e (rootElement 0 (1:F))
  have hz1 : z≠1 := by
    intro hh
    have hh' : rootElement 0 (1:F)=1 := e.map_eq_one_iff.mp hh
    exact one_ne_zero (RootSubgroup.element_injective 0
      (hh'.trans (RootSubgroup.element_zero 0).symm))
  refine ⟨z,hz1,?_,?_,?_⟩
  · rw [hR]
    exact (heR _).mp ((RootSubgroup.mem_group_iff _ _).mpr ⟨1,rfl⟩)
  · change a (e (rootElement 0 (1:F)))=_
    rw [hact,field_root_zero,map_one]
  · intro x hx hfix
    have hx' : e.symm x ∈ RootSubgroup.group 0 :=
      (heR _).mpr (by simpa only [e.apply_symm_apply] using hR ▸ hx)
    obtain ⟨t,ht⟩ := (RootSubgroup.mem_group_iff _ _).mp hx'
    have hx : x=e (rootElement 0 t) := by rw [ht,e.apply_symm_apply]
    have hσt : σ t=t := by
      rw [hx,hact,field_root_zero] at hfix
      exact RootSubgroup.element_injective 0 (e.injective hfix)
    rcases fixed_parameter_binary hF σ hσ t hσt with rfl | rfl
    · left; rw [hx,RootSubgroup.element_zero,map_one]
    · exact Or.inr hx
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
