module
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Faithful FF-modules from invariant sections

Suppose a binary representation has an invariant section killed by a solvable
normal subgroup Q, and F*(G/Q) is quasisimple with trivial two-core. If F*(G/Q)
acts nontrivially on that section, its action kernel lies in the center of F*
and hence in the solvable radical. Each elementary two-subgroup of G/Q acts
faithfully on the section. A displacement bound by the rank of the image of A
modulo Q therefore produces an offender for the actual quotient by the section's
action kernel. The constructed quotient representation is faithful.

This proves the kernel, rank-preservation and FF-contradiction steps of E.5.4.
Existence of an active chief section and the two-core kernel condition remain
explicit inputs; no chief section or offender is included in a definition.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.5.4,
printed p.244; the quasisimple kernel argument also occurs in B.1.5(8).
-/

open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterE.NoFFAlternative
variable {G H V : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A kernel avoiding a quasisimple Fitting subgroup is solvable. -/
private theorem kernel_le_radical_of_nontrivial_fitting_image
    {D : Type*} [Group D]
    (hL : IsQuasisimple (generalizedFitting H))
    (f : H →* D) (hmove : ¬ generalizedFitting H ≤ f.ker) :
    f.ker ≤ solvableRadical H := by
  have h := ChapterB.QuasisimpleSections.kernel_le_fitting_center hL f hmove
  have hs : Group.IsSolvable f.ker := Group.isSolvable_of_comm (by
    intro a b
    obtain ⟨a', ha', hea⟩ := h a.property
    obtain ⟨b', hb', heb⟩ := h b.property
    apply Subtype.ext
    change (a : H) * (b : H) = (b : H) * (a : H)
    rw [← hea, ← heb]
    exact congrArg (fun l : generalizedFitting H => (l : H))
      ((mem_center_iff.mp ha') b').symm)
  exact le_solvableRadical _ inferInstance hs

/-- The faithful action on G/ker(action) is an actual representation. -/
@[expose] public noncomputable def faithfulQuotient (ρ : Representation (ZMod 2) G V) :
    Representation (ZMod 2) (G ⧸ (actionHom ρ).ker) V :=
  (imageRepresentation ρ).comp
    (QuotientGroup.quotientKerEquivOfSurjective
      (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective).toMonoidHom

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
public theorem faithfulQuotient_injective (ρ : Representation (ZMod 2) G V) :
    Function.Injective (faithfulQuotient ρ) :=
  (imageRepresentation_injective ρ).comp
    (QuotientGroup.quotientKerEquivOfSurjective
      (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective).injective

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
public theorem faithfulQuotient_apply (ρ : Representation (ZMod 2) G V) (g : G) :
    faithfulQuotient ρ (QuotientGroup.mk' (actionHom ρ).ker g) = ρ g := rfl

/-- A section with the indicated displacement bound yields a faithful FF
quotient. Nontriviality on F* supplies faithfulness of the elementary image. -/
public theorem faithful_ff_quotient_of_section
    (Q : Subgroup G) [Q.Normal] [Group.IsSolvable Q]
    (hcore : pCore 2 (G ⧸ Q) = ⊥)
    (hL : IsQuasisimple (generalizedFitting (G ⧸ Q)))
    (ρ : Representation (ZMod 2) G V) (U W : Subrepresentation ρ)
    (hQ : Q ≤ (actionHom (sectionRepresentation ρ U W)).ker)
    (hmove : ¬ (generalizedFitting (G ⧸ Q)).comap (QuotientGroup.mk' Q) ≤
      (actionHom (sectionRepresentation ρ U W)).ker)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hne : ¬ A ≤ Q)
    (hdisp : fixedCodim ρ A ≤ rank (A.map (QuotientGroup.mk' Q))) :
    let σ := sectionRepresentation ρ U W
    Q ≤ (actionHom σ).ker ∧ (actionHom σ).ker ≤ solvableRadical G ∧
      Function.Injective (faithfulQuotient σ) ∧ IsFFModule (faithfulQuotient σ) := by
  let σ := sectionRepresentation ρ U W
  let π := QuotientGroup.mk' Q
  let f := QuotientGroup.lift Q (actionHom σ) hQ
  have hm : ¬ generalizedFitting (G ⧸ Q) ≤ f.ker := by
    intro h
    apply hmove
    intro g hg
    exact h hg
  have hker : (actionHom σ).ker = f.ker.comap π := rfl
  have hk : (actionHom σ).ker ≤ solvableRadical G := by
    let _ : Group.IsSolvable π.ker := by
      change Group.IsSolvable (QuotientGroup.mk' Q).ker
      rw [QuotientGroup.ker_mk']
      infer_instance
    rw [hker, ← comap_solvableRadical_eq_of_solvable_ker π
      (QuotientGroup.mk'_surjective Q)]
    exact comap_mono (kernel_le_radical_of_nontrivial_fitting_image hL f hm)
  let a := A.map π
  let _ : IsElementaryAbelian 2 a := IsElementaryAbelian.map π
  have hf : ∀ x ∈ a, f x = 1 → x = 1 :=
    ChapterB.QuasisimpleSections.faithful_on_nontrivial_fitting_image hcore hL f hm
      (IsElementaryAbelian.isPGroup 2 a)
  let X := (actionHom σ).ker
  let q := QuotientGroup.mk' X
  let B := A.map q
  let g : (G ⧸ Q) →* G ⧸ X := QuotientGroup.lift Q q
    (by simpa only [q, QuotientGroup.ker_mk'] using hQ)
  have hB : B = a.map g := by rw [map_map]; rfl
  have hga : Function.Injective (g.comp a.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply hf x x.property
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective Q x
    change g (x : G ⧸ Q) = 1 at hx
    rw [← hz] at hx ⊢
    exact (QuotientGroup.eq_one_iff z).mp hx
  have hcard : rank B = rank a := by
    rw [hB]
    unfold rank
    congr 1
    let e : a ≃* a.map g := MulEquiv.ofBijective (g.subgroupMap a)
      ⟨fun x y hxy => hga (congrArg Subtype.val hxy), g.subgroupMap_surjective a⟩
    exact (Nat.card_congr e.toEquiv).symm
  refine ⟨hQ, hk, faithfulQuotient_injective σ, B, ⟨?_, IsElementaryAbelian.map q⟩, ?_⟩
  · intro hb
    have hab : a = ⊥ := by
      apply bot_unique
      intro x hx
      apply hf x hx
      obtain ⟨z, hz, rfl⟩ := hx
      have hzB : q z ∈ B := mem_map_of_mem q hz
      rw [hb, mem_bot] at hzB
      exact (QuotientGroup.eq_one_iff z).mp hzB
    exact hne (by simpa only [π, QuotientGroup.ker_mk'] using (map_eq_bot_iff A).mp hab)
  · have hcod : fixedCodim (faithfulQuotient σ) B = fixedCodim σ A := by
      have he : fixedSpace (faithfulQuotient σ) B = fixedSpace σ A :=
        (fixedSpace_comp_map (faithfulQuotient σ) q A).symm
      unfold fixedCodim
      congr 2
    rw [hcod, hcard]
    exact (fixedCodim_section_le ρ U W A).trans hdisp
end CFSG.Quasithin.ChapterE.NoFFAlternative
