module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.TerminalGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Geometry

/-!
# The literal natural point-stabilizer action

A nonzero fixed vector modulo the central line prevents its support from being
exchanged with the other separated support. Thus the actual quotient centralizer
lies in the support normalizer. Restricting the full natural action gives exactly
the stabilizer of that vector. The natural summand, its dual and the fixed factor
of U/Z detect the original two-core, so the restricted action has two-group kernel.

The final consumer keeps H=Mc and the same suitable u. It constructs the action
and S3 quotient of P=h.kernel(zpowers u), including compatibility with the original
conjugation section. The natural/dual markings and decomposition are explicit
14.6.22--23 inputs; the elimination of the other component alternatives is separate.

Source: Aschbacher--Smith, 14.6.22--24 and the final paragraph on printed p.1042.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

omit [Finite G] in
private theorem cyclic_square_one_cases (u : G) (hu2 : u ^ 2 = 1)
    (a : G) (ha : a ∈ zpowers u) : a = 1 ∨ a = u := by
  let A : Subgroup G := {
    carrier := {a | a = 1 ∨ a = u}
    one_mem' := Or.inl rfl
    mul_mem' := by rintro a b (rfl | rfl) (rfl | rfl) <;> simp_all [pow_two]
    inv_mem' := by
      rintro a (rfl | rfl)
      · simp
      · exact Or.inr (inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hu2)) }
  exact (zpowers_le.mpr (show u ∈ A from Or.inr rfl)) ha


/-- The original quotient centralizer is detected by the chosen involution alone. -/
theorem mem_point_kernel_iff (u : G) (huH : u ∈ D.H) (hu2 : u ^ 2 = 1) (x : G) :
    x ∈ h.kernel (zpowers u) ↔ x ∈ D.H ∧ ⁅u,x⁆ ∈ D.V₁ := by
  rw [h.mem_kernel_iff (zpowers_le.mpr huH)]
  constructor
  · exact fun hx => ⟨hx.1,hx.2 u (mem_zpowers u)⟩
  · rintro ⟨hx, hc⟩
    refine ⟨hx,fun a ha => ?_⟩
    rcases cyclic_square_one_cases u hu2 a ha with rfl | rfl
    · simp
    · exact hc

/-- Fixing a nonzero quotient vector cannot interchange its separated supports. -/
theorem point_kernel_le_support_normalizer
    (W W' : Subgroup G) (hWH : W ≤ D.H) (hZW : D.V₁ ≤ W)
    (hsep : W ⊓ W' ≤ D.V₁)
    (hpair : ∀ x ∈ D.H, W.map (MulAut.conj x).toMonoidHom = W ∨
      W.map (MulAut.conj x).toMonoidHom = W')
    (u : G) (hu : u ∈ W) (huz : u ∉ D.V₁) (hu2 : u ^ 2 = 1) :
    h.kernel (zpowers u) ≤ D.H ⊓ normalizer (W : Set G) := by
  intro x hx
  obtain ⟨hxH,hcomm⟩ := (mem_point_kernel_iff h u (hWH hu) hu2 x).mp hx
  refine ⟨hxH,mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  rcases hpair x hxH with he | he
  · exact he
  · exfalso
    have hxW : (MulAut.conj x) u ∈ W := by
      have hh := W.mul_mem (W.inv_mem (hZW hcomm)) hu
      simpa [commutatorElement_def, MulAut.conj_apply, mul_assoc] using hh
    have hxW' : (MulAut.conj x) u ∈ W' :=
      he ▸ mem_map_of_mem (MulAut.conj x).toMonoidHom hu
    have hxZ := hsep ⟨hxW,hxW'⟩
    have hn := (centralizer_le_normalizer (D.V₁ : Set G)) (h.H_centralizes hxH)
    exact huz ((hn u).mpr hxZ)

/-- The full natural action restricts to the literal point centralizer. Its
image, kernel, and compatibility with the original section are all retained. -/
theorem point_action_of_natural_section
    (W W' : Subgroup G) (hWH : W ≤ D.H) (hZW : D.V₁ ≤ W)
    (hsep : W ⊓ W' ≤ D.V₁)
    (hpair : ∀ x ∈ D.H, W.map (MulAut.conj x).toMonoidHom = W ∨
      W.map (MulAut.conj x).toMonoidHom = W')
    (f : (D.H ⊓ normalizer (W : Set G) : Subgroup G) →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ D.QH.subgroupOf (D.H ⊓ normalizer (W : Set G)))
    (c : BinaryConjugationSection (D.H ⊓ normalizer (W : Set G)) W D.V₁
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (u : G) (hu : u ∈ W) (huz : u ∉ D.V₁) (hu2 : u ^ 2 = 1) :
    ∃ a : SourcePointStabilizerAction (h.kernel (zpowers u)),
      a.point = (c.coordinates ⟨u,hu⟩).toAdd ∧
      (∀ x : h.kernel (zpowers u), ∀ hx : (x : G) ∈ D.H ⊓ normalizer (W : Set G),
        a.actor x = f ⟨x,hx⟩) ∧
      (∀ (x : h.kernel (zpowers u)) (w : W),
        a.actor x (c.coordinates w).toAdd =
          (c.coordinates ⟨(x : G) * w * (x : G)⁻¹,
            (mem_normalizer_iff.mp
              ((point_kernel_le_support_normalizer h W W' hWH hZW hsep hpair u hu huz hu2)
                x.property).2 w).mp w.property⟩).toAdd) := by
  let A := D.H ⊓ normalizer (W : Set G)
  let P := h.kernel (zpowers u)
  have hPA : P ≤ A := point_kernel_le_support_normalizer h W W' hWH hZW hsep hpair u hu huz hu2
  let inc : P →* A := inclusion hPA
  let actor := f.comp inc
  let v := (c.coordinates ⟨u,hu⟩).toAdd
  have hv : v ≠ 0 := by
    intro hv
    exact huz ((c.coordinates_eq_one_iff ⟨u,hu⟩).mp hv)
  have hfix (x : A) : f x v = v ↔ (x : G) ∈ P := by
    rw [mem_point_kernel_iff h u (hWH hu) hu2]
    have hc := c.fixed_coordinate_iff_commutator_mem x ⟨u,hu⟩
    exact hc.trans (and_iff_right x.property.1).symm
  have hr : actor.range = MulAction.stabilizer (BinaryLinear.GL (Fin 3 → ZMod 2)) v := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact (hfix (inc x)).mpr x.property
    · intro hy
      obtain ⟨x,rfl⟩ := hf y
      have hxP : (x : G) ∈ P := (hfix x).mp hy
      exact ⟨⟨x,hxP⟩,rfl⟩
  have hk : IsPGroup 2 actor.ker := by
    have he : actor.ker = f.ker.comap inc := rfl
    rw [he]
    exact ((isPGroup_pCoreIn 2 D.H).comap_subtype.to_le hker).comap_of_injective inc
      (inclusion_injective hPA)
  refine ⟨⟨actor,v,hv,hr,hk⟩,rfl,fun _ _ => rfl,?_⟩
  intro x w
  exact (c.equivariant (inc x) w).symm

include h in
/-- Faithfulness on a natural summand and its dual detects the original two-core.
The fixed factor of U/Z is retained, rather than discarded from the span. -/
theorem natural_kernel_le_core_of_dual_decomposition
    (W W' C : Subgroup G)
    (f : (D.H ⊓ normalizer (W : Set G) : Subgroup G) →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (c : BinaryConjugationSection (D.H ⊓ normalizer (W : Set G)) W D.V₁
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (c' : BinaryConjugationSection (D.H ⊓ normalizer (W : Set G)) W' D.V₁
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f)))
    (hcover : ∀ v ∈ D.UH, ∃ w ∈ W, ∃ w' ∈ W', ∃ v₀ ∈ C, v = w * w' * v₀)
    (hfixed : ∀ x ∈ D.H, ∀ v₀ ∈ C, ⁅v₀,x⁆ ∈ D.V₁) :
    f.ker ≤ D.QH.subgroupOf (D.H ⊓ normalizer (W : Set G)) := by
  intro x hx
  change (x : G) ∈ D.QH
  rw [← h.kernel_UH_eq_QH]
  apply (h.mem_kernel_iff h.UH_le_H).mpr
  refine ⟨x.property.1,?_⟩
  intro v hv
  obtain ⟨w,hw,w',hw',v₀,hv₀,rfl⟩ := hcover v hv
  have hx1 : f x = 1 := hx
  have hcw : ⁅w,(x : G)⁆ ∈ D.V₁ := by
    apply (c.fixed_coordinate_iff_commutator_mem x ⟨w,hw⟩).mp
    change f x _ = _
    rw [hx1]
    rfl
  have hcw' : ⁅w',(x : G)⁆ ∈ D.V₁ := by
    apply (c'.fixed_coordinate_iff_commutator_mem x ⟨w',hw'⟩).mp
    apply LinearMap.ext
    intro a
    change (c'.coordinates ⟨w',hw'⟩).toAdd ((f x⁻¹) a) = _
    rw [map_inv,hx1,inv_one]
    rfl
  have hmul (a b : G) (ha : a ∈ D.H)
      (hac : ⁅a,(x : G)⁆ ∈ D.V₁) (hbc : ⁅b,(x : G)⁆ ∈ D.V₁) :
      ⁅a*b,(x : G)⁆ ∈ D.V₁ := by
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact D.V₁.mul_mem
      (((centralizer_le_normalizer (D.V₁ : Set G)) (h.H_centralizes ha) _).mp hbc) hac
  have hwH := (c.section_le hw).1
  have hw'H := (c'.section_le hw').1
  exact hmul (w*w') v₀ (D.H.mul_mem hwH hw'H)
    (hmul w w' hwH hcw hcw') (hfixed x x.property.1 v₀ hv₀)

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- On the original H=Mc and the same suitable u, the natural/dual decomposition
constructs the parabolic action and its literal S3 quotient. No parabolic action,
image, or two-group kernel is an input to this source application. -/
theorem source_parabolic_action_of_natural_pair
    (W W' C : Subgroup G)
    (hsep : W ⊓ W' ≤ centralInvolutions T)
    (hpair : ∀ x ∈ Mc, W.map (MulAut.conj x).toMonoidHom = W ∨
      W.map (MulAut.conj x).toMonoidHom = W')
    (f : (Mc ⊓ normalizer (W : Set G) : Subgroup G) →* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hf : Function.Surjective f)
    (c : BinaryConjugationSection (Mc ⊓ normalizer (W : Set G)) W (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (c' : BinaryConjugationSection (Mc ⊓ normalizer (W : Set G)) W' (centralInvolutions T)
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f)))
    (hcover : ∀ v ∈ conjugateSpanBy (localModule T M) Mc,
      ∃ w ∈ W, ∃ w' ∈ W', ∃ v₀ ∈ C, v = w * w' * v₀)
    (hfixed : ∀ x ∈ Mc, ∀ v₀ ∈ C, ⁅v₀,x⁆ ∈ centralInvolutions T)
    (u : G) (huW : u ∈ W)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u) :
    let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let P := h.kernel (zpowers u)
    Nonempty (SourceParabolicAction P) ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      ∃ a : SourcePointStabilizerAction P,
        a.point = (c.coordinates ⟨u,huW⟩).toAdd ∧
        ∀ x : P, ∀ hx : (x : G) ∈ Mc ⊓ normalizer (W : Set G), a.actor x = f ⟨x,hx⟩ := by
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  have hWH : W ≤ Mc := c.section_le.trans inf_le_left
  have huz : u ∉ centralInvolutions T := by
    intro hz
    apply hu.2.2.2.1
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (h.H_centralizes (pCoreIn_le 2 Mc hx) u hz).symm
  let := h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu.1
  obtain ⟨a,ha,hcompat,_⟩ := point_action_of_natural_section h W W' hWH c.kernel_le
    hsep hpair f hf (natural_kernel_le_core_of_dual_decomposition h W W' C f c c' hcover hfixed)
    c u huW huz hu2
  exact ⟨⟨.point a⟩,(SourceParabolicAction.point a).quotient,a,ha,hcompat⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
