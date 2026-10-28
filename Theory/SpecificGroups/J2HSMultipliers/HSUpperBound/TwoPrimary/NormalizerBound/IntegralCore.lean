module

public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound.IntegralCore.ActionData
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound.IntegralCore.ConcreteAction
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary.NormalizerBound.IntegralCore.Normalization

/-!
# Applying integral core cohomology to the literal HS cover

Conjugation on the abelian core preimage descends through a central cover.
The failure of a specified core section to respect that action is a right
crossed homomorphism with values in the actual central kernel. It vanishes
on Q. A correction by a kernel-valued homomorphism gives another section.

If the corrected errors lie in a central subgroup Z, all core displacements
lie in the product of that section and Z, and their intersection with the
kernel lies in Z. The literal integral action certificate and its crossed
homomorphism normalization provide such a Z of order at most two. Applying
them to the constructed cocycle proves |[g⁻¹(Q),D] ∩ ker(g)| ≤ 2. This needs
only a finite central cover and its core section: no perfectness, involution
lift, exponent bound on ker(g), or invariant section is assumed.

Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407, and the HS
normalizer argument of I.2.2(5), printed p.412. This does not invoke the
center-order-two assumption of the latter to prove a center bound.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
open Sporadic.LeechRelated.HS BlockNormalizer
variable {D : Type*} [Group D]

theorem coreDisplacements_inf_ker_le_of_section_errors (g : D →* baseNormalizer) (hk : g.ker ≤ center D)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype)
    (Z : Subgroup D) (hZ : Z ≤ g.ker)
    (herr : ∀ (d : D) (q : pCore 2 baseNormalizer),
      d * s q * d⁻¹ / s (MulAut.conjNormal (g d) q) ∈ Z) :
    coreDisplacements g ⊓ g.ker ≤ Z := by
  have hsec (q : pCore 2 baseNormalizer) : g (s q) = q := DFunLike.congr_fun hs q
  have hc (z : D) (hz : z ∈ Z) (d : D) : d * z = z * d :=
    mem_center_iff.mp (hk (hZ hz)) d
  let : Z.Normal := ⟨fun z hz d => by
    simpa only [hc z hz d, mul_inv_cancel_right] using hz⟩
  have hR : coreDisplacements g ≤ s.range ⊔ Z := by
    apply commutator_le.mpr
    intro x hx d _
    let q : pCore 2 baseNormalizer := ⟨g x, hx⟩
    rw [CentralExtension.commutator_eq_of_image_eq g hk (hsec q).symm rfl]
    have hconj : d * s q * d⁻¹ ∈ s.range ⊔ Z := by
      have he := (show Z ≤ s.range ⊔ Z from le_sup_right) (herr d q)
      have hsq : s (MulAut.conjNormal (g d) q) ∈ s.range ⊔ Z :=
        (show s.range ≤ s.range ⊔ Z from le_sup_left) ⟨_, rfl⟩
      simpa only [div_mul_cancel] using (s.range ⊔ Z).mul_mem he hsq
    have hsq : s q ∈ s.range ⊔ Z := (show s.range ≤ s.range ⊔ Z from le_sup_left) ⟨q, rfl⟩
    have heq : ⁅s q, d⁆ = s q * (d * s q * d⁻¹)⁻¹ := by
      simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
    rw [heq]
    exact (s.range ⊔ Z).mul_mem hsq ((s.range ⊔ Z).inv_mem hconj)
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup_of_normal_right.mp (hR hx.1)
  obtain ⟨q, rfl⟩ := hy
  have hq : q = 1 := by
    apply Subtype.ext
    have he : g (s q * z) = 1 := hx.2
    rw [map_mul, hsec, show g z = 1 from hZ hz, mul_one] at he
    exact he
  simpa only [hq, map_one, one_mul] using hz

noncomputable def integralCoreAction (g : D →* baseNormalizer)
    (hg : Function.Surjective g) (hk : g.ker ≤ center D) :
    baseNormalizer →* MulAut (corePreimage g) :=
  g.liftOfSurjective hg ⟨MulAut.conjNormal, by
    intro d hd
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    change d * (a : D) * d⁻¹ = a
    rw [← mem_center_iff.mp (hk hd) (a : D), mul_inv_cancel_right]⟩

theorem integralCoreAction_apply (g : D →* baseNormalizer)
    (hg : Function.Surjective g) (hk : g.ker ≤ center D)
    (d : D) (a : corePreimage g) :
    (integralCoreAction g hg hk (g d) a : D) = d * a * d⁻¹ := by
  unfold integralCoreAction
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

noncomputable def integralCoreSection (g : D →* baseNormalizer)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype) :
    pCore 2 baseNormalizer →* corePreimage g :=
  s.codRestrict (corePreimage g) (fun q => by
    change g (s q) ∈ pCore 2 baseNormalizer
    rw [show g (s q) = q from DFunLike.congr_fun hs q]
    exact q.property)

noncomputable def sectionError (g : D →* baseNormalizer)
    (hg : Function.Surjective g) (hk : g.ker ≤ center D)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype)
    (n : baseNormalizer) : pCore 2 baseNormalizer →* center D := by
  let := corePreimage_commutative g hk s hs
  let σ := integralCoreSection g s hs
  let e : pCore 2 baseNormalizer →* corePreimage g :=
    ((integralCoreAction g hg hk n).toMonoidHom.comp σ) /
      (σ.comp (MulAut.conjNormal n).toMonoidHom)
  exact ((corePreimage g).subtype.comp e).codRestrict (center D) (fun q => by
    apply hk
    change g ((integralCoreAction g hg hk n (σ q) : D) /
      s (MulAut.conjNormal n q)) = 1
    rw [map_div]
    obtain ⟨d, rfl⟩ := hg n
    rw [integralCoreAction_apply]
    change g (d * s q * d⁻¹) / g (s (MulAut.conjNormal (g d) q)) = 1
    have hsec (v : pCore 2 baseNormalizer) : g (s v) = v := DFunLike.congr_fun hs v
    rw [map_mul, map_mul, map_inv, hsec, hsec]
    exact div_self' _)

theorem sectionError_apply (g : D →* baseNormalizer)
    (hg : Function.Surjective g) (hk : g.ker ≤ center D)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype)
    (d : D) (q : pCore 2 baseNormalizer) :
    (sectionError g hg hk s hs (g d) q : D) =
      d * s q * d⁻¹ / s (MulAut.conjNormal (g d) q) := by
  change (integralCoreAction g hg hk (g d) (integralCoreSection g s hs q) : D) /
      s (MulAut.conjNormal (g d) q) = _
  rw [integralCoreAction_apply]
  rfl

theorem sectionError_mul (g : D →* baseNormalizer)
    (hg : Function.Surjective g) (hk : g.ker ≤ center D)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype)
    (n m : baseNormalizer) (q : pCore 2 baseNormalizer) :
    sectionError g hg hk s hs (n * m) q =
      sectionError g hg hk s hs n (MulAut.conjNormal m q) *
        sectionError g hg hk s hs m q := by
  obtain ⟨d, rfl⟩ := hg n
  obtain ⟨e, rfl⟩ := hg m
  apply Subtype.ext
  change (sectionError g hg hk s hs (g d * g e) q : D) =
    (sectionError g hg hk s hs (g d) (MulAut.conjNormal (g e) q) : D) *
      (sectionError g hg hk s hs (g e) q : D)
  rw [← map_mul, sectionError_apply, sectionError_apply, sectionError_apply]
  have hact : MulAut.conjNormal (g (d * e)) q =
      MulAut.conjNormal (g d) (MulAut.conjNormal (g e) q) := by rw [map_mul, map_mul]; rfl
  rw [hact]
  let z : D := e * s q * e⁻¹ / s (MulAut.conjNormal (g e) q)
  have hcent : z ∈ center D := by
    simpa only [sectionError_apply] using (sectionError g hg hk s hs (g e) q).property
  have he : e * s q * e⁻¹ = z * s (MulAut.conjNormal (g e) q) := by
    exact (div_mul_cancel _ _).symm
  calc
    _ = d * (e * s q * e⁻¹) * d⁻¹ /
        s (MulAut.conjNormal (g d) (MulAut.conjNormal (g e) q)) := by group
    _ = d * (z * s (MulAut.conjNormal (g e) q)) * d⁻¹ /
        s (MulAut.conjNormal (g d) (MulAut.conjNormal (g e) q)) := by rw [he]
    _ = z * (d * s (MulAut.conjNormal (g e) q) * d⁻¹ /
        s (MulAut.conjNormal (g d) (MulAut.conjNormal (g e) q))) := by
      rw [← mul_assoc d z, mem_center_iff.mp hcent d]
      simp only [div_eq_mul_inv, mul_assoc]
    _ = _ := (mem_center_iff.mp hcent _).symm

theorem sectionError_core (g : D →* baseNormalizer)
    (hg : Function.Surjective g) (hk : g.ker ≤ center D)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype)
    (u : pCore 2 baseNormalizer) : sectionError g hg hk s hs u = 1 := by
  have hsec (v : pCore 2 baseNormalizer) : g (s v) = v := DFunLike.congr_fun hs v
  apply MonoidHom.ext
  intro q
  apply Subtype.ext
  change (sectionError g hg hk s hs u q : D) = 1
  rw [← hsec u, sectionError_apply, hsec]
  have hq : MulAut.conjNormal (u : baseNormalizer) q = q := by
    apply Subtype.ext
    change (u : baseNormalizer) * q * (u : baseNormalizer)⁻¹ = q
    exact congrArg Subtype.val (show u * q * u⁻¹ = q by rw [mul_comm u q, mul_inv_cancel_right])
  rw [hq, ← map_mul, ← map_inv, ← map_mul, mul_comm u q, mul_inv_cancel_right, div_self']

/-- The central kernel, with its inherited commutative group structure. -/
@[expose] def integralKernel (g : D →* baseNormalizer) : Subgroup (center D) :=
  g.ker.comap (center D).subtype

@[expose] def integralKernelInclusion (g : D →* baseNormalizer) : integralKernel g →* D :=
  (center D).subtype.comp (integralKernel g).subtype

noncomputable def kernelSectionError (g : D →* baseNormalizer)
    (hg : Function.Surjective g) (hk : g.ker ≤ center D)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype)
    (n : baseNormalizer) : pCore 2 baseNormalizer →* integralKernel g :=
  (sectionError g hg hk s hs n).codRestrict (integralKernel g) (fun q => by
    change g (sectionError g hg hk s hs n q : D) = 1
    obtain ⟨d, rfl⟩ := hg n
    rw [sectionError_apply, map_div, map_mul, map_mul, map_inv]
    have hsec (v : pCore 2 baseNormalizer) : g (s v) = v := DFunLike.congr_fun hs v
    rw [hsec, hsec]
    exact div_self' _)

noncomputable def sectionCrossedHom (g : D →* baseNormalizer)
    (hg : Function.Surjective g) (hk : g.ker ≤ center D)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype) : CoreCrossedHom (integralKernel g) where
  toFun := kernelSectionError g hg hk s hs
  mul_rule n m q := Subtype.ext (sectionError_mul g hg hk s hs n m q)
  core_rule u := by
    apply MonoidHom.ext
    intro q
    apply Subtype.ext
    change sectionError g hg hk s hs u q = 1
    rw [sectionError_core]
    rfl

/-- Correcting by a homomorphism into the central kernel preserves a core section. -/
noncomputable def correctedSection (g : D →* baseNormalizer)
    (s : pCore 2 baseNormalizer →* D) (t : pCore 2 baseNormalizer →* integralKernel g) :
    pCore 2 baseNormalizer →* D where
  toFun q := integralKernelInclusion g (t q) * s q
  map_one' := by simp only [map_one, mul_one]
  map_mul' x y := by
    simp only [map_mul]
    have hc : integralKernelInclusion g (t y) * s x =
        s x * integralKernelInclusion g (t y) :=
      (mem_center_iff.mp (t y).val.property (s x)).symm
    rw [mul_assoc, ← mul_assoc _ (s x), hc]
    simp only [mul_assoc]

theorem correctedSection_comp (g : D →* baseNormalizer)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype)
    (t : pCore 2 baseNormalizer →* integralKernel g) :
    g.comp (correctedSection g s t) = (pCore 2 baseNormalizer).subtype := by
  apply MonoidHom.ext
  intro q
  change g (integralKernelInclusion g (t q) * s q) = q
  rw [map_mul, show g (integralKernelInclusion g (t q)) = 1 from (t q).property,
    one_mul]
  exact DFunLike.congr_fun hs q

theorem correctedSection_error (g : D →* baseNormalizer)
    (hg : Function.Surjective g) (hk : g.ker ≤ center D)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype)
    (t : pCore 2 baseNormalizer →* integralKernel g)
    (d : D) (q : pCore 2 baseNormalizer) :
    d * correctedSection g s t q * d⁻¹ /
        correctedSection g s t (MulAut.conjNormal (g d) q) =
      integralKernelInclusion g ((sectionCrossedHom g hg hk s hs).toFun (g d) q *
        t q / t (MulAut.conjNormal (g d) q)) := by
  rw [map_div, map_mul]
  have herr : integralKernelInclusion g ((sectionCrossedHom g hg hk s hs).toFun (g d) q) =
      d * s q * d⁻¹ / s (MulAut.conjNormal (g d) q) := sectionError_apply g hg hk s hs d q
  rw [herr]
  change d * (integralKernelInclusion g (t q) * s q) * d⁻¹ /
      (integralKernelInclusion g (t (MulAut.conjNormal (g d) q)) *
        s (MulAut.conjNormal (g d) q)) = _
  have hz := (t q).val.property
  change integralKernelInclusion g (t q) ∈ center D at hz
  calc
    _ = integralKernelInclusion g (t q) *
        (d * s q * d⁻¹ / s (MulAut.conjNormal (g d) q)) /
          integralKernelInclusion g (t (MulAut.conjNormal (g d) q)) := by
      rw [← mul_assoc d, mem_center_iff.mp hz d]
      simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
    _ = _ := by rw [mem_center_iff.mp hz _]

/-- The integral crossed-homomorphism calculation applies to the actual
core preimage and its given section, without an invariant section or an
exponent-two assumption on the original kernel. -/
theorem card_coreDisplacements_inf_ker_le_of_cyclic_error [Finite D]
    (g : D →* baseNormalizer) (hg : Function.Surjective g) (hk : g.ker ≤ center D)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype)
    (hnorm : (sectionCrossedHom g hg hk s hs).HasCyclicError) :
    Nat.card (coreDisplacements g ⊓ g.ker : Subgroup D) ≤ 2 := by
  obtain ⟨t, z, hz, herr⟩ := hnorm
  let Z : Subgroup D := zpowers (integralKernelInclusion g z)
  have hZ : Z ≤ g.ker := zpowers_le.mpr z.property
  have hle : coreDisplacements g ⊓ g.ker ≤ Z :=
    coreDisplacements_inf_ker_le_of_section_errors g hk (correctedSection g s t)
      (correctedSection_comp g s hs t) Z hZ (by
        intro d q
        rw [correctedSection_error g hg hk s hs t d q]
        have he : integralKernelInclusion g
            ((sectionCrossedHom g hg hk s hs).toFun (g d) q *
              t q / t (MulAut.conjNormal (g d) q)) ∈
            (zpowers z).map (integralKernelInclusion g) :=
          Subgroup.mem_map.mpr ⟨_, herr (g d) q, rfl⟩
        rw [MonoidHom.map_zpowers] at he
        exact he)
  have hzD : integralKernelInclusion g z ^ 2 = 1 := by rw [← map_pow, hz, map_one]
  exact (Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)).trans
    ((Nat.card_zpowers _).le.trans (orderOf_le_of_pow_eq_one (by decide) hzD))

/-- For a finite central cover of the literal HS normalizer with a section over
its two-core, the central kernel of the core displacement subgroup has order
at most two. The concrete action certificate discharges every action,
generation and quotient-relation premise of integral normalization. -/
theorem card_coreDisplacements_inf_ker_le [Finite D]
    (g : D →* baseNormalizer) (hg : Function.Surjective g) (hk : g.ker ≤ center D)
    (s : pCore 2 baseNormalizer →* D)
    (hs : g.comp s = (pCore 2 baseNormalizer).subtype) :
    Nat.card (coreDisplacements g ⊓ g.ker : Subgroup D) ≤ 2 :=
  card_coreDisplacements_inf_ker_le_of_cyclic_error g hg hk s hs
    (CoreCrossedHom.hasCyclicError integralActionData (sectionCrossedHom g hg hk s hs))

end Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.NormalizerBound
