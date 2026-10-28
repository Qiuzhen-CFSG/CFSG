module

public import Theory.Representation.RegularCyclicNormalClosure.Regular
public import Theory.Representation.RegularCyclicNormalClosure.Seed
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# The commuting branch of the local factor construction

Regularity and normality in the fixed-space stabilizer imply that distinct
conjugates of the cyclic subgroup have trivial intersection. This is a
statement about the actor subgroups, not a TI assertion about their fixed
spaces.

If two distinct conjugates commute, each fixes the other's moved space.
Indeed, regularity makes the intersection of one moved space with the
other fixed space either zero or the whole moved space. In the zero case,
dimension equality and commutation identify the two moved spaces and then
the fixed spaces, contradicting distinctness of the conjugates. Thus C
itself supplies `FactorSeed` when it commutes with all its conjugates.

These are elementary deductions from the module setup in Aschbacher–Smith,
E.6.24, printed p.255 (PDF p.266). The general nonnormal existence theorem,
including the order-21 branch, is not proved here. That theorem cites
Aschbacher, *Weak closure in finite groups of even characteristic*,
J. Algebra 70 (1981), 10.4, DOI 10.1016/0021-8693(81)90236-2. Its hypotheses
and noncommuting argument still require verification against that article;
GLS, volume 2, C.14.2 has an additional TI fixed-space hypothesis.
-/

public section

open Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
namespace FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) A W)

private theorem fixedSpace_conjugate (C : Subgroup A) (a : A) :
    fixedSpace ρ (C.map (MulAut.conj a).toMonoidHom) =
      (fixedSpace ρ C).map (ρ a) := by
  apply le_antisymm
  · intro v hv
    refine ⟨ρ a⁻¹ v, ?_, ?_⟩
    · intro c
      have hh := hv ⟨a * (c : A) * a⁻¹, c, c.property, rfl⟩
      change ρ (a * (c : A) * a⁻¹) v = v at hh
      have hh' := congrArg (ρ a⁻¹) hh
      change ρ (c : A) (ρ a⁻¹ v) = ρ a⁻¹ v
      simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel_left] using hh'
    · simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
  · rintro _ ⟨v, hv, rfl⟩ b
    obtain ⟨c, hc, he⟩ := b.property
    change ρ (b : A) (ρ a v) = ρ a v
    rw [← he]
    change ρ (a * c * a⁻¹) (ρ a v) = ρ a v
    calc
      _ = ρ a (ρ c v) := by
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
      _ = ρ a v := congrArg (ρ a) (hv ⟨c, hc⟩)

private theorem action_injective (a : A) : Function.Injective (ρ a) := by
  intro v w he
  have hh := congrArg (ρ a⁻¹) he
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using hh

private theorem moved_finrank_conjugate (C : Subgroup A) (a : A) :
    Module.finrank (ZMod 2) (displacementSpan ρ (C.map (MulAut.conj a).toMonoidHom) ⊤) =
      Module.finrank (ZMod 2) (displacementSpan ρ C ⊤) := by
  have he := displacementSpan_conjugate ρ C ⊤ a
  rw [map_top_action ρ a] at he
  rw [he]
  exact (Submodule.equivMapOfInjective (ρ a) (action_injective ρ a)
    (displacementSpan ρ C ⊤)).finrank_eq.symm

end FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- A common nonidentity element forces two conjugates of the cyclic actor
 to coincide, because it identifies their fixed spaces. -/
theorem Input.conjugate_eq_of_common_ne_one (h : Input ρ C) (a : A)
    {c : A} (hc : c ∈ C) (hca : c ∈ C.map (MulAut.conj a).toMonoidHom)
    (hne : c ≠ 1) : C.map (MulAut.conj a).toMonoidHom = C := by
  obtain ⟨d, hd, he⟩ := hca
  have hdn : d ≠ 1 := by
    intro hd1
    subst d
    exact hne (he.symm.trans (map_one _))
  apply h.normal_in_stabilizer
  calc
    (fixedSpace ρ C).map (ρ a) = (fixedSpace ρ (zpowers d)).map (ρ a) :=
      congrArg (fun S : Submodule (ZMod 2) W => S.map (ρ a))
        (h.fixedSpace_zpowers hd hdn).symm
    _ = fixedSpace ρ ((zpowers d).map (MulAut.conj a).toMonoidHom) :=
      (FactorConstruction.fixedSpace_conjugate ρ (zpowers d) a).symm
    _ = fixedSpace ρ (zpowers c) := by rw [MonoidHom.map_zpowers, he]
    _ = fixedSpace ρ C := h.fixedSpace_zpowers hc hne

/-- Distinct conjugates of the cyclic actor intersect trivially. No TI
 hypothesis about the fixed spaces is used or asserted. -/
theorem Input.disjoint_conjugate_of_ne (h : Input ρ C) (a : A)
    (hne : C.map (MulAut.conj a).toMonoidHom ≠ C) :
    Disjoint C (C.map (MulAut.conj a).toMonoidHom) := by
  apply Subgroup.disjoint_def.mpr
  intro c hc hca
  by_contra hcn
  exact hne (h.conjugate_eq_of_common_ne_one a hc hca hcn)

/-- Commuting distinct conjugates fix one another's moved spaces. -/
theorem Input.cross_fixed_of_commuting_conjugate [FiniteDimensional (ZMod 2) W]
    (h : Input ρ C) (a : A)
    (hne : C.map (MulAut.conj a).toMonoidHom ≠ C)
    (hcomm : ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d) :
    ∀ c ∈ C, ∀ v ∈ displacementSpan ρ (C.map (MulAut.conj a).toMonoidHom) ⊤,
      ρ c v = v := by
  let D := C.map (MulAut.conj a).toMonoidHom
  let S := displacementSpan ρ C ⊤
  have commute_action (c : C) (d : D) (v : W) :
      ρ c (ρ d v) = ρ d (ρ c v) := by
    simp only [← Module.End.mul_apply, ← map_mul]
    rw [(hcomm c c.property d d.property).eq]
  have d_preserves_moved (d : D) {v : W} (hv : v ∈ S) : ρ d v ∈ S := by
    have hd : (d : A) ∈ normalizer (C : Set A) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr
        (fun c hc => (hcomm c hc d d.property).eq))
    have hm := Submodule.mem_map_of_mem (f := ρ d) hv
    change ρ d v ∈ displacementSpan ρ C ⊤
    rwa [displacementSpan_map_of_normalized ρ C d
      (mem_normalizer_iff_map_conj_eq.mp hd)] at hm
  have d_preserves_fixed (d : D) {v : W} (hv : v ∈ fixedSpace ρ C) :
      ρ d v ∈ fixedSpace ρ C := by
    intro c
    change ρ (c : A) (ρ (d : A) v) = ρ (d : A) v
    rw [commute_action c d, (show ρ (c : A) v = v from hv c)]
  have hex : ∃ v ∈ S, v ∈ fixedSpace ρ D ∧ v ≠ 0 := by
    by_contra hn
    have hdis : Disjoint (fixedSpace ρ D) S := by
      apply Submodule.disjoint_def.mpr
      intro v hvD hvS
      by_contra hvn
      exact hn ⟨v, hvS, hvD, hvn⟩
    have hdim : Module.finrank (ZMod 2) (fixedSpace ρ C) +
        Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) W :=
      Submodule.finrank_add_eq_of_isCompl h.split
    have hfixed : Module.finrank (ZMod 2) (fixedSpace ρ C) =
        Module.finrank (ZMod 2) (fixedSpace ρ D) :=
      (fixedSpaceConjEquiv ρ C a).finrank_eq
    have hspan : fixedSpace ρ D ⊔ S = ⊤ :=
      Submodule.eq_top_of_disjoint _ _ (by omega) hdis
    have hmle : displacementSpan ρ D ⊤ ≤ S := by
      apply Submodule.span_le.mpr
      rintro _ ⟨d, hd, v, _, rfl⟩
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
        (show v ∈ fixedSpace ρ D ⊔ S by rw [hspan]; trivial)
      have he : ρ d (u + w) - (u + w) = ρ d w - w := by
        rw [map_add, (show ρ d u = u from hu ⟨d, hd⟩)]
        abel
      rw [he]
      exact S.sub_mem (d_preserves_moved ⟨d, hd⟩ hw) hw
    have hm : displacementSpan ρ D ⊤ = S :=
      Submodule.eq_of_le_of_finrank_eq hmle (FactorConstruction.moved_finrank_conjugate ρ C a)
    have hf_le : fixedSpace ρ C ≤ fixedSpace ρ D := by
      intro v hv d
      have hdiffS : ρ d v - v ∈ S := by
        rw [← hm]
        exact Submodule.subset_span ⟨d, d.property, v, Submodule.mem_top, rfl⟩
      have hdiffF : ρ d v - v ∈ fixedSpace ρ C :=
        (fixedSpace ρ C).sub_mem (d_preserves_fixed d hv) hv
      exact sub_eq_zero.mp (Submodule.disjoint_def.mp h.split.disjoint _ hdiffF hdiffS)
    have hf : fixedSpace ρ C = fixedSpace ρ D :=
      Submodule.eq_of_le_of_finrank_eq hf_le hfixed
    apply hne
    apply h.normal_in_stabilizer
    exact (FactorConstruction.fixedSpace_conjugate ρ C a).symm.trans hf.symm
  obtain ⟨u, huS, huD, hun⟩ := hex
  have hfix : ∀ d : D, ∀ v ∈ S, ρ d v = v := by
    intro d v hv
    by_cases hvn : v = 0
    · simp [hvn]
    obtain ⟨c, hc, _⟩ := h.regular u huS hun v hv hvn
    rw [← hc, ← commute_action c d, (show ρ (d : A) u = u from huD d)]
  intro c hc v hv
  apply Submodule.span_induction (p := fun v _ => ρ c v = v) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨d, hd, w, _, rfl⟩
    have he := hfix ⟨d, hd⟩ (ρ c w - w)
      (Submodule.subset_span ⟨c, hc, w, Submodule.mem_top, rfl⟩)
    change ρ d (ρ c w - w) = ρ c w - w at he
    rw [map_sub, sub_eq_iff_eq_add] at he
    rw [map_sub, commute_action ⟨c, hc⟩ ⟨d, hd⟩, he]
    abel
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy]
  · intro r x _ hx
    rw [map_smul, hx]

/-- The cyclic subgroup itself is a factor when it commutes with all its
 conjugates. The general existence theorem must still establish this
 condition or construct the exceptional nonabelian factor. -/
theorem Input.factorSeed_of_commuting_conjugates [FiniteDimensional (ZMod 2) W]
    (h : Input ρ C)
    (hcomm : ∀ a : A, ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom,
      Commute c d) : FactorSeed ρ C C where
  contained := le_rfl
  in_normalClosure := le_normalClosure
  split := h.split
  cross_fixed := fun a ha => h.cross_fixed_of_commuting_conjugate a ha (hcomm a)
  alternatives := Or.inl rfl

end Representation.RegularCyclicNormalClosure
