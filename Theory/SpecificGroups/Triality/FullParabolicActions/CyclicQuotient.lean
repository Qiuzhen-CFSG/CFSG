module

public import Theory.SpecificGroups.Triality.ParabolicLocalStructure

/-!
# Cyclic residual quotients of the full triality parabolics

The full parabolic is the product of its prime-to-two residual and the
original torus. The torus has one extension-field and one fixed-field unit
coordinate. Its folded subsystem coroot words belong to the genuine Levi,
hence to the residual. Killing that coordinate leaves a surjection from
the other field's cyclic unit group onto the parabolic quotient.

For the arms node the surviving field is GF(q); for the central node it is
GF(q³). The elementary lifts and quotient by the elementary group's own
center are retained throughout. No perfectness assertion is used, so the
proof includes q = 2.

Source: GLS3 §2.4 and Theorem 2.6.5(f,g)
(`refs/KGroup/GLS3/chapter2.tex`); the parabolics in Aschbacher–Smith
F.1.12(I)(4), printed pp.263–264 (`refs/quasithin.pdf`).
-/

public section
noncomputable section
namespace Triality.Standard.Parabolics
open ConcreteBruhat ConcreteBruhat.TorusCoordinates RadicalCoordinates

theorem parabolic_eq_localFactor_sup_torus (P : Parameters) (hp : P.prime = 2) (a : Node) :
    parabolic P a = localFactor P a ⊔ torus P := by
  rw [localFactor_eq_root_sup_levi P hp a, sup_assoc]
  exact parabolic_eq_root_sup_levi_sup_torus P hp a

private def torusToQuotient (P : Parameters) (hp : P.prime = 2) (a : Node) :
    OrbitParameters P →* parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a) :=
  (QuotientGroup.mk' _).comp ((Subgroup.inclusion
    ((torus_le_borel P).trans (borel_le_parabolic P a))).comp
      (torusMulEquiv P hp).toMonoidHom)

private theorem torusToQuotient_surjective (P : Parameters) (hp : P.prime = 2) (a : Node) :
    Function.Surjective (torusToQuotient P hp a) := by
  intro z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    ((localFactor P a).subgroupOf (parabolic P a)) z
  have htop : (localFactor P a).subgroupOf (parabolic P a) ⊔
      (torus P).subgroupOf (parabolic P a) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (localFactor_le_parabolic P a)
      ((torus_le_borel P).trans (borel_le_parabolic P a)),
      ← parabolic_eq_localFactor_sup_torus P hp a, Subgroup.subgroupOf_self]
  obtain ⟨l, hl, t, ht, hlt⟩ := Subgroup.mem_sup_of_normal_left.mp
    (htop.symm ▸ Subgroup.mem_top g)
  change t.val ∈ torus P at ht
  have hlq : QuotientGroup.mk' ((localFactor P a).subgroupOf (parabolic P a)) l = 1 :=
    (QuotientGroup.eq_one_iff l).mpr hl
  refine ⟨(torusMulEquiv P hp).symm ⟨t.val, ht⟩, ?_⟩
  change QuotientGroup.mk' _ (Subgroup.inclusion
    ((torus_le_borel P).trans (borel_le_parabolic P a))
    (torusMulEquiv P hp ((torusMulEquiv P hp).symm ⟨t.val, ht⟩))) = _
  rw [MulEquiv.apply_symm_apply, ← hlt, map_mul, hlq, one_mul]
  rfl

private theorem torusToQuotient_kills_arms (P : Parameters) (hp : P.prime = 2)
    (t : (ExtensionField P)ˣ) : torusToQuotient P hp .arms (t, 1) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  change (torusMulEquiv P hp (t, 1)).val ∈ localFactor P .arms
  rw [torusMulEquiv_val]
  have hone : foldedTorusElementary P hp .central 1 = 1 := by
    apply LeviCommutators.elementaryInclusion_injective P
    exact (inclusion_foldedTorus_central P hp 1).trans
      ((congrArg (torusWord P 1) (map_one (fixedUnit P))).trans
        ((torusWord_one P hp 1).trans (map_one (elementaryInclusion P)).symm))
  change toCarrier P (foldedTorusElementary P hp .arms t *
    foldedTorusElementary P hp .central 1) ∈ localFactor P .arms
  simp only [hone, mul_one]
  exact levi_le_localFactor P hp .arms (LeviCommutators.torusActor_mem_levi P hp .arms t)


private theorem torusToQuotient_kills_central (P : Parameters) (hp : P.prime = 2)
    (t : (fixedField P)ˣ) : torusToQuotient P hp .central (1, t) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  change (torusMulEquiv P hp (1, t)).val ∈ localFactor P .central
  rw [torusMulEquiv_val]
  have hone : foldedTorusElementary P hp .arms 1 = 1 := by
    apply LeviCommutators.elementaryInclusion_injective P
    apply (inclusion_foldedTorus_arms P hp 1).trans
    apply Eq.trans ?_ (map_one (elementaryInclusion P)).symm
    have hf := map_one (frobenius P)
    have hff := (congrArg (frobenius P) hf).trans hf
    have h0 := torusWord_one P hp 0
    have h2 := (congrArg (torusWord P 2) hf).trans (torusWord_one P hp 2)
    have h3 := (congrArg (torusWord P 3) hff).trans (torusWord_one P hp 3)
    exact (congrArg₂ (· * ·) (congrArg₂ (· * ·) h0 h2) h3).trans (by simp only [one_mul])
  change toCarrier P (foldedTorusElementary P hp .arms 1 *
    foldedTorusElementary P hp .central t) ∈ localFactor P .central
  simp only [hone, one_mul]
  exact levi_le_localFactor P hp .central
    (LeviCommutators.torusActor_mem_levi P hp .central t)

theorem parabolic_quotient_isCyclic (P : Parameters) (hp : P.prime = 2) (a : Node) :
    IsCyclic (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) := by
  cases a with
  | arms =>
    apply isCyclic_of_surjective ((torusToQuotient P hp .arms).comp
      (MonoidHom.inr (ExtensionField P)ˣ (fixedField P)ˣ))
    intro z
    obtain ⟨⟨s, t⟩, rfl⟩ := torusToQuotient_surjective P hp .arms z
    refine ⟨t, ?_⟩
    change torusToQuotient P hp .arms (1, t) = torusToQuotient P hp .arms (s, t)
    rw [show (s, t) = (s, 1) * (1, t) by simp, map_mul,
      torusToQuotient_kills_arms, one_mul]
  | central =>
    apply isCyclic_of_surjective ((torusToQuotient P hp .central).comp
      (MonoidHom.inl (ExtensionField P)ˣ (fixedField P)ˣ))
    intro z
    obtain ⟨⟨s, t⟩, rfl⟩ := torusToQuotient_surjective P hp .central z
    refine ⟨s, ?_⟩
    change torusToQuotient P hp .central (s, 1) = torusToQuotient P hp .central (s, t)
    rw [show (s, t) = (s, 1) * (1, t) by simp, map_mul,
      torusToQuotient_kills_central, mul_one]

/-- Both full-parabolic residual quotients are cyclic at every positive binary exponent. -/
theorem parabolic_quotient_isCyclic_binary (f : ℕ) (hf : 0 < f) (a : Node) :
    IsCyclic (parabolic (binaryParameters f hf) a ⧸
      (localFactor (binaryParameters f hf) a).subgroupOf
        (parabolic (binaryParameters f hf) a)) :=
  parabolic_quotient_isCyclic _ rfl a

end Triality.Standard.Parabolics
