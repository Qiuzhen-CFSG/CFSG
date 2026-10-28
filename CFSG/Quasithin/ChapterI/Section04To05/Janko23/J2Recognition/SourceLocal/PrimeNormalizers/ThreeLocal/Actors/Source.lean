module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Actors
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Recognition.Inputs

/-!
# The source A₅ complement and inverting involution

Choose a five-subgroup in the selected root-involution centralizer of 47.1.
The marked product normalizer from 47.2 embeds its A₅ factor in the
centralizer of a conjugate of z. Conjugating back gives an actual A₅ in
C_G(z), hence an internal complement and an involution inverting the seed X.

Only the exact earlier conclusions in `EarlierConclusions` are used for
these constructions. Their producers remain `qt-i47-j2-source-involutions`
and `qt-i47-j2-five-local-calculation`. The order-eight reduction retains
its separate, explicit finite core-norm premise.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1–47.2, pp.259–261,
and the local-normalizer step in the proof of 47.3, p.262.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

namespace EarlierConclusions

/-- The actual A₅ component from 47.2, conjugated into the marked C_G(z). -/
theorem exists_alternating_embedding (E : EarlierConclusions D) :
    ∃ f : alternatingGroup (Fin 5) →* involutionCentralizer D.z,
      Function.Injective f := by
  have ht : 5 ^ (Nat.card (involutionCentralizer E.geometry.t)).factorization 5 = 5 := by
    rw [E.geometry.model.centralizer_card]
    decide +kernel
  obtain ⟨F, hF, hFt⟩ := FiveLocal.exists_fiveCentralizing E.geometry.t ht
  obtain ⟨W⟩ := E.five.root F ⟨hF, E.geometry.t, IsConj.refl _, hFt⟩
  let b : DihedralGroup 5 × alternatingGroup (Fin 5) →* G :=
    (normalizer (F : Set G)).subtype.comp W.equiv.symm.toMonoidHom
  have hb : Function.Injective b :=
    (normalizer (F : Set G)).subtype_injective.comp W.equiv.symm.injective
  let j : alternatingGroup (Fin 5) →* G := b.comp (MonoidHom.inr _ _)
  have hj : Function.Injective j := by
    intro x y h
    exact congrArg Prod.snd (hb h)
  have hjC (x : alternatingGroup (Fin 5)) : j x ∈ involutionCentralizer W.inverter := by
    apply W.component_le
    rw [← W.component_factor]
    exact ⟨(1, x), ⟨rfl, mem_top _⟩, rfl⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp W.inverter_conj
  let a : G ≃* G := MulAut.conj g
  have ha : a D.z = W.inverter := hg
  let k := a.symm.toMonoidHom.comp j
  have hk (x : alternatingGroup (Fin 5)) : k x ∈ involutionCentralizer D.z := by
    apply mem_centralizer_singleton_iff.mpr
    apply a.injective
    change a (a.symm (j x) * D.z) = a (D.z * a.symm (j x))
    rw [map_mul, map_mul, a.apply_symm_apply, ha]
    exact mem_centralizer_singleton_iff.mp (hjC x)
  let f := k.codRestrict (involutionCentralizer D.z) hk
  refine ⟨f, ?_⟩
  intro x y h
  apply hj
  exact a.symm.injective (congrArg Subtype.val h)

/-- The earlier source geometry supplies an actual internal A₅ complement. -/
theorem exists_alternating_complement (E : EarlierConclusions D) :
    ∃ A : Subgroup (involutionCentralizer D.z),
      Nonempty (A ≃* alternatingGroup (Fin 5)) ∧ A.IsComplement' (localCore D.z) := by
  obtain ⟨f, hf⟩ := E.exists_alternating_embedding
  exact ⟨f.range, ⟨(MonoidHom.ofInjective hf).symm⟩, alternating_complement D f hf⟩

/-- The order-two inverter in the literal normalizer, with no 47.3 premise. -/
theorem exists_inverter (E : EarlierConclusions D) :
    ∃ m : M D, orderOf m = 2 ∧
      ∀ x : D.X, (m : G) * x * (m : G)⁻¹ = (x : G)⁻¹ := by
  obtain ⟨f, hf⟩ := E.exists_alternating_embedding
  apply inverter_of_alternating_embedding D ((involutionCentralizer D.z).subtype.comp f)
    ((involutionCentralizer D.z).subtype_injective.comp hf)
  rintro _ ⟨x, rfl⟩
  exact (f x).property

/-- Both actors follow from earlier source geometry and the explicit finite
norm calculation. Only the latter premise remains to be discharged here. -/
theorem actors_of_core_norm (E : EarlierConclusions D)
    (hnorm : ∀ φ : alternatingGroup (Fin 5) →* MulAut MinusExtraspecial.Model,
      Function.Injective φ → ∀ x r : alternatingGroup (Fin 5),
      orderOf x = 3 → orderOf r = 2 → r * x * r⁻¹ = x⁻¹ →
      ∃ q : MinusExtraspecial.Model,
        φ x q = q ∧ orderOf (q * φ r q) = 4) :
    (∃ m : M D, orderOf m = 2 ∧
      ∀ x : D.X, (m : G) * x * (m : G)⁻¹ = (x : G)⁻¹) ∧
    (∃ s : M D, orderOf s = 8) := by
  obtain ⟨f, hf⟩ := E.exists_alternating_embedding
  exact ⟨E.exists_inverter, eight_of_core_norm D f hf
    (centralizer_generalizedFitting_le _) hnorm⟩

end EarlierConclusions
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
