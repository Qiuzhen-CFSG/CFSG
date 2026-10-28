module
public import Theory.Representation.NormalComponentConstituents.Orthogonal
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.Geometry

/-!
# Duality and faithfulness of a spanning exchanged pair

A totally isotropic irreducible subspace pairs perfectly with its conjugate
when the two span a nondegenerate ambient representation. The reverse
pairing transfers equality of actions to the second summand, so ambient
faithfulness gives faithfulness on the first. Homogeneous selection excludes
isomorphic moved translates, hence excludes self-duality of either member.

The quotient comparison uses the literal map by the fixed space, and the
conjugate representation uses the repository's inverse-action convention.
The terminal central-kernel branch applies these results after proving
properness and excluding the nondegenerate constituent alternative.

Source: Aschbacher--Smith G.10.15(2)(II), printed pp.362--363.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

private def quotientImageEquivOfFixedSpaceEqBot (H : Subgroup G)
    (hfix : fixedSpace ρ H = ⊥) (I : Submodule (ZMod 2) V)
    (hI : H ≤ subspaceStabilizer ρ I) :
    (invariantSubspace ρ H I hI).toRepresentation.Equiv
      (Homogeneous.quotientImage ρ H I hI).toRepresentation := by
  let q := (fixedSpace ρ H).mkQ
  have hq : Function.Injective q := LinearMap.ker_eq_bot.mp
    ((Submodule.ker_mkQ _).trans hfix)
  exact .mk (Submodule.equivMapOfInjective q hq I) (fun _ => by ext; rfl)

/-- Homogeneous selection excludes an equivariant identification with a
moved translate, on the original subspaces rather than only their quotients. -/
theorem Homogeneous.IsIrrPlusWith.not_equiv_moved
    {H X : Subgroup G} [H.Normal] {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ H X I) (hfix : fixedSpace ρ H = ⊥)
    (x : X) (hx : I.map (ρ (x : G)⁻¹) ≠ I) :
    ¬ Nonempty (Representation.Equiv
      (invariantSubspace ρ H I hI.invariant).toRepresentation
      (conjugateSubrepresentation ρ H (invariantSubspace ρ H I hI.invariant)
        (x : G)).toRepresentation) := by
  rintro ⟨e⟩
  let J := I.map (ρ (x : G)⁻¹)
  have hJ := (hI.isIrrPlus.map_normalizer ρ (hI.normalizes x⁻¹.property)).choose
  let qI := quotientImageEquivOfFixedSpaceEqBot ρ H hfix I hI.invariant
  let qJ := quotientImageEquivOfFixedSpaceEqBot ρ H hfix J hJ
  have eqJ : conjugateSubrepresentation ρ H
      (invariantSubspace ρ H I hI.invariant) (x : G) = invariantSubspace ρ H J hJ := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  rw [eqJ] at e
  let eq := (qI.symm.trans e).trans qJ
  have he : Homogeneous.SameModule
      (Homogeneous.quotientImage ρ H I hI.invariant)
      (Homogeneous.quotientImage ρ H J hJ) :=
    ⟨eq.toLinearEquiv, fun a w => LinearMap.congr_fun (eq.isIntertwining' a) w⟩
  exact hx (hI.eq_of_isomorphic_conjugate ρ x⁻¹ he)

variable [FiniteDimensional (ZMod 2) V]

/-- An isotropic constituent and a spanning conjugate pair perfectly as
representations of the same normal subgroup. -/
theorem isotropic_spanning_conjugate_dual
    (B : LinearMap.BilinForm (ZMod 2) V) (hnd : B.Nondegenerate)
    (hpres : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (H : Subgroup G) [H.Normal] (I : Submodule (ZMod 2) V)
    (hI : H ≤ subspaceStabilizer ρ I)
    (hi : IsIrreducible (invariantSubspace ρ H I hI).toRepresentation)
    (hiso : ∀ u ∈ I, ∀ w ∈ I, B u w = 0) (x : G)
    (hspan : I ⊔ I.map (ρ x⁻¹) = ⊤) :
    Nonempty (Representation.Equiv (invariantSubspace ρ H I hI).toRepresentation
      (conjugateSubrepresentation ρ H (invariantSubspace ρ H I hI) x).toRepresentation.dual) := by
  let R := invariantSubspace ρ H I hI
  let J := conjugateSubrepresentation ρ H R x
  have hne : ∃ u ∈ I, ∃ w ∈ J.toSubmodule, B u w ≠ 0 := by
    by_contra! hz
    have hbot : I = ⊥ := by
      apply bot_unique
      intro u hu
      apply hnd.1 u
      intro w
      have hw : w ∈ I ⊔ I.map (ρ x⁻¹) := hspan.symm ▸ Submodule.mem_top
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add, hiso u hu a ha, hz u hu b hb, add_zero]
    exact ((Subrepresentation.irreducible_iff_isAtom R).mp hi).ne_bot
      (Subrepresentation.toSubmodule_injective hbot)
  let f := bilinearCrossPairing (ρ.comp H.subtype) B
    (fun h u w => hpres h u w) R J
  have hinj : Function.Injective f := bilinearCrossPairing_injective
    (ρ.comp H.subtype) B (fun h u w => hpres h u w) R J hi hne
  have hdim : finrank (ZMod 2) R.toSubmodule = finrank (ZMod 2) J.toSubmodule :=
    (finrank_map_action ρ I x⁻¹).symm
  exact ⟨f.ofBijective ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using hdim)).mp hinj⟩⟩

omit [FiniteDimensional (ZMod 2) V] in
/-- A faithful action on a spanning dual pair is faithful on either member. -/
theorem faithful_of_spanning_dual_pair
    (hf : Function.Injective ρ) (H : Subgroup G) [H.Normal]
    (I : Submodule (ZMod 2) V) (hI : H ≤ subspaceStabilizer ρ I) (x : G)
    (hspan : I ⊔ I.map (ρ x⁻¹) = ⊤)
    (e : Representation.Equiv
      (conjugateSubrepresentation ρ H (invariantSubspace ρ H I hI) x).toRepresentation
      (invariantSubspace ρ H I hI).toRepresentation.dual) :
    Function.Injective (invariantSubspace ρ H I hI).toRepresentation.asGroupHom := by
  let R := invariantSubspace ρ H I hI
  let J := conjugateSubrepresentation ρ H R x
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  have hai : R.toRepresentation a⁻¹ = 1 := by
    have he : R.toRepresentation.asGroupHom a⁻¹ = 1 := by rw [map_inv,ha,inv_one]
    exact congrArg Units.val he
  have haj (w : J.toSubmodule) : J.toRepresentation a w = w := by
    apply e.injective
    have he := LinearMap.congr_fun (e.isIntertwining' a) w
    change e (J.toRepresentation a w) = R.toRepresentation.dual a (e w) at he
    change e (J.toRepresentation a w) = e w
    rw [he]
    ext f
    change (e w) (R.toRepresentation a⁻¹ f) = (e w) f
    rw [hai, Module.End.one_apply]
  have hfix : ∀ w : V, ρ (a : G) w = w := by
    intro w
    have hw : w ∈ I ⊔ I.map (ρ x⁻¹) := hspan.symm ▸ Submodule.mem_top
    obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add]
    have hu' : ρ (a : G) u = u := congrArg (fun f => (f.val (⟨u,hu⟩ : I) : V)) ha
    have hz' : ρ (a : G) z = z := congrArg Subtype.val (haj ⟨z,hz⟩)
    rw [hu',hz']
  apply Subtype.ext
  apply hf
  ext w
  simpa only [Subgroup.coe_one, map_one, Module.End.one_apply] using hfix w

/-- An isotropic spanning orbit of two inequivalent constituents has faithful,
non-self-dual constituent action and duality with every moved orbit member. -/
theorem Homogeneous.IsIrrPlusWith.faithful_dual_of_isotropic_pair
    (hf : Function.Injective ρ)
    (B : LinearMap.BilinForm (ZMod 2) V) (hnd : B.Nondegenerate)
    (hpres : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    {H X : Subgroup G} [H.Normal] {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ H X I) (hfix : fixedSpace ρ H = ⊥)
    (hi : IsIrreducible (invariantSubspace ρ H I hI.invariant).toRepresentation)
    (hiso : ∀ u ∈ I, ∀ w ∈ I, B u w = 0)
    (hex : ∃ x : X, I.map (ρ (x : G)⁻¹) ≠ I)
    (hpair : ∀ x : X, I.map (ρ (x : G)⁻¹) ≠ I → I ⊔ I.map (ρ (x : G)⁻¹) = ⊤) :
    let R := invariantSubspace ρ H I hI.invariant
    Function.Injective R.toRepresentation.asGroupHom ∧
    ¬ Nonempty (Representation.Equiv R.toRepresentation R.toRepresentation.dual) ∧
    ∀ x : X, I.map (ρ (x : G)⁻¹) ≠ I → Nonempty (Representation.Equiv
      R.toRepresentation (conjugateSubrepresentation ρ H R (x : G)).toRepresentation.dual) := by
  let R := invariantSubspace ρ H I hI.invariant
  have hdual (x : X) (hx : I.map (ρ (x : G)⁻¹) ≠ I) :=
    isotropic_spanning_conjugate_dual ρ B hnd hpres H I hI.invariant hi hiso x (hpair x hx)
  obtain ⟨x,hx⟩ := hex
  let J := conjugateSubrepresentation ρ H R (x : G)
  have hj : IsIrreducible J.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom _).mpr
    simpa only [J, conjugateSubrepresentationOrderIso_apply, inv_inv] using
      ((conjugateSubrepresentationOrderIso ρ H (x : G)⁻¹).isAtom_iff R).mpr
      ((Subrepresentation.irreducible_iff_isAtom R).mp hi)
  have hisoJ : ∀ u ∈ J.toSubmodule, ∀ w ∈ J.toSubmodule, B u w = 0 := by
    rintro u ⟨u',hu,rfl⟩ w ⟨w',hw,rfl⟩
    exact (hpres (x : G)⁻¹ u' w').trans (hiso u' hu w' hw)
  have hne : ∃ u ∈ J.toSubmodule, ∃ w ∈ I, B u w ≠ 0 := by
    by_contra! hz
    have hbot : J.toSubmodule = ⊥ := by
      apply bot_unique
      intro u hu
      apply hnd.1 u
      intro w
      have hw : w ∈ I ⊔ I.map (ρ (x : G)⁻¹) := (hpair x hx).symm ▸ Submodule.mem_top
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add,hz u hu a ha,hisoJ u hu b hb,add_zero]
    exact ((Subrepresentation.irreducible_iff_isAtom J).mp hj).ne_bot
      (Subrepresentation.toSubmodule_injective hbot)
  let f := bilinearCrossPairing (ρ.comp H.subtype) B
    (fun h u w => hpres h u w) J R
  have hinj : Function.Injective f := bilinearCrossPairing_injective
    (ρ.comp H.subtype) B (fun h u w => hpres h u w) J R hj hne
  have hdim : finrank (ZMod 2) J.toSubmodule = finrank (ZMod 2) R.toSubmodule :=
    finrank_map_action ρ I (x : G)⁻¹
  let e := f.ofBijective ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using hdim)).mp hinj⟩
  refine ⟨faithful_of_spanning_dual_pair ρ hf H I hI.invariant x (hpair x hx) e,?_,hdual⟩
  rintro ⟨sd⟩
  exact hI.not_equiv_moved ρ hfix x hx ⟨(e.trans sd.symm).symm⟩
end Representation.BinaryOffender
