module

public import Theory.AlgebraicGroup.RootSubgroups.Conjugation
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter

/-!
# Rank-one torus reflections and integral character functionals

An actual ambient conjugating element acts on a torus by
`t ↦ t * h(β(t))⁻¹`, where `h` is an algebraic cocharacter and `β ∘ h`
is the square map. Laurent evaluation then gives an integral reflection on
all characters. Conjugating actual root subgroups proves that this reflection
preserves the actual root set, without a root-system realization as input.

The structure below records this local geometric input; its existence from
reductivity is a separate theorem. In the inverse-conjugation root convention,
the SL₂ cocharacter has matrix `diag(a⁻¹, a)`, so its root value is `a²`.
The conjugated root subgroup in the proof is `n⁻¹ X n`, consistently with
pullback of its character by `t ↦ n t n⁻¹`.

Source: Borel, *Linear Algebraic Groups*, §§13.14 and 13.18(4);
GLS3, Theorem 1.9.5(d), Remarks 1.9.6 and §1.12.
The consumer is `RootSubgroups.ReductiveIntegralCoroots`.
-/

namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- A rank-one torus reflection induced by an actual ambient group element.
The cocharacter has square evaluation on its root; no Cartan values on other
roots are included in this geometric input. -/
public structure IntegralCorootReflection (T : ClosedSubgroup G) (β : TorusWeight T) where
  cocharacter : ClosedSubgroupTorusCocharacter T
  torusAction : AlgebraicGroup.Iso T.carrierVariety T.carrierVariety
  representative : Variety.Point G
  conjugation_eq : ∀ s : Variety.Point T.carrierVariety,
    T.includePoint (torusAction.hom.onPoints s) =
      representative * T.includePoint s * representative⁻¹
  action_eq : ∀ s : Variety.Point T.carrierVariety,
    torusAction.hom.onPoints s = s * (cocharacter.onPoints (β.onPoints s))⁻¹
  root_eq_two : WeightCocharacterEquation T β cocharacter 2

private theorem root_pullback_of_conjugation
    (e : AlgebraicGroup.Iso T.carrierVariety T.carrierVariety)
    (n : Variety.Point G)
    (he : ∀ s : Variety.Point T.carrierVariety,
      T.includePoint (e.hom.onPoints s) = n * T.includePoint s * n⁻¹)
    {χ : TorusWeight T} (hχ : IsTorusRoot T χ) :
    IsTorusRoot T (χ.comp e.hom) := by
  obtain ⟨X, hX, hχ⟩ := hχ
  refine ⟨X.conjugate n⁻¹, ⟨?_, (hX.conjugate n⁻¹).2⟩, ?_⟩
  · intro t ht x hx
    rw [X.mem_conjugate_iff] at hx ⊢
    simp only [inv_inv] at hx ⊢
    have ht' : n * t * n⁻¹ ∈ T := by
      let s := T.pointEquiv.symm ⟨t, ht⟩
      have hs : T.includePoint s = t := congrArg Subtype.val
        (T.pointEquiv.apply_symm_apply ⟨t, ht⟩)
      rw [← hs, ← he]
      exact (T.pointEquiv (e.hom.onPoints s)).property
    have h := hX.1 (n * t * n⁻¹) ht' (n * x * n⁻¹) hx
    change n * (t⁻¹ * x * t) * n⁻¹ ∈ X
    convert h using 1
    group
  · intro y t s
    let xIso := X.conjugateIso n⁻¹
    let x : OneParameterParametrization X.carrierVariety :=
      { hom := xIso.inv.comp y.hom
        inv := y.inv.comp xIso.hom
        hom_inv_id := by
          intro z
          change y.inv.onPoints (xIso.hom.onPoints
            (xIso.inv.onPoints (y.hom.onPoints z))) = z
          rw [xIso.inv_hom_id, y.hom_inv_id]
        inv_hom_id := by
          intro z
          change xIso.inv.onPoints (y.hom.onPoints
            (y.inv.onPoints (xIso.hom.onPoints z))) = z
          rw [y.inv_hom_id, xIso.hom_inv_id] }
    have hy (a : k) : X.includePoint (x.value a) =
        n * (X.conjugate n⁻¹).includePoint (y.value a) * n⁻¹ := by
      change X.inclusion.onPoints ((X.conjugateIso n⁻¹).inv.onPoints (y.value a)) =
        n * (X.conjugate n⁻¹).inclusion.onPoints (y.value a) * n⁻¹
      simpa only [inv_inv] using
        X.conjugateIso_inv_inclusion_apply n⁻¹ (y.value a)
    apply (MulAut.conj n).injective
    simp only [MulAut.conj_apply]
    calc
      _ = (T.includePoint (e.hom.onPoints s))⁻¹ * X.includePoint (x.value t) *
          T.includePoint (e.hom.onPoints s) := by
        rw [he, hy]
        group
      _ = X.includePoint (x.value (χ.pointCharacter (e.hom.onPoints s) * t)) :=
        hχ x t (e.hom.onPoints s)
      _ = _ := hy _

namespace IntegralCorootReflection
variable {β : TorusWeight T} (C : IntegralCorootReflection T β)
variable [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem pointCharacter_mul_zpow (χ ψ : TorusWeight T)
    (m : ℤ) (s : Variety.Point T.carrierVariety) :
    (χ * ψ ^ m).pointCharacter s = χ.pointCharacter s * ψ.pointCharacter s ^ m := by
  let ev : TorusWeight T →* k :=
    { toFun := fun η => η.pointCharacter s
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact (ev.map_mul χ (ψ ^ m)).trans
    (congrArg (fun z : k => ev χ * z) (map_zpow ev ψ m))

/-- Laurent evaluation gives the full-character reflection formula. -/
public theorem pullback_eq (χ : TorusWeight T) :
    χ.comp C.torusAction.hom =
      χ * β ^ (-characterCocharacterPairing T C.cocharacter (Additive.ofMul χ)) := by
  apply TorusCharacter.pointCharacter_injective
  ext s
  change χ.pointCharacter (C.torusAction.hom.onPoints s) = _
  calc
    _ = χ.pointCharacter s * (χ.pointCharacter
        (C.cocharacter.onPoints (β.onPoints s)))⁻¹ := by
      rw [C.action_eq, map_mul, map_inv]
    _ = χ.pointCharacter s * (β.pointCharacter s ^
        characterCocharacterPairing T C.cocharacter (Additive.ofMul χ))⁻¹ :=
      congrArg (fun z : k => χ.pointCharacter s * z⁻¹)
        (characterCocharacterPairing_spec T χ C.cocharacter (β.onPoints s))
    _ = _ := by
      rw [← zpow_neg]
      exact (pointCharacter_mul_zpow χ β _ s).symm

/-- The actual ambient representative makes the integral reflection preserve roots. -/
public theorem preserves_roots {χ : TorusWeight T} (hχ : IsTorusRoot T χ) :
    IsTorusRoot T
      (χ * β ^ (-characterCocharacterPairing T C.cocharacter (Additive.ofMul χ))) := by
  rw [← C.pullback_eq]
  exact root_pullback_of_conjugation C.torusAction C.representative C.conjugation_eq hχ

/-- The distinguished root evaluates to two on the canonical integral functional. -/
public theorem pairing_self : characterCocharacterPairing T C.cocharacter (Additive.ofMul β) = 2 := by
  obtain ⟨m, hm, huniq⟩ := weightCocharacterEquation_existsUnique T β C.cocharacter
  exact (huniq _ (characterCocharacterPairing_spec T β C.cocharacter)).trans
    (huniq _ C.root_eq_two).symm

end IntegralCorootReflection
end Theory.AlgebraicGroup
