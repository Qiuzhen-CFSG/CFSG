module
public import Theory.Representation.SL2FourQuadraticRecognition
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
/-!
# Quadratic recognition through the original SL₂(4) quotient map

An original actor H maps onto SL₂(4), and the map's kernel acts trivially on
an arbitrary binary H-module. If an actual Sylow two-subgroup is quadratic
and moves at most two dimensions, the module's literal global-fixed quotient
is the natural four-space. The source actor, the quotient map, and all fixed
attachments remain unchanged.

The proof descends the action through its invertible linear operators,
conjugates the image Sylow to the upper root group, applies quadratic
recognition, and undoes that conjugation on the vectors. Natural faithfulness
then identifies the exact original action kernel, not merely an abstract
isomorphism type of a section.

Source: Niles, “Pushing-up in finite groups” (1979), Lemma 2.8, printed
pp.32–33. The earlier proof that the offender is Sylow and that the odd
quotient kernel acts trivially remains a separate input to this application.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.SL2FourQuadraticRecognition
open SL2FourNatural
variable {H M : Type*} [Group H] [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M]

/-- Recognition on the original module and its original global fixed quotient,
through a surjective SL2(4) marking whose kernel acts trivially. -/
theorem natural_fixed_quotient_of_marked_sylow
    (ρ : Representation (ZMod 2) H M) (q : H →* SL)
    (hs : Function.Surjective q) (hk : q.ker ≤ ρ.ker)
    (hn : ρ ≠ 1) (A : Subgroup H) (hA : A.map q = BorelFactors.U0)
    (hq : IsQuadratic ρ A) (hd : fixedCodim ρ A ≤ 2) :
    ∃ e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V,
      ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v) := by
  have hkU : q.ker ≤ ρ.asGroupHom.ker := by
    intro h hh
    apply Units.ext
    exact hk hh
  let τ := q.liftOfSurjective hs ⟨ρ.asGroupHom, hkU⟩
  let σ : Representation (ZMod 2) SL M := (Units.coeHom _).comp τ
  have he (h : H) : σ (q h) = ρ h := by
    exact congrArg Units.val (q.liftOfRightInverse_comp_apply (Function.surjInv hs)
      (Function.rightInverse_surjInv hs) ⟨ρ.asGroupHom, hkU⟩ h)
  have hσ : σ ≠ 1 := by
    intro hh
    apply hn
    ext h v
    rw [← he, hh]
    rfl
  have heq (h : H) (v : M) :
      (LinearEquiv.refl (ZMod 2) M) (ρ h v) = σ (q h) (LinearEquiv.refl (ZMod 2) M v) := by
    exact LinearMap.congr_fun (he h).symm v
  have hquad : IsQuadratic σ BorelFactors.U0 := by
    rw [← hA]
    exact quadratic_map_equivariant ρ σ q (LinearEquiv.refl _ _) heq hq
  have hdim : fixedCodim σ BorelFactors.U0 ≤ 2 := by
    rw [← hA, ← fixedCodim_map_equivariant ρ σ q (LinearEquiv.refl _ _) heq A]
    exact hd
  have hfixed : fixedSpace ρ ⊤ = fixedSpace σ ⊤ := by
    have h := fixedSpace_map_equivariant ρ σ q (LinearEquiv.refl _ _) heq ⊤
    simpa only [LinearEquiv.refl_toLinearMap, Submodule.map_id,
      map_top_of_surjective q hs] using h
  obtain ⟨e, hee⟩ := natural_fixed_quotient σ hσ hquad hdim
  let E := (Submodule.quotEquivOfEq _ _ hfixed).trans e
  refine ⟨E, ?_⟩
  intro h v
  obtain ⟨x, rfl⟩ := (fixedSpace ρ ⊤).mkQ_surjective v
  change e (Submodule.quotEquivOfEq _ _ hfixed ((fixedSpace ρ ⊤).mkQ (ρ h x))) =
    specialLinearNatural 2 (q h) (e (Submodule.quotEquivOfEq _ _ hfixed ((fixedSpace ρ ⊤).mkQ x)))
  change e ((fixedSpace σ ⊤).mkQ (ρ h x)) =
    specialLinearNatural 2 (q h) (e ((fixedSpace σ ⊤).mkQ x))
  rw [← he]
  exact hee (q h) ((fixedSpace σ ⊤).mkQ x)

/-- The same recognition for any actual Sylow subgroup of the source actor.
The returned coordinates intertwine the original, unchanged SL2 marking. -/
theorem natural_fixed_quotient_of_sylow [Finite H]
    (ρ : Representation (ZMod 2) H M) (q : H →* SL)
    (hs : Function.Surjective q) (hk : q.ker ≤ ρ.ker)
    (hn : ρ ≠ 1) (S : Sylow 2 H)
    (hq : IsQuadratic ρ (S : Subgroup H))
    (hd : fixedCodim ρ (S : Subgroup H) ≤ 2) :
    ∃ e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V,
      ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v) := by
  let P : Sylow 2 SL := S.mapSurjective (f := q) hs
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL P
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
  let q' : H →* SL := (MulAut.conj g).toMonoidHom.comp q
  have hs' : Function.Surjective q' := (MulAut.conj g).surjective.comp hs
  have hk' : q'.ker ≤ ρ.ker := by
    intro h hh
    apply hk
    apply (MulAut.conj g).injective
    exact (show (MulAut.conj g) (q h) = 1 from hh).trans (map_one (MulAut.conj g)).symm
  have hA : (S : Subgroup H).map q' = BorelFactors.U0 := by
    rw [← map_map]
    exact congrArg (fun R : Sylow 2 SL => (R : Subgroup SL)) hg
  obtain ⟨E,hE⟩ := natural_fixed_quotient_of_marked_sylow ρ q' hs' hk' hn S hA hq hd
  refine ⟨E.trans (SL2FourNatural.action g⁻¹), ?_⟩
  intro h v
  change SL2FourNatural.action g⁻¹ (E (fixedQuotient ρ ⊤ h v)) =
    specialLinearNatural 2 (q h) (SL2FourNatural.action g⁻¹ (E v))
  rw [hE]
  change SL2FourNatural.action g⁻¹ (SL2FourNatural.action (q' h) (E v)) =
    SL2FourNatural.action (q h) (SL2FourNatural.action g⁻¹ (E v))
  rw [← LinearEquiv.mul_apply, ← map_mul, ← LinearEquiv.mul_apply, ← map_mul]
  have hm : g⁻¹ * q' h = q h * g⁻¹ := by
    change g⁻¹ * (g * q h * g⁻¹) = q h * g⁻¹
    simp only [← mul_assoc, inv_mul_cancel, one_mul]
  rw [hm]

/-- Complete action-recognition packet after descent to a marked SL2 quotient.
It identifies the actual representation kernel and the order of the literal
fixed quotient, as well as its natural coordinates. -/
theorem recognition_of_sylow [Finite H]
    (ρ : Representation (ZMod 2) H M) (q : H →* SL)
    (hs : Function.Surjective q) (hk : q.ker ≤ ρ.ker)
    (hn : ρ ≠ 1) (S : Sylow 2 H)
    (hq : IsQuadratic ρ (S : Subgroup H))
    (hd : fixedCodim ρ (S : Subgroup H) ≤ 2) :
    ρ.ker = q.ker ∧ Nonempty ((H ⧸ ρ.ker) ≃* SL) ∧
    Nat.card (M ⧸ fixedSpace ρ ⊤) = 16 ∧
    ∃ e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V,
      ∀ h v, e (fixedQuotient ρ ⊤ h v) = specialLinearNatural 2 (q h) (e v) := by
  obtain ⟨e, he⟩ := natural_fixed_quotient_of_sylow ρ q hs hk hn S hq hd
  have hker : ρ.ker = q.ker := by
    apply le_antisymm ?_ hk
    intro h hh
    apply SL2FourNatural.action_faithful
    apply LinearEquiv.ext
    intro v
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [map_one]
    change specialLinearNatural 2 (q h) (e u) = e u
    calc
      _ = e (fixedQuotient ρ ⊤ h u) := (he h u).symm
      _ = e u := by
        apply congrArg e
        obtain ⟨x, rfl⟩ := (fixedSpace ρ ⊤).mkQ_surjective u
        change (fixedSpace ρ ⊤).mkQ (ρ h x) = (fixedSpace ρ ⊤).mkQ x
        rw [show ρ h = 1 from hh]
        rfl
  refine ⟨hker, ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hs)⟩, ?_, e, he⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, SL2FourNatural.card_vector]

/-- The literal original normal quotient, retaining arbitrary central fixed
attachments of the module. The original kernel's trivial action is explicit. -/
theorem recognition_of_original_quotient [Finite H]
    (ρ : Representation (ZMod 2) H M) (K : Subgroup H) [K.Normal]
    (a : (H ⧸ K) ≃* SL) (hK : K ≤ ρ.ker)
    (hn : ρ ≠ 1) (S : Sylow 2 H)
    (hq : IsQuadratic ρ (S : Subgroup H))
    (hd : fixedCodim ρ (S : Subgroup H) ≤ 2) :
    ρ.ker = K ∧ Nonempty ((H ⧸ ρ.ker) ≃* SL) ∧
    Nat.card (M ⧸ fixedSpace ρ ⊤) = 16 ∧
    ∃ e : (M ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V,
      ∀ h v, e (fixedQuotient ρ ⊤ h v) =
        specialLinearNatural 2 (a (QuotientGroup.mk' K h)) (e v) := by
  let q := a.toMonoidHom.comp (QuotientGroup.mk' K)
  have hs : Function.Surjective q := a.surjective.comp (QuotientGroup.mk'_surjective K)
  have hk : q.ker = K := by
    ext h
    change a (QuotientGroup.mk' K h) = 1 ↔ h ∈ K
    rw [map_eq_one_iff a a.injective]
    exact QuotientGroup.eq_one_iff h
  have hh := recognition_of_sylow ρ q hs (hk ▸ hK) hn S hq hd
  rw [hk] at hh
  exact hh


end Representation.SL2FourQuadraticRecognition
