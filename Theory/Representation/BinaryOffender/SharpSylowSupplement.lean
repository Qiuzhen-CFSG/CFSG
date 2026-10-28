module
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinarySylowFixedSpace
public import Theory.Representation.SL2NaturalOffenders.Ratios
public import Theory.Representation.BinaryOffender.GeneratedCore
/-!
# A Sylow offender forces a global fixed-space supplement

Equality in the offender bound on an invariant submodule gives a supplement
to the Sylow fixed space. Averaging that fixed vector over the odd number
of Sylow cosets gives a globally fixed representative modulo the submodule.
For a genuine natural SL₂ section, the lower no-strong-offender theorem
forces the equality and the actual offender fills its defining Sylow.
No splitting or whole-module quotient marker is assumed.

Source application: Aschbacher–Smith B.6.9 and E.2.3(1), pp.115–116,216–217.
-/
public section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem invariants_supplement_of_sylow_offender
    (ρ : Representation (ZMod 2) G V) (W : Subrepresentation ρ)
    (hquot : ∀ g v, ρ g v - v ∈ W)
    (S : Sylow 2 G) (hS : IsOffender ρ (S : Subgroup G))
    (hn : ¬ IsStrongFFModule W.toRepresentation) :
    W.toSubmodule ⊔ ρ.invariants = ⊤ := by
  have hle : rank (S : Subgroup G) ≤ fixedCodim W.toRepresentation (S : Subgroup G) :=
    Nat.le_of_not_gt (fun h => hn ⟨S,hS.1,h⟩)
  have he : fixedCodim W.toRepresentation (S : Subgroup G) = fixedCodim ρ (S : Subgroup G) :=
    le_antisymm (fixedCodim_subrepresentation_le ρ W S) (hS.2.trans hle)
  have hs := (fixedCodim_subrepresentation_eq_iff ρ W S).mp he
  apply top_unique
  intro v _
  obtain ⟨w,hw,z,hz,hv⟩ := Submodule.mem_sup.mp (hs ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)))
  obtain ⟨z₀,hz₀,hzz⟩ := BinarySylowFixedSpace.fixed_lift_mod_trivial_quotient ρ S W.toSubmodule hquot z hz
  apply Submodule.mem_sup.mpr
  refine ⟨w+(z-z₀), W.toSubmodule.add_mem hw hzz,z₀,hz₀,?_⟩
  simpa only [add_assoc, sub_add_cancel] using hv

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
theorem natural_layer_supplement_of_moved_section
    (ρ : Representation (ZMod 2) G V) (W : Subrepresentation ρ)
    (L : Subgroup G) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (τ : Representation (ZMod 2) G (Fin 2 → F)) (hfaith : Function.Injective τ)
    (hnat : ∀ (g : L) v, τ (g:G) v = Matrix.mulVec (e g).val v)
    (hF : 2 < Nat.card F)
    (f : W.toSubmodule →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g w, f (W.toRepresentation g w) = τ g (f w))
    (hquot : ∀ g ∈ L, ∀ v, ρ g v - v ∈ W)
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsOffender ρ A) (hAT : A ≤ T) :
    W.toSubmodule ⊔ fixedSpace ρ L = ⊤ := by
  have hAτ : IsOffender τ A := ⟨hA.1,
    (fixedCodim_le_of_equivariant_surjection W.toRepresentation τ f hf he A).trans
      ((fixedCodim_subrepresentation_le ρ W A).trans hA.2)⟩
  have hAL : A = (T : Subgroup G) ⊓ L :=
    (SL2NaturalOffenders.Ratios.offender_iff_eq_sylowInf L e τ hnat hF hfaith T hAT).mp hAτ
  obtain ⟨P,hP⟩ := T.exists_sylow_map_eq_inf_of_normal L
  have hPA : (P : Subgroup L).map L.subtype = A := hP.trans hAL.symm
  let W' : Subrepresentation (ρ.comp L.subtype) :=
    ⟨W.toSubmodule,fun g _ hv => W.apply_mem_toSubmodule g hv⟩
  have hn : ¬ IsStrongFFModule W'.toRepresentation := by
    apply SL2NaturalOffenders.NoStrong.not_strong_of_natural_quotient
      W'.toRepresentation e.toMonoidHom e.injective f hf
    intro g w
    change f (W.toRepresentation (g:G) w) = _
    rw [he,hnat]
    rfl
  have hPoff : IsOffender (ρ.comp L.subtype) (P : Subgroup L) := by
    have h := hA.subgroupOf ρ (hAL.le.trans inf_le_right)
    have hh : A.subgroupOf L = (P : Subgroup L) := by
      rw [←hPA]
      ext x
      change (x:G) ∈ (P : Subgroup L).map L.subtype ↔ x ∈ P
      constructor
      · rintro ⟨a,ha,hax⟩
        exact L.subtype_injective hax ▸ ha
      · intro hx
        exact ⟨x,hx,rfl⟩
    rwa [hh] at h
  exact invariants_supplement_of_sylow_offender (ρ.comp L.subtype) W'
    (fun g v => hquot g g.property v) P hPoff hn
end Representation.BinaryOffender
