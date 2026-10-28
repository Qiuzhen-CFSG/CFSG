module

public import Theory.Representation.BinaryOffender.IrreducibleSection

/-!
# Addition on the actual paired central quotient

If K₀ = K₁ ⊔ K₂ and W = W₁ + W₂, with each Wᵢ fixed by the other
factor, addition induces (W₁/C_W₁(K₁)) × (W₂/C_W₂(K₂)) ≃ W/C_W(K₀).
Testing fixedness under each factor separately proves injectivity. In
particular the intersection W₁ ∩ W₂ is handled through the fixed spaces;
no direct-sum decomposition of W is assumed.

This is the linear-algebra step for Aschbacher–Smith F.9.18(5iii), printed
pp.325–326, and 13.8.16, pp.952–953 (1 March 2004 manuscript). The model
recognition of the individual factor quotients is a separate prerequisite.
-/

@[expose] public section

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.PairQuotient
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  {K₀ K₁ K₂ : Subgroup G} {W W₁ W₂ : Submodule (ZMod 2) V}

private theorem fixed_sup {v : V} (h₁ : v ∈ fixedSpace ρ K₁)
    (h₂ : v ∈ fixedSpace ρ K₂) : v ∈ fixedSpace ρ (K₁ ⊔ K₂) := by
  let F : Subgroup G :=
    { carrier := {g | ρ g v = v}
      one_mem' := by simp
      mul_mem' := by
        intro g h hg hh
        change ρ (g * h) v = v
        rw [map_mul, Module.End.mul_apply, hh, hg]
      inv_mem' := by
        intro g hg
        change ρ g⁻¹ v = v
        calc
          ρ g⁻¹ v = ρ g⁻¹ (ρ g v) := congrArg (ρ g⁻¹) hg.symm
          _ = v := by simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Module.End.one_apply] }
  have hF : K₁ ⊔ K₂ ≤ F := sup_le (fun g hg => h₁ ⟨g, hg⟩) (fun g hg => h₂ ⟨g, hg⟩)
  intro g
  exact hF g.property

variable (hK : K₀ = K₁ ⊔ K₂) (hW : W = W₁ ⊔ W₂)
  (h₁₂ : W₁ ≤ fixedSpace ρ K₂) (h₂₁ : W₂ ≤ fixedSpace ρ K₁)

include hK h₁₂ h₂₁ in
/-- Testing each factor separately identifies the actual fixed vectors of a sum. -/
theorem sum_mem_fixed_iff (x : W₁) (y : W₂) :
    (x : V) + y ∈ fixedSpace ρ K₀ ↔
      (x : V) ∈ fixedSpace ρ K₁ ∧ (y : V) ∈ fixedSpace ρ K₂ := by
  subst K₀
  constructor
  · intro h
    constructor
    · intro k
      have he := h ⟨k, (le_sup_left : K₁ ≤ K₁ ⊔ K₂) k.property⟩
      change ρ k ((x : V) + y) = (x : V) + y at he
      have hy : ρ k y = y := h₂₁ y.property k
      rw [map_add, hy] at he
      exact add_right_cancel he
    · intro k
      have he := h ⟨k, (le_sup_right : K₂ ≤ K₁ ⊔ K₂) k.property⟩
      change ρ k ((x : V) + y) = (x : V) + y at he
      have hx : ρ k x = x := h₁₂ x.property k
      rw [map_add, hx] at he
      exact add_left_cancel he
  · rintro ⟨hx, hy⟩
    exact (fixedSpace ρ (K₁ ⊔ K₂)).add_mem
      (fixed_sup ρ hx (h₁₂ x.property)) (fixed_sup ρ (h₂₁ y.property) hy)

/-- Addition descends from the factor central quotients to the literal quotient of W. -/
noncomputable def centralSumMap :
    (centralQuotient ρ K₁ W₁ × centralQuotient ρ K₂ W₂) →ₗ[ZMod 2]
      centralQuotient ρ K₀ W :=
  ((fixedSpace ρ K₁).comap W₁.subtype |>.mapQ
    ((fixedSpace ρ K₀).comap W.subtype)
    (Submodule.inclusion (show W₁ ≤ W from hW ▸ le_sup_left)) (by
      intro x hx
      change (x : V) ∈ fixedSpace ρ K₀
      rw [hK]
      exact fixed_sup ρ hx (h₁₂ x.property))).coprod
  ((fixedSpace ρ K₂).comap W₂.subtype |>.mapQ
    ((fixedSpace ρ K₀).comap W.subtype)
    (Submodule.inclusion (show W₂ ≤ W from hW ▸ le_sup_right)) (by
      intro y hy
      change (y : V) ∈ fixedSpace ρ K₀
      rw [hK]
      exact fixed_sup ρ (h₂₁ y.property) hy))

/-- A representative formula independent of a chosen decomposition of W. -/
theorem centralSumMap_mk (x : W₁) (y : W₂) :
    centralSumMap ρ hK hW h₁₂ h₂₁ (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (⟨(x : V) + y,
        hW ▸ Submodule.add_mem_sup x.property y.property⟩ : W) := by
  simp only [centralSumMap, LinearMap.coprod_apply, Submodule.mapQ_apply,
    ← Submodule.Quotient.mk_add]
  rfl

/-- The overlap of the two spaces disappears through their actual fixed subspaces. -/
theorem centralSumMap_bijective :
    Function.Bijective (centralSumMap ρ hK hW h₁₂ h₂₁) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    rintro ⟨a, b⟩ hab
    induction a using Submodule.Quotient.induction_on with | _ x =>
    induction b using Submodule.Quotient.induction_on with | _ y =>
    rw [centralSumMap_mk, Submodule.Quotient.mk_eq_zero] at hab
    obtain ⟨hx, hy⟩ := (sum_mem_fixed_iff ρ hK h₁₂ h₂₁ x y).mp hab
    exact Prod.ext ((Submodule.Quotient.mk_eq_zero _).mpr hx)
      ((Submodule.Quotient.mk_eq_zero _).mpr hy)
  · intro a
    induction a using Submodule.Quotient.induction_on with | _ w =>
    obtain ⟨x, hx, y, hy, he⟩ := Submodule.mem_sup.mp (show (w : V) ∈ W₁ ⊔ W₂ by rw [← hW]; exact w.property)
    refine ⟨(Submodule.Quotient.mk (⟨x, hx⟩ : W₁),
      Submodule.Quotient.mk (⟨y, hy⟩ : W₂)), ?_⟩
    rw [centralSumMap_mk]
    exact congrArg Submodule.Quotient.mk (Subtype.ext he)

/-- The central quotient of the sum is the product of the two central quotients. -/
noncomputable def centralSumEquiv :
    (centralQuotient ρ K₁ W₁ × centralQuotient ρ K₂ W₂) ≃ₗ[ZMod 2]
      centralQuotient ρ K₀ W :=
  LinearEquiv.ofBijective (centralSumMap ρ hK hW h₁₂ h₂₁)
    (centralSumMap_bijective ρ hK hW h₁₂ h₂₁)

theorem centralSumEquiv_mk (x : W₁) (y : W₂) :
    centralSumEquiv ρ hK hW h₁₂ h₂₁ (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (⟨(x : V) + y,
        hW ▸ Submodule.add_mem_sup x.property y.property⟩ : W) :=
  centralSumMap_mk ρ hK hW h₁₂ h₂₁ x y

theorem centralSumEquiv_symm_mk (x : W₁) (y : W₂) :
    (centralSumEquiv ρ hK hW h₁₂ h₂₁).symm
      (Submodule.Quotient.mk (⟨(x : V) + y,
        hW ▸ Submodule.add_mem_sup x.property y.property⟩ : W)) =
      (Submodule.Quotient.mk x, Submodule.Quotient.mk y) := by
  rw [← centralSumEquiv_mk ρ hK hW h₁₂ h₂₁]
  exact LinearEquiv.symm_apply_apply _ _

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.PairQuotient
