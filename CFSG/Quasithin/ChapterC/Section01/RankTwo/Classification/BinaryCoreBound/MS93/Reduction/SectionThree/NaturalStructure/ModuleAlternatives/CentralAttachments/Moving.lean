module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralAttachments.Basic

/-!
# Natural coordinates on the actual moving module

The established quotient classification and six-dimensional bound apply to
D = [V,SL₃(2)]. The doubled quotient is injective; the one-copy fixed kernel
has dimension at most one by the checked H¹ calculation. This gives the
three moving-layer alternatives, retaining the nonsplit four-dimensional
cover. Quotient coordinates are actual linear equivalences and satisfy the
original marked action equation.

Source: Aschbacher–Smith B.4.8(1), B.4.9(2), B.5.1, printed pp.91–103;
Meierfrankenfeld–Stellmacher (1993), (3.2), printed p.863.
-/

@[expose] public section
open Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
open AbelianCore.QuotientRecognition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) SL V}

/-- Natural copies have zero fixed space, for every common marking. -/
theorem Copies.fixed_eq_bot {m : ℕ} (e : Copies ρ m) : fixedSpace ρ ⊤ = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  apply e.equiv.injective
  rw [map_zero]
  funext i
  have hfix : e.equiv v i ∈ fixed (specialLinearNatural (k := ZMod 2) 3) := by
    intro g
    have he := e.equivariant (e.marking.symm g) v i
    have hv' : ρ (e.marking.symm g) v = v := hv ⟨e.marking.symm g, Subgroup.mem_top _⟩
    rw [hv', e.marking.apply_symm_apply] at he
    exact he.symm
  rw [SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)] at hfix
  exact hfix

/-- Natural coordinates give quotient coordinates with their exact fixed kernel. -/
noncomputable def Copies.toQuotient {m : ℕ} (e : Copies ρ m) : ModuleQuotient ρ m where
  marking := e.marking
  projection := e.equiv.toLinearMap
  surjective := e.equiv.surjective
  kernel := (LinearMap.ker_eq_bot.mpr e.equiv.injective).trans e.fixed_eq_bot.symm
  equivariant := e.equivariant

/-- Injective natural quotient coordinates are actual natural coordinates. -/
noncomputable def copiesOfQuotient {m : ℕ} (q : ModuleQuotient ρ m)
    (hi : Function.Injective q.projection) : Copies ρ m where
  marking := q.marking
  equiv := LinearEquiv.ofBijective q.projection ⟨hi, q.surjective⟩
  equivariant := q.equivariant

/-- No central kernel remains once a natural quotient is injective. -/
theorem fixed_eq_bot_of_quotient_injective {m : ℕ} (q : ModuleQuotient ρ m)
    (hi : Function.Injective q.projection) : fixedSpace ρ ⊤ = ⊥ := by
  rw [← q.kernel]
  exact LinearMap.ker_eq_bot.mpr hi

/-- The surjection explicitly identifies the quotient by its fixed kernel
with the natural coordinate space. -/
noncomputable def quotientCoordinates {m : ℕ} (q : ModuleQuotient ρ m) :
    (V ⧸ fixedSpace ρ ⊤) ≃ₗ[ZMod 2] (Fin m → Fin 3 → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ q.kernel.symm).trans
    (q.projection.quotKerEquivOfSurjective q.surjective)

/-- The quotient coordinates agree with the given natural projection. -/
theorem quotientCoordinates_mk {m : ℕ} (q : ModuleQuotient ρ m) (v : V) :
    quotientCoordinates q ((fixedSpace ρ ⊤).mkQ v) = q.projection v := by
  simp only [quotientCoordinates, LinearEquiv.trans_apply, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The induced quotient identification keeps the same automorphism marking. -/
theorem quotientCoordinates_equivariant {m : ℕ} (q : ModuleQuotient ρ m)
    (g : SL) (v : V) (i : Fin m) :
    quotientCoordinates q ((fixedSpace ρ ⊤).mkQ (ρ g v)) i =
      specialLinearNatural 3 (q.marking g)
        (quotientCoordinates q ((fixedSpace ρ ⊤).mkQ v) i) := by
  rw [quotientCoordinates_mk, quotientCoordinates_mk]
  exact q.equivariant g v i

variable [FiniteDimensional (ZMod 2) V] (ρ)

/-- The doubled quotient exhausts the six-dimensional bound on D. -/
theorem two_quotient_injective (hFF : IsFFModule ρ)
    (q : ModuleQuotient (moving ρ).toRepresentation 2) : Function.Injective q.projection := by
  have hr := q.projection.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr q.surjective, finrank_top] at hr
  have hd : Module.finrank (ZMod 2) (Fin 2 → Fin 3 → ZMod 2) = 6 := by simp [Module.finrank_pi_fintype]
  have hb := moving_finrank_le_six ρ hFF
  have hk : Module.finrank (ZMod 2) q.projection.ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The one-copy central kernel in the actual D has dimension at most one. -/
theorem one_quotient_kernel_finrank_le_one
    (q : ModuleQuotient (moving ρ).toRepresentation 1) :
    Module.finrank (ZMod 2) (fixedSpace (moving ρ).toRepresentation ⊤) ≤ 1 := by
  have hc := oneCopy_kernel_card_le_two _ (moving_full ρ) q
  rw [q.kernel, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  by_contra hn
  have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show
    2 ≤ Module.finrank (ZMod 2) (fixedSpace (moving ρ).toRepresentation ⊤) by omega)
  norm_num at hh
  omega

/-- The abstract moving-layer trichotomy for D = [V,SL₃(2)].
All natural coordinates have one common marking; the last alternative retains
its actual fixed line and does not split the extension. -/
theorem moving_trichotomy (hρ : Function.Injective ρ) (hFF : IsFFModule ρ) :
    (Nonempty (Copies (moving ρ).toRepresentation 1) ∧
      Disjoint (fixedSpace ρ ⊤) (moving ρ).toSubmodule) ∨
    (Nonempty (Copies (moving ρ).toRepresentation 2) ∧
      Disjoint (fixedSpace ρ ⊤) (moving ρ).toSubmodule) ∨
    (Nonempty (ModuleQuotient (moving ρ).toRepresentation 1) ∧
      Module.finrank (ZMod 2)
        (fixedSpace ρ ⊤ ⊓ (moving ρ).toSubmodule : Submodule (ZMod 2) V) = 1) := by
  obtain ⟨m, hm, ⟨q⟩⟩ := moving_quotient ρ hρ hFF
  rcases hm with rfl | rfl
  · have hb := one_quotient_kernel_finrank_le_one ρ q
    by_cases hz : fixedSpace (moving ρ).toRepresentation ⊤ = ⊥
    · have hi : Function.Injective q.projection := LinearMap.ker_eq_bot.mp (q.kernel.trans hz)
      exact Or.inl ⟨⟨copiesOfQuotient q hi⟩, (disjoint_iff_fixedMoving_eq_bot ρ).mpr hz⟩
    · have hn : Module.finrank (ZMod 2) (fixedSpace (moving ρ).toRepresentation ⊤) ≠ 0 :=
        fun h => hz (Submodule.finrank_eq_zero.mp h)
      exact Or.inr (Or.inr ⟨⟨q⟩, (fixedMovingEquiv ρ).finrank_eq.symm.trans (by omega)⟩)
  · have hi := two_quotient_injective ρ hFF q
    exact Or.inr (Or.inl ⟨⟨copiesOfQuotient q hi⟩,
      (disjoint_iff_fixedMoving_eq_bot ρ).mpr (fixed_eq_bot_of_quotient_injective q hi)⟩)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.CentralAttachments
