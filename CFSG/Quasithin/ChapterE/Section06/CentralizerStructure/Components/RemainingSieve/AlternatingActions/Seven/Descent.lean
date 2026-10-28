module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.AlternatingActions.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.AlternatingActions.Seven.Permutation
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# Transferring the seven-letter calculation through a central kernel

Relabel the actual quotient so its Sylow image is the displayed Sylow subgroup.
Faithful descent embeds the acting automorphisms in its four-element permutation
centralizer. Equality of orders gives all four permutations in the image.

Every fixed point downstairs lifts for an involution when the kernel has
exponent dividing three: its displacement corrects the original lift. This
is the same elementary lifting argument used in Chapter 2's
`AlternatingSeven.CoverAction`, applied here to every involution of the acting
four-group. Thus the two concrete centralizers generate the image of the join
of fixed subgroups. Perfectness and the central kernel lift this generation
to the whole original group.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.6.8(4),
printed p.248, and 1.1.5(3)(d), printed pp.501--502.
-/

public section

open Subgroup Equiv
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.AlternatingActions
namespace Seven
variable {X : Type*} [Group X]

private theorem fixed_lift (f : X →* A7) (hf : Function.Surjective f)
    (hker : ∀ c ∈ f.ker, c ^ 3 = 1) (α : MulAut X) (hα : α ^ 2 = 1)
    (y : A7) (hy : ∀ x, f x = y → f (α x) = y) :
    ∃ x : X, f x = y ∧ α x = x := by
  obtain ⟨x, hx⟩ := hf y
  let c : X := α x * x⁻¹
  have hfc : f c = 1 := by simp [c, hy x hx, hx]
  have hc : c ^ 3 = 1 := hker c (MonoidHom.mem_ker.mpr hfc)
  have hαα : α (α x) = x := by
    have hh := DFunLike.congr_fun hα x
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have hαc : α c = c⁻¹ := by
    dsimp [c]
    rw [map_mul, map_inv, hαα]
    group
  have hαx : α x = c * x := by simp [c]
  have hcc : c * c = c⁻¹ := by
    apply (eq_inv_iff_mul_eq_one).mpr
    simpa only [pow_succ, pow_zero, one_mul] using hc
  refine ⟨c⁻¹ * x, by simp [hfc, hx], ?_⟩
  rw [map_mul, map_inv, hαc, inv_inv, hαx, ← mul_assoc, hcc]

private theorem elementary_square (E : Subgroup (MulAut X)) [IsElementaryAbelian 2 E]
    (α : MulAut X) (hα : α ∈ E) : α ^ 2 = 1 := by
  exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 E) (⟨α, hα⟩ : E))

private theorem standard_action_calculations [Finite X] [Group.IsPerfect X]
    (f : X →* A7) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center X) (hcube : ∀ c ∈ f.ker, c ^ 3 = 1)
    (ρ : MulAut X →* S7) (hρ : Function.Injective ρ)
    (hact : ∀ (α : MulAut X) (x : X), (f (α x) : S7) =
      ρ α * (f x : S7) * (ρ α)⁻¹)
    (E : Subgroup (MulAut X)) [IsElementaryAbelian 2 E]
    (S : Sylow 2 X) (hS : (S : Subgroup X).map f = standardSylowGroup)
    (hfix : ∀ α ∈ E, ∀ x ∈ (S : Subgroup X), α x = x) :
    Nat.card E ≤ 4 ∧ (Nat.card E = 4 →
      (⊤ : Subgroup X) ≤ ⨆ (α : E) (_ : α ≠ 1), fixedSubgroup (α : MulAut X)) := by
  have hEC : E.map ρ ≤ permutationFixer := by
    rintro _ ⟨α, hα, rfl⟩ y ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := mem_map.mp (hS.symm ▸ hz)
    have he := hact α x
    rw [hfix α hα x hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  have hcard : Nat.card (E.map ρ) = Nat.card E := card_map_of_injective hρ
  refine ⟨?_, ?_⟩
  · rw [← hcard, ← permutationFixer_card]
    exact card_le_of_le hEC
  · intro hfour
    have heq : E.map ρ = permutationFixer := eq_of_le_of_card_ge hEC (by
      rw [permutationFixer_card, hcard, hfour])
    let H : Subgroup X := ⨆ (α : E) (_ : α ≠ 1), fixedSubgroup (α : MulAut X)
    apply perfect_le_of_map_le_of_central_kernel f hcentral ⊤ H
    rw [map_top_of_surjective _ hf]
    have hcentralizers (g : S7) (hg : g ∈ permutationFixer) (hg1 : g ≠ 1)
        (y : A7) (hy : (y : S7) * g = g * (y : S7)) : y ∈ H.map f := by
      obtain ⟨α, hα, he⟩ := mem_map.mp (heq.symm ▸ hg)
      have hα1 : (⟨α, hα⟩ : E) ≠ 1 := by
        intro hn
        apply hg1
        rw [← he, show α = 1 from congrArg Subtype.val hn, map_one]
      obtain ⟨x, hx, hfixed⟩ := fixed_lift f hf hcube α (elementary_square E α hα) y (by
        intro x hx
        apply Subtype.ext
        rw [hact, he, hx, ← hy, mul_inv_cancel_right])
      have hle : fixedSubgroup α ≤ H :=
        le_iSup_of_le (⟨α, hα⟩ : E) (le_iSup_of_le hα1 le_rfl)
      exact mem_map.mpr ⟨x, hle hfixed, hx⟩
    apply centralizers_generate
    · exact hcentralizers _ doubleSwap_mem_permutationFixer (by decide)
    · exact hcentralizers _ singleSwap_mem_permutationFixer (by decide)

private noncomputable def symmetricAutEquiv : S7 ≃* MulAut A7 :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))

private theorem symmetricAutEquiv_apply (g : S7) (x : A7) :
    (symmetricAutEquiv g x : S7) = g * (x : S7) * g⁻¹ := rfl

-- The actual cover map can be relabeled to put its Sylow image in the displayed coordinates.
private theorem coordinates [Finite X] (f : X →* A7) (hf : Function.Surjective f)
    (S : Sylow 2 X) : ∃ e : MulAut A7,
      (S : Subgroup X).map (e.toMonoidHom.comp f) = standardSylowGroup := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A7 (S.mapSurjective hf) standardSylow
  refine ⟨MulAut.conj g, ?_⟩
  rw [← Subgroup.map_map]
  exact congrArg Sylow.toSubgroup hg

/-- Faithful descent and an actual equivariant central projection onto A₇
suffice for the Sylow-fixing bound and fixed-point generation. -/
theorem projection_calculations [Finite X] [Group.IsPerfect X]
    (f : X →* A7) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ center X) (hcube : ∀ c ∈ f.ker, c ^ 3 = 1)
    (d : MulAut X →* MulAut A7) (hd : Function.Injective d)
    (hact : ∀ (α : MulAut X) (x : X), d α (f x) = f (α x))
    (E : Subgroup (MulAut X)) [IsElementaryAbelian 2 E]
    (S : Sylow 2 X) (hfix : ∀ α ∈ E, ∀ x ∈ (S : Subgroup X), α x = x) :
    Nat.card E ≤ 4 ∧ (Nat.card E = 4 →
      (⊤ : Subgroup X) ≤ ⨆ (α : E) (_ : α ≠ 1), fixedSubgroup (α : MulAut X)) := by
  obtain ⟨e, hS⟩ := coordinates f hf S
  let F : X →* A7 := e.toMonoidHom.comp f
  let D : MulAut X →* MulAut A7 := (MulAut.congr e).toMonoidHom.comp d
  let ρ : MulAut X →* S7 := symmetricAutEquiv.symm.toMonoidHom.comp D
  have hker : F.ker = f.ker := by
    ext x
    change e (f x) = 1 ↔ f x = 1
    constructor
    · intro hx
      exact e.injective (hx.trans e.map_one.symm)
    · intro hx
      rw [hx, map_one]
  have hρ : Function.Injective ρ :=
    symmetricAutEquiv.symm.injective.comp ((MulAut.congr e).injective.comp hd)
  have hD (α : MulAut X) (x : X) : D α (F x) = F (α x) := by
    change e (d α (e.symm (e (f x)))) = e (f (α x))
    rw [e.symm_apply_apply, hact]
  have hρD (α : MulAut X) : symmetricAutEquiv (ρ α) = D α :=
    symmetricAutEquiv.apply_symm_apply _
  apply standard_action_calculations F (e.surjective.comp hf)
    (hker ▸ hcentral) (hker ▸ hcube) ρ hρ ?_ E S hS hfix
  intro α x
  rw [← hD, ← hρD]
  exact symmetricAutEquiv_apply _ _

end Seven
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.AlternatingActions
