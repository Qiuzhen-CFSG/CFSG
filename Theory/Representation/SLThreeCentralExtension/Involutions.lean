module

public import Theory.Representation.SLThreeCentralExtension
public import Theory.Representation.BinaryOffender.ConjugateDisplacement
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.QuadraticDuality
public import Theory.Representation.PSL3Two.FourGroupGeometry.FixedSpaces.Certificates
import Mathlib.Tactic.FinCases

/-!
# Involutions in four-dimensional binary SL₃ extensions

Three elementary involutions generate SL₃(2), and all involutions are
conjugate. The conjugate-generation dimension bound therefore excludes
transvections on a four-space with no fixed vectors. Duality gives the
same exclusion on a commutator-generated four-space. Rank-nullity then
identifies the involution displacement and fixed spaces, both of dimension
two. An indecomposable four-space containing a natural submodule has no
nonzero fixed vector, since such a vector would give a direct summand.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.8(2)–(3), printed p.91.
-/

public section
open Matrix Representation Representation.BinaryOffender Subgroup
namespace BinaryLinearThree.NaturalExtension
private def generators : Fin 3 → Group := ![
  SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2),
  SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : ZMod 2),
  SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) (1 : ZMod 2)]

private theorem generators_generate : closure (Set.range generators) = ⊤ := by
  apply top_unique
  intro g _
  apply Representation.OneCohomology.SLHigherNatural.transvection_induction
    (fun g => g ∈ closure (Set.range generators)) ?_ (fun a b ha hb => mul_mem ha hb) g
  intro i j hij c
  have h0 := subset_closure (Set.mem_range_self (f := generators) 0)
  have h1 := subset_closure (Set.mem_range_self (f := generators) 1)
  have h2 := subset_closure (Set.mem_range_self (f := generators) 2)
  have h01 : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : ZMod 2) =
      generators 0 * generators 1 * generators 0 * generators 1 := by decide
  have h12 : SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : ZMod 2) =
      generators 1 * generators 2 * generators 1 * generators 2 := by decide
  have h20 : SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) =
      generators 2 * generators 0 * generators 2 * generators 0 := by decide
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp
  · fin_cases i <;> fin_cases j
    all_goals try first | exact False.elim (hij rfl) | exact h0 | exact h1 | exact h2
    · rw [h01]; exact mul_mem (mul_mem (mul_mem h0 h1) h0) h1
    · rw [h12]; exact mul_mem (mul_mem (mul_mem h1 h2) h1) h2
    · rw [h20]; exact mul_mem (mul_mem (mul_mem h2 h0) h2) h0

/-- Three conjugates of any involution generate the actual binary SL₃ group. -/
theorem exists_three_conjugate_generators (a : Group) (ha : a ≠ 1) (hsq : a * a = 1) :
    ∃ c : Fin 3 → Group, closure (Set.range fun i => c i * a * (c i)⁻¹) = ⊤ := by
  obtain ⟨k, hk⟩ := FourGroupGeometry.FixedSpaces.exists_involution_conjugator a ha hsq
  have ht (i : Fin 3) : generators i ≠ 1 ∧ generators i * generators i = 1 := by
    revert i; decide
  choose d hd using fun i => FourGroupGeometry.FixedSpaces.exists_involution_conjugator
    (generators i) (ht i).1 (ht i).2
  refine ⟨fun i => d i * k⁻¹, ?_⟩
  have he (i : Fin 3) : (d i * k⁻¹) * a * (d i * k⁻¹)⁻¹ = generators i := by
    have ha' : a = k * FourGroupGeometry.FixedSpaces.involution * k⁻¹ :=
      (eq_mul_inv_iff_mul_eq).mpr hk
    have hi : generators i = d i * FourGroupGeometry.FixedSpaces.involution * (d i)⁻¹ :=
      (eq_mul_inv_iff_mul_eq).mpr (hd i)
    rw [ha', hi]
    group
  simpa only [he] using generators_generate

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Group V)

/-- A four-space with zero fixed space has involution fixed codimension two. -/
theorem involution_codim_of_fixed_zero
    (hdim : Module.finrank (ZMod 2) V = 4) (hfix : ρ.invariants = ⊥)
    (a : Group) (ha : orderOf a = 2) : fixedCodim ρ (zpowers a) = 2 := by
  have hs : a * a = 1 := by simpa [pow_two, ha] using pow_orderOf_eq_one a
  have hn : a ≠ 1 := by intro h; simp [h] at ha
  obtain ⟨c,hc⟩ := exists_three_conjugate_generators a hn hs
  have hf : fixedSpace ρ (⊤ : Subgroup Group) = ⊥ := by
    rw [← hfix]
    ext v
    exact ⟨fun h g => h ⟨g,mem_top g⟩, fun h g => h g⟩
  have hlo := finrank_le_mul_fixedCodim_of_conjugate_generation ρ ⊤ hf a c hc.ge
  have hhi := (involution_actor_rank_and_fixedCodim ρ a ha).2.2.2
  omega

/-- Duality gives the same calculation for a commutator-generated four-space. -/
theorem involution_codim_of_commutator_top
    (hdim : Module.finrank (ZMod 2) V = 4) (hm : Coinvariants.ker ρ = ⊤)
    (a : Group) (ha : orderOf a = 2) : fixedCodim ρ (zpowers a) = 2 := by
  have hf : ρ.dual.invariants = ⊥ := by
    rw [← dualAnnihilator_coinvariantsKer, hm, Submodule.dualAnnihilator_top]
  have hd : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) V) = 4 := by
    rw [Subspace.dual_finrank_eq, hdim]
  rw [← fixedCodim_zpowers_dual]
  exact involution_codim_of_fixed_zero ρ.dual hd hf a ha

/-- In degree four, codimension two makes the displacement and fixed spaces equal. -/
theorem involution_range_eq_fixed
    (hdim : Module.finrank (ZMod 2) V = 4) (a : Group) (ha : orderOf a = 2)
    (hc : fixedCodim ρ (zpowers a) = 2) :
    LinearMap.range (ρ a - LinearMap.id) = fixedSpace ρ (zpowers a) ∧
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) = 2 := by
  have hf := fixedCodim_add_finrank ρ (zpowers a)
  have hd : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers a)) = 2 := by omega
  refine ⟨?_,hd⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v,rfl⟩
    rw [mem_fixedSpace_zpowers_iff]
    apply involution_fixes_displacement
    simpa [pow_two, ha] using pow_orderOf_eq_one a
  · rw [← fixedCodim_zpowers_eq_displacement_rank, hc, hd]
/-- In an indecomposable four-space a natural submodule has no fixed supplement. -/
theorem invariants_eq_bot_of_natural_submodule
    (hdim : Module.finrank (ZMod 2) V = 4)
    (N : Subrepresentation ρ) (e : Representation.Equiv N.toRepresentation W)
    (hind : ∀ A B : Submodule (ZMod 2) V,
      (∀ g v, v ∈ A → ρ g v ∈ A) →
      (∀ g v, v ∈ B → ρ g v ∈ B) → IsCompl A B → A = ⊥ ∨ B = ⊥) :
    ρ.invariants = ⊥ := by
  have hn : Module.finrank (ZMod 2) N.toSubmodule = 3 :=
    e.toLinearEquiv.finrank_eq.trans (Module.finrank_fin_fun (ZMod 2))
  have hnfix : N.toRepresentation.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    have he : e v ∈ Representation.OneCohomology.fixed W := by
      intro g
      have hh := LinearMap.congr_fun (e.isIntertwining' g) v
      change e (N.toRepresentation g v) = W g (e v) at hh
      exact hh.symm.trans (congrArg e (hv g))
    rw [Representation.OneCohomology.SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)] at he
    exact e.injective (show e v = e 0 from (show e v = 0 from he).trans e.map_zero.symm)
  have hd : Disjoint N.toSubmodule ρ.invariants := by
    apply Submodule.disjoint_def.mpr
    intro v hv hf
    have hv' : (⟨v,hv⟩ : N.toSubmodule) ∈ N.toRepresentation.invariants :=
      fun g => Subtype.ext (hf g)
    rw [hnfix] at hv'
    exact congrArg Subtype.val (show (⟨v,hv⟩ : N.toSubmodule) = 0 from hv')
  by_contra hfix
  let : Nontrivial ρ.invariants := Submodule.nontrivial_iff_ne_bot.mpr hfix
  have hp : 0 < Module.finrank (ZMod 2) ρ.invariants := Module.finrank_pos
  have hs := N.toSubmodule.finrank_sup_add_finrank_inf_eq ρ.invariants
  rw [hd.eq_bot, finrank_bot, add_zero, hn] at hs
  have hle := (N.toSubmodule ⊔ ρ.invariants).finrank_le
  rw [hdim] at hle
  have htop : N.toSubmodule ⊔ ρ.invariants = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hdim]
    omega
  rcases hind N.toSubmodule ρ.invariants
      (fun g v hv => N.apply_mem_toSubmodule g hv)
      (fun g v hv => by rw [hv g]; exact hv)
      ⟨hd,codisjoint_iff.mpr htop⟩ with h | h
  · rw [h, finrank_bot] at hn
    omega
  · exact hfix h

end BinaryLinearThree.NaturalExtension
