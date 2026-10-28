module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicSections

/-!
# Fixing the central-involution commutator two-space

The centralizer of the actor stabilizes its commutator space. If the full
flag stabilizer fixes that space, its normal generation of the concrete
middle parabolic forces fixation by the latter. A marked fixed vector
outside W and the lower commutator line suffice for the initial fixation.
Conjugation then transports the fixed critical line and actor normalizer.

The existence of the marked vector and the source normalizer implication
are separate inputs; neither is inferred merely from fixation modulo V₁.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.961–962 (PDF pp.978–979).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic

open Representation Representation.BinaryOffender ChiefFactors
open CriticalTransfer.MarkedGeometry
open BinaryLinear.MiddleParabolic

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

omit [FiniteDimensional (ZMod 2) U] in
/-- The setwise stabilizer of a subspace normalizes its pointwise fixer. -/
theorem stabilizer_normalizes_pointwise (C : Submodule (ZMod 2) U) :
    subspaceStabilizer ρ C ≤ Subgroup.normalizer (subspaceKernel ρ C ⊤ : Set H) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg k hk
  refine ⟨Subgroup.mem_top _, ?_⟩
  intro c hc
  have hinv := (subspaceStabilizer ρ C).inv_mem hg
  have hfix := hk.2 (ρ g⁻¹ c) ((hinv c).2 hc)
  change ρ (g * k * g⁻¹) c = c
  simp only [map_mul, Module.End.mul_apply]
  rw [hfix]
  simp [← Module.End.mul_apply, ← map_mul]

omit [FiniteDimensional (ZMod 2) U] in
/-- An element centralizing the actor preserves its literal commutator space. -/
theorem centralizer_stabilizes_commSpace (A : Subgroup H) :
    Subgroup.centralizer (A : Set H) ≤ subspaceStabilizer ρ (commSpace ρ A) := by
  apply le_subspaceStabilizer
  intro g hg c hc
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨⟨a, u⟩, rfl⟩ := hc
    have hga : g * a = a * g := (Subgroup.mem_centralizer_iff.mp hg a a.property).symm
    have hm := Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) a (ρ g u)
    change ρ a (ρ g u) - ρ g u ∈ commSpace ρ A at hm
    change ρ g (ρ a u - u) ∈ commSpace ρ A
    rwa [map_sub, ← Module.End.mul_apply, ← map_mul, hga, map_mul,
      Module.End.mul_apply]
  | zero => simp
  | add x y _ _ hx hy => simpa using (commSpace ρ A).add_mem hx hy
  | smul r x _ hx => simpa using (commSpace ρ A).smul_mem r hx

omit [FiniteDimensional (ZMod 2) U] in
/-- Normal generation promotes Borel fixation of the central-involution commutator space
to fixation by the middle parabolic. -/
theorem middle_fixes_commSpace
    (eH : H ≃* BinaryLinear.GL V)
    {L P F : Submodule (ZMod 2) V} (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (A : Subgroup H)
    (hA : A.map eH.toMonoidHom ≤ (Subgroup.center (borel L P F)).map (borel L P F).subtype)
    (hT : commSpace ρ A ≤ fixedSpace ρ ((borel L P F).comap eH.toMonoidHom)) :
    commSpace ρ A ≤ fixedSpace ρ ((middle L F).comap eH.toMonoidHom) := by
  let M := (middle L F).comap eH.toMonoidHom
  let N := subspaceKernel ρ (commSpace ρ A) ⊤
  have hcentral : M ≤ Subgroup.centralizer (A : Set H) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply eH.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using
      Subgroup.mem_centralizer_iff.mp (centralizes_flag_center hLP hPF hL hF hg)
        (eH a) (hA (Subgroup.mem_map_of_mem _ ha))
  have hnorm : M ≤ Subgroup.normalizer (N : Set H) :=
    (hcentral.trans (centralizer_stabilizes_commSpace ρ A)).trans
      (stabilizer_normalizes_pointwise ρ (commSpace ρ A))
  have hMN : middle L F ≤ N.map eH.toMonoidHom := by
    apply normally_generates hLP hPF hL hP hF
    · intro t ht
      refine Subgroup.mem_map.mpr ⟨eH.symm t, ?_, eH.apply_symm_apply t⟩
      refine ⟨Subgroup.mem_top _, ?_⟩
      intro u hu
      exact hT hu ⟨eH.symm t, by simpa using ht⟩
    · rw [Subgroup.le_normalizer_iff]
      intro g hg n hn
      obtain ⟨k, hk, rfl⟩ := hn
      have hm : eH.symm g ∈ M := by simpa [M] using hg
      refine Subgroup.mem_map.mpr
        ⟨eH.symm g * k * (eH.symm g)⁻¹, (hnorm hm k).mp hk, ?_⟩
      simp
  intro u hu g
  obtain ⟨k, hk, he⟩ := hMN g.property
  have he' : k = g := eH.injective he
  subst k
  exact hk.2 u hu

omit [FiniteDimensional (ZMod 2) U] in
/-- Fixation of the conjugate of the actual marked line normalizes the conjugate actor,
with the conjugation orientation retained. -/
theorem fixed_conjugate_line_normalizes
    (S : Submodule (ZMod 2) U) (B : Subgroup H) (g k : H)
    (hn : ∀ h : H, (∀ s ∈ S, ρ h s = s) → h ∈ Subgroup.normalizer (B : Set H))
    (hk : ∀ s ∈ S.map (ρ g), ρ k s = s) :
    k ∈ Subgroup.normalizer (B.map (MulAut.conj g).toMonoidHom : Set H) := by
  have hn' : g⁻¹ * k * g ∈ Subgroup.normalizer (B : Set H) := by
    apply hn
    intro s hs
    have hs' := hk (ρ g s) (Submodule.mem_map.mpr ⟨s, hs, rfl⟩)
    simp only [map_mul, Module.End.mul_apply]
    rw [hs']
    simp [← Module.End.mul_apply, ← map_mul]
  rw [← Subgroup.map_equiv_normalizer_eq]
  refine Subgroup.mem_map.mpr ⟨g⁻¹ * k * g, hn', ?_⟩
  change g * (g⁻¹ * k * g) * g⁻¹ = k
  group

omit [FiniteDimensional (ZMod 2) U] in
/-- An invariant binary line is fixed pointwise. -/
theorem binary_line_fixed_of_stable (S : Submodule (ZMod 2) U)
    (hS : Module.finrank (ZMod 2) S = 1) (T : Subgroup H)
    (hT : T ≤ subspaceStabilizer ρ S) : S ≤ fixedSpace ρ T := by
  intro v hv t
  by_cases hv0 : v = 0
  · simp [hv0]
  have hs := eq_span_singleton_of_mem_of_finrank_eq_one hS hv hv0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hs ▸ (hT t.property v).mpr hv)
  have hc0 : c ≠ 0 := by
    intro hz
    have hf : ρ t v = 0 := by simpa [hz] using hc.symm
    have hinj := (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)).injective
    exact hv0 (hinj (hf.trans (map_zero _).symm))
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc.symm

/-- A fixed marked vector outside W, together with the invariant lower commutator line,
spans and fixes the full commutator two-space. -/
theorem commSpace_fixed_of_marked_vector
    (W : Subrepresentation ρ) (A T : Subgroup H)
    (hc : T ≤ Subgroup.centralizer (A : Set H))
    (hW : Module.finrank (ZMod 2) (commSpace W.toRepresentation A) = 1)
    (hU : Module.finrank (ZMod 2) (commSpace ρ A) = 2)
    (v : U) (hv : v ∈ commSpace ρ A) (hvT : v ∈ fixedSpace ρ T)
    (hvW : v ∉ W.toSubmodule) :
    commSpace ρ A ≤ fixedSpace ρ T := by
  let C := (commSpace W.toRepresentation A).map W.toSubmodule.subtype
  have hC : Module.finrank (ZMod 2) C = 1 := by
    rw [Submodule.finrank_map_subtype_eq]
    exact hW
  have hCW : C ≤ W.toSubmodule := Submodule.map_subtype_le _ _
  have hvC : v ∉ C := fun h => hvW (hCW h)
  have hspan : C ⊔ Submodule.span (ZMod 2) {v} = commSpace ρ A := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact sup_le (commSpace_subrepresentation_le ρ W A)
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv))
    · rw [Submodule.finrank_sup_span_singleton hvC, hC, hU]
  have hfix : C ≤ fixedSpace ρ T := by
    rintro _ ⟨w, hw, rfl⟩ t
    exact congrArg Subtype.val
      (binary_line_fixed_of_stable W.toRepresentation _ hW T
        (hc.trans (centralizer_stabilizes_commSpace W.toRepresentation A)) hw t)
  rw [← hspan]
  exact sup_le hfix (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvT))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic
