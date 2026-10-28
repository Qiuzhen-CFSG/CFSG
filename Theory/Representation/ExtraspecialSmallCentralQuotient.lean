module
public import Theory.Representation.ExtraspecialCentralQuotientDegree
public import Theory.Representation.CubicClifford.Dimension
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupAction.QuotientConjugation
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
/-!
# Kernels of small binary extraspecial central-quotient actions

For a nontrivial simple binary representation killing the center of an
extraspecial two-residual of order 27, dimension two gives residual image
of order three and residual kernel of order nine. Dimension four gives
residual image of order nine and kernel exactly the center. The cubic
Clifford bound excludes image of order three in dimension four; the
order of GL₂(2) excludes image of order nine in dimension two.

If the extraspecial subgroup contains its ambient centralizer, the latter
kernel equality holds on the entire acting group: a kernel element acts
on the extraspecial subgroup by a central automorphism, hence by an inner
automorphism. The original actor and quotient kernels are retained.

Source application: the remaining point-central chief intervals in
Aschbacher–Smith 14.7.20(2), printed p.1049. These calculations do not
exclude those intervals from the original ambient configuration.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace Representation

/-- An inverting involution bounds dimension without assuming faithfulness. -/
theorem extraspecial_center_kernel_dimension_bound
    {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) [σ.IsIrreducible]
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hZ : (center P).map P.subtype ≤ σ.ker)
    (hmove : ¬ P ≤ σ.ker) (t : D) (ht : t^2=1)
    (hne : (MulAut.conjNormal t : MulAut P) ≠ 1)
    (hcenter : ∀ z ∈ center P, (MulAut.conjNormal t : MulAut P) z = z) :
    Module.finrank (ZMod 2) W ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (σ t - 1)) := by
  let a : MulAut P := MulAut.conjNormal t
  have ha : Function.Involutive a := by
    intro x
    have he : a^2=1 := by
      change (MulAut.conjNormal t : MulAut P)^2=1
      rw [←map_pow,ht,map_one]
    exact congrArg (fun f : MulAut P => f x) (by simpa only [pow_two] using he)
  have hi := (IsExtraspecial.exponent_and_frattini_inversion_of_card27
    hP a ha hne hcenter).2
  have hφ : frattini P ≤ (σ.comp P.subtype).ker := by
    rw [IsExtraspecial.frattini_eq_center_three]
    intro z hz
    exact hZ (mem_map_of_mem P.subtype hz)
  let τ := quotientOfLEKer (σ.comp P.subtype) (frattini P) hφ
  have hinv : ∀ x ∈ P, σ (t*x*t⁻¹) = σ x⁻¹ := by
    intro x hx
    exact congrArg τ (hi ⟨x,hx⟩)
  have hfix : invariants (σ.comp P.subtype) = ⊥ := by
    by_contra hn
    exact hmove (le_ker_of_normal_invariants_ne_bot σ P hn)
  exact finrank_le_twice_displacement_of_inversion_mod_kernel σ P
    (by rw [hP]; decide) t hinv hfix

/-- Exact residual image and kernel in binary dimensions two and four. -/
theorem extraspecial_center_kernel_residual_card
    {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) [σ.IsIrreducible]
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hR : P = pResidual 2 D)
    (hZ : (center P).map P.subtype ≤ σ.ker) (hmove : ¬ P ≤ σ.ker)
    (hd : Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 4) :
    (Module.finrank (ZMod 2) W = 2 ∧ Nat.card (P ⧸ (σ.comp P.subtype).ker) = 3 ∧
      Nat.card (σ.ker.subgroupOf P) = 9) ∨
    (Module.finrank (ZMod 2) W = 4 ∧ Nat.card (P ⧸ (σ.comp P.subtype).ker) = 9 ∧
      σ.ker.subgroupOf P = center P) := by
  classical
  let q := QuotientGroup.mk' σ.ker
  let τ := quotientOfLEKer σ σ.ker le_rfl
  let : τ.IsIrreducible := (quotientOfLEKer_irreducible_iff σ _ le_rfl).mpr inferInstance
  let R := P.map q
  let : R.Normal := (inferInstance : P.Normal).map q (QuotientGroup.mk'_surjective _)
  have hker : (q.comp P.subtype).ker = (σ.comp P.subtype).ker := by
    ext x
    exact QuotientGroup.eq_one_iff _
  let e : (P ⧸ (σ.comp P.subtype).ker) ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange (q.comp P.subtype)).trans
        (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp,range_subtype])))
  have hc : Nat.card (P ⧸ (σ.comp P.subtype).ker) = Nat.card R := Nat.card_congr e.toEquiv
  have hdiv := (extraspecial_center_kernel_quotient σ P hP hZ).2
  have hm : ¬ R ≤ τ.ker := by
    intro hh
    apply hmove
    intro x hx
    exact hh (mem_map_of_mem q hx)
  have hRne : R ≠ ⊥ := fun he => hm (he ▸ bot_le)
  have hpos := (one_lt_card_iff_ne_bot R).mpr hRne
  have h3or9 : Nat.card R = 3 ∨ Nat.card R = 9 := by
    rw [hc] at hdiv
    have hv := (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card R ∣ 3^2 by simpa using hdiv)
    obtain ⟨n,hn,he⟩ := hv
    interval_cases n
    · have hx : Nat.card R = 1 := he
      omega
    · exact Or.inl he
    · exact Or.inr he
  have hthree (h3 : Nat.card R = 3) : Module.finrank (ZMod 2) W = 2 := by
    apply CubicClifford.finrank_eq_two τ ⊥ R h3 bot_le _ hm
    apply (pResidual_le_iff_isPGroup_quotient 2 (⊥ ⊔ R)).mp
    rw [bot_sup_eq,←map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _),←hR]
  have htwo (h2 : Module.finrank (ZMod 2) W = 2) : Nat.card R = 3 := by
    let b := Module.finBasisOfFinrankEq (ZMod 2) W h2
    let σP : Representation (ZMod 2) P W := σ.comp P.subtype
    let f := (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp
      σP.asGroupHom
    have hk : f.ker = (σ.comp P.subtype).ker := by
      ext x
      change (Matrix.GeneralLinearGroup.toLin' b).symm (σP.asGroupHom x) = 1 ↔ _
      constructor
      · intro hx
        have hu := (Matrix.GeneralLinearGroup.toLin' b).symm.injective
          (hx.trans ((Matrix.GeneralLinearGroup.toLin' b).symm.map_one).symm)
        exact congrArg Units.val hu
      · intro hx
        have hu : σP.asGroupHom x = 1 := Units.ext hx
        rw [hu,map_one]
    have hg : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]
    have hh := f.range.card_subgroup_dvd_card
    rw [←Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hk,hc,hg] at hh
    rcases h3or9 with hh3 | hh9
    · exact hh3
    · norm_num [hh9] at hh
  have hN : (σ.comp P.subtype).ker = σ.ker.subgroupOf P := rfl
  have hprod := card_eq_card_quotient_mul_card_subgroup ((σ.comp P.subtype).ker)
  rw [hP,hc,hN] at hprod
  rcases hd with h2 | h4
  · exact Or.inl ⟨h2,(hc.trans (htwo h2)),by rw [htwo h2] at hprod; omega⟩
  · have h9 : Nat.card R = 9 := h3or9.resolve_left (fun he => by have := hthree he; omega)
    refine Or.inr ⟨h4,hc.trans h9,?_⟩
    apply (eq_of_le_of_card_ge (show center P ≤ σ.ker.subgroupOf P from
      fun z hz => hZ (mem_map_of_mem P.subtype hz)) ?_).symm
    rw [IsExtraspecial.center_order_p 3 P]
    rw [h9] at hprod
    omega
/-- For a self-centralizing extraspecial subgroup, its central restriction
kernel is also the full action kernel. -/
theorem extraspecial_full_kernel_of_restriction_kernel
    {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W)
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hC : centralizer (P : Set D) ≤ P)
    (hN : σ.ker.subgroupOf P = center P) :
    σ.ker = (center P).map P.subtype := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : σ.ker ≤ P := by
    intro n hn
    let a : MulAut P := MulAut.conjNormal n
    have ha : ∀ x : P, a x * x⁻¹ ∈ center P := by
      intro x
      rw [←hN]
      change n*(x : D)*n⁻¹*(x : D)⁻¹ ∈ σ.ker
      rw [show n*(x : D)*n⁻¹*(x : D)⁻¹ = n*((x : D)*n⁻¹*(x : D)⁻¹) by group]
      exact σ.ker.mul_mem hn ((inferInstance : σ.ker.Normal).conj_mem n⁻¹ (σ.ker.inv_mem hn) x)
    obtain ⟨y,hy⟩ := IsExtraspecial.exists_conj_of_central_displacement (p := 3) a ha
    have he : (MulAut.conjNormal (y : D) : MulAut P) = MulAut.conjNormal n := by
      rw [MulAut.conjNormal_val]
      exact hy
    have hc : (y : D)⁻¹*n ∈ centralizer (P : Set D) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer P]
      change (MulAut.conjNormal ((y : D)⁻¹*n) : MulAut P) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using P.mul_mem y.property (hC hc)
  rw [←hN,subgroupOf_map_subtype,inf_eq_left.mpr hle]
end Representation
