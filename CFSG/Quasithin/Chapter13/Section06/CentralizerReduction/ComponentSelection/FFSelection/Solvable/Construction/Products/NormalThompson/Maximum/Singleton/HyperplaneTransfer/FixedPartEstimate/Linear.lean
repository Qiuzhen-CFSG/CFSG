module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Cocycle
public import Theory.Representation.PSL3Two.ResidualFFForms.ConstituentBudget.Dimension
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Ambient
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Displacement in a nonsplit binary three-dimensional natural extension

For a faithful binary SL₃(2) action, the kernel on the moved space is a normal
two-group and therefore trivial. When that space has dimension three, a basis
identifies its linear group with GL₃(2) = SL₃(2). The resulting injective
endomorphism is an automorphism, providing the actual natural marking and
intertwiner without assuming them.

The checked exceptional-cocycle calculation says that an involution-fixed
vector lies in the natural submodule plus the global fixed space. If this
sum is proper, the involution's fixed space lies strictly inside it: equality
would make the involution trivial on the faithful natural submodule. These
two strict inclusions give fixed codimension at least two. Every elementary
abelian subgroup of SL₃(2) has rank at most two, giving the required estimate.

The cohomology calculation is reused through the existing marked-extension
lemma in the Chapter C development; no model is substituted without an
intertwiner. This applies to B.5.6(5)'s first action via NativeGeometry.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.1.6(4),
printed p.408, and B.5.6(5), printed p.105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer.FixedPartEstimate

variable {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]
private abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

private noncomputable def movedSubrepresentation (σ : Representation (ZMod 2) K W) :
    Subrepresentation σ where
  toSubmodule := Coinvariants.ker σ
  apply_mem_toSubmodule g := by
    change Coinvariants.ker σ ≤ (Coinvariants.ker σ).comap (σ g)
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, w⟩, rfl⟩
    change σ g (σ k w - w) ∈ Coinvariants.ker σ
    convert Coinvariants.sub_mem_ker (ρ := σ) (g * k * g⁻¹) (σ g w) using 1
    simp [map_sub, ← Module.End.mul_apply, ← map_mul, mul_assoc]

private theorem moved_trivial_quotient (σ : Representation (ZMod 2) K W) :
    HasTrivialQuotient (movedSubrepresentation σ) :=
  fun g w => Coinvariants.sub_mem_ker (ρ := σ) g w

private theorem faithful_on_trivial_quotient_kernel [Finite K]
    (σ : Representation (ZMod 2) K W) (hf : Function.Injective σ)
    (N : Subrepresentation σ) (ht : HasTrivialQuotient N)
    (hcore : pCore 2 K = ⊥) : Function.Injective N.toRepresentation := by
  have hp : IsPGroup 2 N.toRepresentation.ker := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply hf
    ext v
    have hd := LinearMap.congr_fun (MonoidHom.mem_ker.mp x.property)
      (⟨σ x v - v, ht x v⟩ : N.toSubmodule)
    have hd' := congrArg Subtype.val hd
    change σ x (σ x v - v) = σ x v - v at hd'
    rw [map_sub] at hd'
    have htwo (w : W) : w + w = 0 := by
      simpa only [show (2 : ZMod 2) = 0 from by decide, zero_smul] using
        (@two_smul (ZMod 2) W _ _ _ w).symm
    have hv : σ x (σ x v) = v := by
      apply add_right_cancel (b := v)
      exact (sub_eq_sub_iff_add_eq_add.mp hd').trans ((htwo _).trans (htwo v).symm)
    change σ ((x : K) ^ (2 ^ 1)) v = σ (1 : K) v
    simpa only [pow_one, pow_two, map_mul, Module.End.mul_apply,
      map_one, Module.End.one_apply] using hv
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact le_bot_iff.mp ((show N.toRepresentation.ker ≤ pCore 2 K from
    le_sSup ⟨inferInstance, hp⟩).trans_eq hcore)

private theorem sl3_two_core (eK : K ≃* SL) : pCore 2 K = ⊥ := by
  let e := eK.trans Matrix.PSL3Two.equiv
  apply ((pCore 2 K).map_eq_bot_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso 2 e, Matrix.PSL3Two.pCore_two_PSL_eq_bot]

private theorem natural_marking [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) K W) (hf : Function.Injective σ)
    (eK : K ≃* SL) (hd : Module.finrank (ZMod 2) W = 3) :
    ∃ (a : K ≃* SL) (E : W ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      ∀ g v, E (σ g v) = specialLinearNatural (k := ZMod 2) 3 (a g) (E v) := by
  classical
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hd
  let E := b.equivFun
  let q : LinearMap.GeneralLinearGroup (ZMod 2) W ≃* SL :=
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv E).trans
      Matrix.GeneralLinearGroup.toLin.symm).trans Matrix.PSL3Two.equivGL.symm
  let f : K →* SL := q.toMonoidHom.comp σ.asGroupHom
  have hfi : Function.Injective f := by
    intro g h hgh
    apply hf
    exact congrArg Units.val (q.injective hgh)
  have hfs : Function.Surjective f := by
    have hh : Function.Surjective (f.comp eK.symm.toMonoidHom) :=
      Finite.surjective_of_injective (hfi.comp eK.symm.injective)
    intro g
    obtain ⟨h, hh⟩ := hh g
    exact ⟨eK.symm h, hh⟩
  refine ⟨MulEquiv.ofBijective f ⟨hfi, hfs⟩, E, ?_⟩
  intro g v
  change E (σ g v) = specialLinearNatural (k := ZMod 2) 3 (f g) (E v)
  have heq : Matrix.PSL3Two.equivGL (f g) = Matrix.GeneralLinearGroup.toLin.symm
      (LinearMap.GeneralLinearGroup.congrLinearEquiv E (σ.asGroupHom g)) := by
    simp only [f, q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hh := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) =>
    (Matrix.GeneralLinearGroup.toLin t : Module.End (ZMod 2) (Fin 3 → ZMod 2)) (E v)) heq
  rw [MulEquiv.apply_symm_apply] at hh
  rw [Matrix.PSL3Two.equivGL_apply] at hh
  change specialLinearNatural (k := ZMod 2) 3 (f g) (E v) = E (σ g (E.symm (E v))) at hh
  simpa only [E.symm_apply_apply] using hh.symm

private theorem fixed_involution_mem_moved_sup_fixed
    (σ : Representation (ZMod 2) K W) (N : Subrepresentation σ)
    (a : K ≃* SL) (E : N.toSubmodule ≃ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (he : ∀ g v, E (N.toRepresentation g v) =
      specialLinearNatural (k := ZMod 2) 3 (a g) (E v))
    (ht : HasTrivialQuotient N) (g : K) (hg : g ^ 2 = 1) (hne : g ≠ 1)
    (w : W) (hw : σ g w = w) : w ∈ N.toSubmodule ⊔ σ.invariants := by
  let T := cocyclesCongr N.toRepresentation (specialLinearNatural (k := ZMod 2) 3) a E he
  let f := displacementCocycle N ht w
  have hf : (T f).val (a g) = 0 := by
    change E (f.val (a.symm (a g))) = 0
    rw [a.symm_apply_apply]
    change E (⟨σ g w - w, ht g w⟩ : N.toSubmodule) = 0
    rw [show (⟨σ g w - w, ht g w⟩ : N.toSubmodule) = 0 by
      apply Subtype.ext
      exact sub_eq_zero.mpr hw, map_zero]
  obtain ⟨u, hu⟩ :=
    CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.Transfer.SpanBound.cocycle_principal_of_involution_zero
      (T f) (a g) (by rw [← map_pow, hg, map_one]) (by simpa using hne) hf
  change w ∈ N.toSubmodule ⊔ OneCohomology.fixed σ
  apply (extensionClass_eq_zero_iff N ht w).mp
  apply (classMap_eq_zero_iff N.toRepresentation f).mpr
  refine ⟨E.symm u, T.injective ?_⟩
  simpa only [T, cocyclesCongr_principal, E.apply_symm_apply] using hu

private theorem nonsplit_involution_codim [Finite K] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) K W) (hf : Function.Injective σ)
    (eK : K ≃* SL) (hd : Module.finrank (ZMod 2) (Coinvariants.ker σ) = 3)
    (hn : Coinvariants.ker σ ⊔ σ.invariants ≠ ⊤)
    (g : K) (hg : g ^ 2 = 1) (hne : g ≠ 1) :
    2 ≤ fixedCodim σ (Subgroup.zpowers g) := by
  let N := movedSubrepresentation σ
  have hNf : Function.Injective N.toRepresentation :=
    faithful_on_trivial_quotient_kernel σ hf N (moved_trivial_quotient σ) (sl3_two_core eK)
  obtain ⟨a, E, he⟩ := natural_marking N.toRepresentation hNf eK hd
  let H := N.toSubmodule ⊔ σ.invariants
  have hle : fixedSpace σ (Subgroup.zpowers g) ≤ H := by
    intro w hw
    exact fixed_involution_mem_moved_sup_fixed σ N a E he (moved_trivial_quotient σ)
      g hg hne w (hw ⟨g, Subgroup.mem_zpowers g⟩)
  have hlt : fixedSpace σ (Subgroup.zpowers g) < H := by
    apply lt_of_le_of_ne hle
    intro heq
    apply hne
    apply hNf
    rw [map_one]
    apply LinearMap.ext
    intro v
    have hv : v.val ∈ fixedSpace σ (Subgroup.zpowers g) :=
      heq.symm ▸ (show v.val ∈ H from
        (le_sup_left : N.toSubmodule ≤ H) v.property)
    exact Subtype.ext (hv ⟨g, Subgroup.mem_zpowers g⟩)
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  have hH := Submodule.finrank_lt (show H ≠ ⊤ from hn)
  have hcod := fixedCodim_add_finrank σ (Subgroup.zpowers g)
  omega

theorem nonsplit_rank_le_codim [Finite K] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) K W) (hf : Function.Injective σ)
    (eK : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hd : Module.finrank (ZMod 2) (Coinvariants.ker σ) = 3)
    (hn : Coinvariants.ker σ ⊔ σ.invariants ≠ ⊤)
    (A : Subgroup K) (hA : IsElementaryAbelian 2 A) : rank A ≤ fixedCodim σ A := by
  by_cases hbot : A = ⊥
  · subst A
    rw [Representation.BinaryOffender.rank_bot]
    exact Nat.zero_le _
  have hr : rank A ≤ 2 := by
    have hh := BinaryLinearThree.ResidualFFForms.ConstituentBudget.elementary_rank_le_two
      (A.map eK.toMonoidHom) (hA.map eK.toMonoidHom)
    rwa [rank_map_injective eK.toMonoidHom eK.injective] at hh
  have hex : ∃ g ∈ A, g ≠ (1 : K) := by
    by_contra! hh
    exact hbot (le_bot_iff.mp (fun g hg => hh g hg))
  obtain ⟨g, hg, hgne⟩ := hex
  let : IsElementaryAbelian 2 A := hA
  have htwo := nonsplit_involution_codim σ hf eK hd hn g
    (elemPow_eq_one_of_isElementaryAbelian g hg) hgne
  have hle := Submodule.finrank_mono
    (fixedSpace_antitone σ (Subgroup.zpowers_le.mpr hg))
  have hcodA := fixedCodim_add_finrank σ A
  have hcodg := fixedCodim_add_finrank σ (Subgroup.zpowers g)
  omega

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer.FixedPartEstimate

end
