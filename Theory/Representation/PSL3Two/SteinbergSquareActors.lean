module
public import Theory.Representation.PSL3Two.SteinbergSquare
public import Theory.Representation.BinaryOffender.TwoSectionBudget
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant

/-!
# Excluding Steinberg-square constituents with the original cubic actor

The Steinberg-square obstruction passes through a full action kernel when
the specified elementary actor acts faithfully on the normal square. Its
rank and fixed codimension are preserved in the faithful image.

For an embedded constituent, the square automorphism bound limits ambient
displacement to eight. Its degree64 forces stability under the actor. On
the join of that actor and the normal square, the same budget then contradicts
the Steinberg-square normal-extension theorem. Neither ambient faithfulness
nor constituent stability is an extra premise.

Source: Aschbacher--Smith D.3.7--9, printed pp.197--200. The literal
Chapter10 seed application is ModuleChoice.QuietSeedTensor.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.QuadraticFourGroup.TensorClassification
namespace BinaryLinearThree.SteinbergSquare

/-- The Steinberg-square obstruction retains the specified faithful actor
when the whole ambient action has a kernel. -/
theorem actor_budget_impossible
    {H V : Type*} [_root_.Group H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V)
    (i : (Group × Group) →* H) [i.range.Normal]
    (hf : Function.Injective (ρ.comp i))
    (hirr : Representation.IsIrreducible (ρ.comp i))
    (e : Representation.Equiv (ρ.comp i) (externalTensor S S))
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hAC : A ⊓ centralizer (i.range : Set H) = ⊥)
    (hc : IsCubic ρ A) (hb : fixedCodim ρ A ≤ 2 * rank A) : False := by
  have hfaithN : ∀ n ∈ i.range, (∀ v, ρ n v = v) → n = 1 := by
    rintro _ ⟨g,rfl⟩ hg
    have he : g = 1 := hf (by
      rw [map_one]
      exact LinearMap.ext hg)
    rw [he,map_one]
  have hfaithA : ∀ a ∈ A, (∀ v, ρ a v = v) → a = 1 := by
    have h := actor_faithful_on_section ρ i.range A ⊤
      (by intro n hn v; simp)
      (fun n hn h => hfaithN n hn (fun v => h v Submodule.mem_top))
      (by rw [normalizer_eq_top]; exact le_top) hAC
    exact fun a ha hv => h a ha (fun v _ => hv v)
  let σ := imageRepresentation ρ
  let q := actionHom ρ
  let j := q.comp i
  have hj : Function.Injective j := by
    intro x y hxy
    apply hf
    exact congrArg σ hxy
  have hr : j.range = i.range.map q := MonoidHom.range_comp q i
  let : j.range.Normal := by
    rw [hr]
    exact Normal.map inferInstance q ρ.asGroupHom.rangeRestrict_surjective
  have hcu : cubicRatio σ ≤ 2 := by
    refine (cubicRatio_le_nat_iff σ 2).mpr
      ⟨actionSubgroup ρ A,hA.actionSubgroup ρ hfaithA,
        hc.map_equivariant ρ σ q (LinearEquiv.refl _ _) (fun _ _ => rfl),?_⟩
    rw [fixedCodim_actionSubgroup,actionSubgroup_rank ρ A hfaithA]
    exact hb
  exact not_cubic_normal_extension σ (imageRepresentation_injective ρ) j hj hirr e hcu

/-- A faithfully marked Steinberg-square constituent cannot occur under a
faithful elementary-actor cubic budget on the ambient space. Stability of the
constituent is deduced from its degree and the square automorphism rank. -/
theorem constituent_impossible
    {H V W : Type*} [_root_.Group H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H V)
    (i : (Group × Group) →* H) (hi : Function.Injective i) [i.range.Normal]
    (σ : Representation (ZMod 2) (Group × Group) W)
    (hσ : Function.Injective σ) (hirr : σ.IsIrreducible)
    (b : σ.Equiv (externalTensor S S))
    (f : σ.IntertwiningMap (ρ.comp i)) (hf : Function.Injective f)
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hAC : A ⊓ centralizer (i.range : Set H) = ⊥)
    (hc : IsCubic ρ A) (hb : fixedCodim ρ A ≤ 2 * rank A) : False := by
  let N := i.range
  let e : N ≃* (Group × Group) := (MonoidHom.ofInjective hi).symm
  let U : Subrepresentation (ρ.comp N.subtype) := {
    toSubmodule := f.range.toSubmodule
    apply_mem_toSubmodule g v hv := by
      obtain ⟨k,hk⟩ := g.property
      change ρ g.val v ∈ f.range.toSubmodule
      rw [←hk]
      exact f.range.apply_mem_toSubmodule k hv }
  let d : W ≃ₗ[ZMod 2] U.toSubmodule := LinearEquiv.ofInjective f.toLinearMap hf
  let eU : Representation.Equiv (σ.comp e.toMonoidHom) U.toRepresentation := .mk d (by
    intro g
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have he : i (e g) = (g : H) := congrArg Subtype.val
      ((MonoidHom.ofInjective hi).apply_symm_apply g)
    change f (σ (e g) w) = ρ g.val (f w)
    rw [←he]
    exact LinearMap.congr_fun (f.isIntertwining' (e g)) w)
  have hiU : U.toRepresentation.IsIrreducible :=
    (RepEquiv.ofRepresentationEquiv eU.symm).irreducible_of_euqiv
      ((irreducible_comp_surjective_iff e.toMonoidHom e.surjective σ).mpr hirr)
  let c : Group ≃* BinaryTensorThree.Factor := Matrix.PSL3Two.equivGL.trans
    ((Matrix.GeneralLinearGroup.toLin (n := Fin 3) (R := ZMod 2)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryTensorThree.Natural))
  have hr := BinaryTensorThree.rank_le_four_of_faithful_on_tensor_base N A hA hAC
    (e.trans (c.prodCongr c))
  have hd : Module.finrank (ZMod 2) U.toSubmodule = 64 := by
    rw [←d.finrank_eq,b.toLinearEquiv.finrank_eq,Module.finrank_tensorProduct,finrank_steinberg]
  have hstable : ∀ a ∈ A, U.toSubmodule.map (ρ a) = U.toSubmodule := by
    intro a ha
    apply map_constituent_eq_self_of_displacement_lt ρ N a U hiU
    have hh := NaturalTensor.operatorFixedCodim_le_fixedCodim ρ A ha
    change NaturalTensor.operatorFixedCodim (ρ a) < Module.finrank (ZMod 2) U.toSubmodule
    rw [hd]
    omega
  let J := A ⊔ N
  have hAJ : A ≤ J := le_sup_left
  have hNJ : N ≤ J := le_sup_right
  let U' : Subrepresentation (ρ.comp J.subtype) := {
    toSubmodule := U.toSubmodule
    apply_mem_toSubmodule g v hv := by
      obtain ⟨a,ha,n,hn,hg⟩ := mem_sup_of_normal_right.mp g.property
      change ρ g.val v ∈ U.toSubmodule
      rw [←hg,map_mul,Module.End.mul_apply,←hstable a ha]
      exact ⟨ρ n v,U.apply_mem_toSubmodule ⟨n,hn⟩ hv,rfl⟩ }
  let j : (Group × Group) →* J := i.codRestrict J (fun g => hNJ ⟨g,rfl⟩)
  have hjr : j.range = N.subgroupOf J := by
    ext g
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x,rfl⟩
    · rintro ⟨x,hx⟩
      exact ⟨x,Subtype.ext hx⟩
  let : j.range.Normal := hjr.symm ▸ inferInstanceAs (N.subgroupOf J).Normal
  let τ := U'.toRepresentation
  let d' : σ.Equiv (τ.comp j) := .mk d (by
    intro g
    apply LinearMap.ext
    intro w
    exact Subtype.ext (LinearMap.congr_fun (f.isIntertwining' g) w))
  have hτ : Function.Injective (τ.comp j) := by
    intro x y he
    apply hσ
    apply LinearMap.ext
    intro w
    apply d.injective
    exact (LinearMap.congr_fun (d'.isIntertwining' x) w).trans
      ((LinearMap.congr_fun he (d w)).trans (LinearMap.congr_fun (d'.isIntertwining' y) w).symm)
  have hiτ : Representation.IsIrreducible (τ.comp j) :=
    (RepEquiv.ofRepresentationEquiv d'.symm).irreducible_of_euqiv hirr
  let A' := A.subgroupOf J
  let : IsElementaryAbelian 2 A := hA.2
  have hA' : IsElementaryTwo A' := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hAJ⟩
    intro hz
    apply hA.1
    have hh := congrArg (map J.subtype) hz
    simpa only [A',map_subgroupOf_eq_of_le hAJ,Subgroup.map_bot] using hh
  have hAC' : A' ⊓ centralizer (j.range : Set J) = ⊥ := by
    rw [hjr]
    apply bot_unique
    rintro a ⟨ha,hcent⟩
    apply mem_bot.mpr
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hAC]
    exact ⟨ha,fun n hn => congrArg Subtype.val (hcent ⟨n,hNJ hn⟩ hn)⟩
  have hc' : IsCubic τ A' := cubic_subrepresentation (ρ.comp J.subtype) U'
    (fun a ha b hb c hc' v => hc a ha b hb c hc' v)
  have hb' : fixedCodim τ A' ≤ 2 * rank A' := by
    rw [rank_subgroupOf hAJ]
    have hh := fixedCodim_subrepresentation_le (ρ.comp J.subtype) U' A'
    rw [fixedCodim_subgroupOf ρ hAJ] at hh
    exact hh.trans hb
  exact actor_budget_impossible τ j hτ hiτ (d'.symm.trans b) A' hA' hAC' hc' hb'

end BinaryLinearThree.SteinbergSquare
