module
public import Theory.Representation.PSL3Two.NaturalDualCentralizer
public import Theory.Representation.Quotient
public import Theory.Representation.ElementaryPerfectSplit

/-!
# Sums of oppositely marked natural modules

The natural and dual binary three-spaces are irreducible and inequivalent
under the same surjective actor map. Their injective images therefore have
zero intersection. Addition identifies their spanning sum with the actual
natural-plus-dual representation, without an assumed disjointness premise.
The original fixed-line application is Amalgam/LinearOrbitSum.
Source: Aschbacher–Smith 13.4.7, printed p.901.
-/

public noncomputable section
open Representation
namespace BinaryLinearThree.NaturalDualSum
variable {A M : Type*} [_root_.Group A] [AddCommGroup M] [Module (ZMod 2) M]

/-- Opposite natural embeddings under the same actor have disjoint ranges. -/
theorem intersection_zero (f : A →* Group) (hf : Function.Surjective f)
    (ρ : Representation (ZMod 2) A M)
    (i : Representation.IntertwiningMap (W.comp f) ρ) (hi : Function.Injective i)
    (j : Representation.IntertwiningMap (W.dual.comp f) ρ) (hj : Function.Injective j)
    (v : Vector) (w : Module.Dual (ZMod 2) Vector) (h : i v = j w) : v = 0 ∧ w = 0 := by
  let I : Subrepresentation (W.comp f) := {
    toSubmodule := j.range.toSubmodule.comap i.toLinearMap
    apply_mem_toSubmodule a x hx := by
      change i ((W.comp f) a x) ∈ j.range.toSubmodule
      rw [i.isIntertwining]
      exact j.range.apply_mem_toSubmodule a hx }
  let : IsIrreducible (W.comp f) :=
    (irreducible_comp_surjective_iff f hf W).mpr IrreducibleCatalogue.natural_irreducible
  let : IsIrreducible (W.dual.comp f) :=
    (irreducible_comp_surjective_iff f hf W.dual).mpr IrreducibleCatalogue.dual_irreducible
  rcases eq_bot_or_eq_top I with hI | hI
  · have hv : v ∈ I := ⟨w,h.symm⟩
    rw [hI] at hv
    have hv0 : v = 0 := hv
    exact ⟨hv0,hj (h.symm.trans (by rw [hv0,map_zero,map_zero]))⟩
  · let e := LinearEquiv.ofInjective j.toLinearMap hj
    let t := e.symm.toLinearMap.comp (i.toLinearMap.codRestrict j.range.toSubmodule
      (fun x => by change x ∈ I; rw [hI]; trivial))
    have ht (x : Vector) : j (t x) = i x := congrArg Subtype.val (e.apply_symm_apply _)
    let s : Representation.IntertwiningMap (W.comp f) (W.dual.comp f) := {
      toLinearMap := t
      isIntertwining' a := by
        apply LinearMap.ext
        intro x
        apply hj
        change j (t ((W.comp f) a x)) = j ((W.dual.comp f) a (t x))
        rw [ht,j.isIntertwining,ht,i.isIntertwining] }
    have hs : s ≠ 0 := by
      intro hz
      obtain ⟨x,hx⟩ := exists_ne (0 : Vector)
      have ht0 : t x = 0 := congrArg (fun q : Representation.IntertwiningMap
        (W.comp f) (W.dual.comp f) => q x) hz
      have hx0 : i x = i 0 := (ht x).symm.trans (by rw [ht0,map_zero,map_zero])
      exact hx (hi hx0)
    rcases IsIrreducible.bijective_or_eq_zero s with hb | hz
    · let E := s.ofBijective hb
      apply False.elim
      apply AutomorphismAction.natural_not_equiv_dual
      refine ⟨{ toLinearEquiv := E.toLinearEquiv, isIntertwining' := ?_ }⟩
      intro g
      obtain ⟨a,rfl⟩ := hf g
      exact E.isIntertwining' a
    · exact (hs hz).elim

/-- Addition is injective for the two oppositely marked natural images. -/
theorem sum_injective (f : A →* Group) (hf : Function.Surjective f)
    (ρ : Representation (ZMod 2) A M)
    (i : Representation.IntertwiningMap (W.comp f) ρ) (hi : Function.Injective i)
    (j : Representation.IntertwiningMap (W.dual.comp f) ρ) (hj : Function.Injective j) :
    Function.Injective (i.toLinearMap.coprod j.toLinearMap) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  rintro ⟨v,w⟩ h
  change i v + j w = 0 at h
  have hh : i v = j (-w) := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h
  obtain ⟨hv,hw⟩ := intersection_zero f hf ρ i hi j hj v (-w) hh
  exact Prod.ext hv (neg_eq_zero.mp hw)

/-- When the two images span, their actual sum is the six-dimensional
natural-plus-dual representation. -/
theorem equiv_of_spanning_sum (f : A →* Group) (hf : Function.Surjective f)
    (ρ : Representation (ZMod 2) A M)
    (i : Representation.IntertwiningMap (W.comp f) ρ) (hi : Function.Injective i)
    (j : Representation.IntertwiningMap (W.dual.comp f) ρ) (hj : Function.Injective j)
    (hs : Function.Surjective (i.toLinearMap.coprod j.toLinearMap)) :
    Nonempty (Representation.Equiv ((W.prod W.dual).comp f) ρ) ∧
      Module.finrank (ZMod 2) M = 6 := by
  let t : Representation.IntertwiningMap ((W.prod W.dual).comp f) ρ := {
    toLinearMap := i.toLinearMap.coprod j.toLinearMap
    isIntertwining' a := by
      apply LinearMap.ext
      rintro ⟨v,w⟩
      change i ((W.comp f) a v) + j ((W.dual.comp f) a w) = ρ a (i v + j w)
      rw [i.isIntertwining,j.isIntertwining,map_add] }
  let e := t.ofBijective ⟨sum_injective f hf ρ i hi j hj,hs⟩
  refine ⟨⟨e⟩,e.toLinearEquiv.finrank_eq.symm.trans ?_⟩
  rw [Module.finrank_prod,Subspace.dual_finrank_eq]
  simp [Vector]

end BinaryLinearThree.NaturalDualSum

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace BinaryLinearThree.NaturalDualSum
variable {G : Type*} [_root_.Group G] [Finite G] {C E U₁ U₂ : Subgroup G}
    [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 U₁] [IsElementaryAbelian 2 U₂]

/-- The comparison for actual invariant elementary subgroups, retaining the
literal common actor and conjugation action. -/
theorem subgroup_sum (f : C →* Group) (hf : Function.Surjective f)
    (hCE : C ≤ normalizer (E : Set G))
    (hC₁ : C ≤ normalizer (U₁ : Set G)) (hC₂ : C ≤ normalizer (U₂ : Set G))
    (hs : U₁ ⊔ U₂ = E)
    (e₁ : Representation.Equiv (W.comp f)
      (Representation.elementaryRepresentation (p := 2)
        (U₁.normalizerMonoidHom.comp (inclusion hC₁))))
    (e₂ : Representation.Equiv (W.dual.comp f)
      (Representation.elementaryRepresentation (p := 2)
        (U₂.normalizerMonoidHom.comp (inclusion hC₂)))) :
    U₁ ⊓ U₂ = ⊥ ∧
      Nonempty (Representation.Equiv ((W.prod W.dual).comp f)
        (Representation.elementaryRepresentation (p := 2)
          (E.normalizerMonoidHom.comp (inclusion hCE)))) ∧ Nat.card E = 64 := by
  let ρ := Representation.elementaryRepresentation (p := 2)
    (E.normalizerMonoidHom.comp (inclusion hCE))
  let ρ₁ := Representation.elementaryRepresentation (p := 2)
    (U₁.normalizerMonoidHom.comp (inclusion hC₁))
  let ρ₂ := Representation.elementaryRepresentation (p := 2)
    (U₂.normalizerMonoidHom.comp (inclusion hC₂))
  have h₁ : U₁ ≤ E := hs ▸ le_sup_left
  have h₂ : U₂ ≤ E := hs ▸ le_sup_right
  let i₀ : ρ₁.IntertwiningMap ρ := {
    toLinearMap := (inclusion h₁).toAdditive.toZModLinearMap 2
    isIntertwining' c := by apply LinearMap.ext; intro x; rfl }
  let j₀ : ρ₂.IntertwiningMap ρ := {
    toLinearMap := (inclusion h₂).toAdditive.toZModLinearMap 2
    isIntertwining' c := by apply LinearMap.ext; intro x; rfl }
  let i := i₀.comp e₁.toIntertwiningMap
  let j := j₀.comp e₂.toIntertwiningMap
  have hi : Function.Injective i := (inclusion_injective h₁).comp e₁.injective
  have hj : Function.Injective j := (inclusion_injective h₂).comp e₂.injective
  have hdis : U₁ ⊓ U₂ = ⊥ := by
    apply bot_unique
    intro x hx
    let v := e₁.symm (Additive.ofMul ⟨x,hx.1⟩)
    let w := e₂.symm (Additive.ofMul ⟨x,hx.2⟩)
    have he : i v = j w := by
      change i₀ (e₁ (e₁.symm _)) = j₀ (e₂ (e₂.symm _))
      rw [e₁.apply_symm_apply,e₂.apply_symm_apply]
      rfl
    have hv := (intersection_zero f hf ρ i hi j hj v w he).1
    have hzero := congrArg (fun a => (e₁ a).toMul.val) hv
    simp only [v,e₁.apply_symm_apply,map_zero] at hzero
    change x = 1 at hzero
    exact hzero
  have hspan : Function.Surjective (i.toLinearMap.coprod j.toLinearMap) := by
    let P := U₁.subgroupOf E
    let Q := U₂.subgroupOf E
    have hPQ : P ⊔ Q = ⊤ := by
      apply map_injective E.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le h₁,map_subgroupOf_eq_of_le h₂,
        ←MonoidHom.range_eq_map,range_subtype,hs]
    intro w
    obtain ⟨a,ha,b,hb,hab⟩ := mem_sup_of_normal_left.mp (hPQ ▸ mem_top w.toMul)
    refine ⟨(e₁.symm (Additive.ofMul ⟨a.val,ha⟩),
      e₂.symm (Additive.ofMul ⟨b.val,hb⟩)),?_⟩
    change i₀ (e₁ (e₁.symm _)) + j₀ (e₂ (e₂.symm _)) = w
    rw [e₁.apply_symm_apply,e₂.apply_symm_apply]
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Subtype.val hab
  obtain ⟨he,hd⟩ := equiv_of_spanning_sum f hf ρ i hi j hj hspan
  refine ⟨hdis,he,?_⟩
  calc
    Nat.card E = Nat.card (Additive E) := rfl
    _ = 2 ^ Module.finrank (ZMod 2) (Additive E) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    _ = 64 := by rw [hd]; rfl

end BinaryLinearThree.NaturalDualSum
