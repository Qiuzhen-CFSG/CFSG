module
public import Theory.Representation.PSL3Two.FixedParabolicQuotient

/-!
# Fixed-free quotients of the point permutation module

The original point parabolic gives a permutation surjection with the specified
actor marking. Triviality of the fixed space kills the constant line. The three
submodules of the augmentation core then identify the whole target as the
natural three-space or the point core. This is the point counterpart of the
line quotient, used to compare the two original orbits under one marking.
Source: Aschbacher–Smith H.5.3 and 13.4.7, printed pp.385–386,901.
-/

public noncomputable section
open Representation Module Subgroup
namespace BinaryLinearThree.FanoPointFixedFree
open FanoDecomposition FanoCoreStructure
variable {A M : Type*} [_root_.Group A] [AddCommGroup M] [Module (ZMod 2) M]

local instance pointAction : MulAction Group Point := MulAction.compHom Point pointPerm
local instance pointTransitive : MulAction.IsPretransitive Group Point where
  exists_smul_eq x y := by
    obtain ⟨a,ha⟩ := SimpleHeadQuotientObstruction.point_reachable x
    obtain ⟨b,hb⟩ := SimpleHeadQuotientObstruction.point_reachable y
    refine ⟨b * a⁻¹, ?_⟩
    change pointPerm (b * a⁻¹) x = y
    rw [map_mul, Equiv.Perm.mul_apply, ←ha, map_inv, Equiv.Perm.inv_def,
      Equiv.symm_apply_apply, hb]

/-- The point parabolic gives a permutation quotient under the supplied marking. -/
theorem marked_quotient (f : A →* Group) (hf : Function.Surjective f)
    (P : Subgroup A) (hk : f.ker ≤ P) (hP : P.map f = Matrix.PSL3Two.pointParabolicSL)
    (ρ : Representation (ZMod 2) A M) (w : M) (hw : ∀ a : P, ρ a w = w)
    (hs : Submodule.span (ZMod 2) (Set.range (fun a : A => ρ a w)) = ⊤) :
    ∃ q : Representation.IntertwiningMap (pointRepresentation.comp f) ρ, Function.Surjective q := by
  classical
  have hfix : P.map f = MulAction.stabilizer Group Matrix.PSL3Two.flagPoint := by
    rw [hP]
    ext g
    exact FanoLocalStructure.ParabolicSpaces.mem_pointParabolic_iff_fixes_point g
  let E := MulAction.surjectiveCosetEquiv P f hf hk Matrix.PSL3Two.flagPoint hfix
  obtain ⟨q,hq,hm,he⟩ := exists_coset_orbit_map ρ P w hw hs
  let v : Point → M := fun l => q (Finsupp.single (E.symm l) 1)
  have hv (a : A) (l : Point) : v (pointPerm (f a) l) = ρ a (v l) := by
    have hE : E.symm (pointPerm (f a) l) = a • E.symm l := by
      apply E.injective
      rw [E.apply_symm_apply]
      exact (MulAction.surjectiveCosetEquiv_smul P f hf hk _ hfix a (E.symm l)).trans
        (congrArg (fun l : Point => f a • l) (E.apply_symm_apply l)) |>.symm
    change q (Finsupp.single (E.symm (pointPerm (f a) l)) 1) = _
    rw [hE]
    simpa only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single] using
      he a (Finsupp.single (E.symm l) 1)
  have hvspan : Submodule.span (ZMod 2) (Set.range v) = ⊤ := by
    apply top_unique
    rw [←hs]
    apply Submodule.span_mono
    rintro _ ⟨a,rfl⟩
    exact ⟨E (QuotientGroup.mk a),by
      change q (Finsupp.single (E.symm (E (QuotientGroup.mk a))) 1) = ρ a w
      rw [E.symm_apply_apply,hm]⟩
  exact ⟨BinaryPermutation.orbitQuotient ρ (pointPerm.comp f) v hv,
    BinaryPermutation.orbitQuotient_surjective ρ (pointPerm.comp f) v hv hvspan⟩

/-- Every nonzero quotient of the point core is natural or the whole core. -/
theorem core_models (f : A →* Group) (hf : Function.Surjective f)
    (ρ : Representation (ZMod 2) A M)
    (t : Representation.IntertwiningMap (U₂.comp f) ρ)
    (ht : Function.Surjective t) (hd : 0 < finrank (ZMod 2) M) :
    Nonempty (Representation.Equiv (W.comp f) ρ) ∨
      Nonempty (Representation.Equiv (U₂.comp f) ρ) := by
  let N : Subrepresentation U₂ := {
    toSubmodule := t.toLinearMap.ker
    apply_mem_toSubmodule g x hx := by
      obtain ⟨a,rfl⟩ := hf g
      change t ((U₂.comp f) a x) = 0
      rw [t.isIntertwining, show t x = 0 from hx, map_zero] }
  rcases pointCore_subrepresentations N with hn | hn | hn
  · have hk : t.toLinearMap.ker = ⊥ := congrArg Subrepresentation.toSubmodule hn
    exact Or.inr ⟨t.ofBijective ⟨LinearMap.ker_eq_bot.mp hk,ht⟩⟩
  · have hk : t.toLinearMap.ker = pointWeightedSum.toLinearMap.ker :=
      congrArg Subrepresentation.toSubmodule hn
    let e := pointWeightedSum.toLinearMap.quotKerEquivOfSurjective pointWeightedSum_surjective
    let z := pointWeightedSum.toLinearMap.ker.liftQ t.toLinearMap hk.ge
    let r := z.comp e.symm.toLinearMap
    have hr (x : Core) : r (pointWeightedSum x) = t x := by
      change z (e.symm (pointWeightedSum x)) = t x
      rw [show pointWeightedSum x = e (Submodule.Quotient.mk x) from rfl,e.symm_apply_apply]
      rfl
    let s : Representation.IntertwiningMap (W.comp f) ρ := {
      toLinearMap := r
      isIntertwining' a := by
        apply LinearMap.ext
        intro v
        obtain ⟨x,rfl⟩ := pointWeightedSum_surjective v
        change r (W (f a) (pointWeightedSum x)) = ρ a (r (pointWeightedSum x))
        rw [←pointWeightedSum.isIntertwining,hr,hr]
        exact IntertwiningMap.isIntertwining _ _ t a x }
    have hs : Function.Surjective s := by
      intro y
      obtain ⟨x,rfl⟩ := ht y
      exact ⟨pointWeightedSum x,hr x⟩
    have hi : Function.Injective s := by
      intro v w he
      obtain ⟨x,rfl⟩ := pointWeightedSum_surjective v
      obtain ⟨y,rfl⟩ := pointWeightedSum_surjective w
      change r (pointWeightedSum x) = r (pointWeightedSum y) at he
      rw [hr,hr] at he
      have hz : x - y ∈ t.toLinearMap.ker := by
        change t (x-y) = 0
        rw [map_sub,sub_eq_zero]
        exact he
      rw [hk] at hz
      change pointWeightedSum (x-y) = 0 at hz
      rwa [map_sub,sub_eq_zero] at hz
    exact Or.inl ⟨s.ofBijective ⟨hi,hs⟩⟩
  · have hz (x : Core) : t x = 0 := by
      have hx : x ∈ N := hn ▸ (show x ∈ (⊤ : Subrepresentation U₂) from trivial)
      exact hx
    have hzero : ∀ x : M, x = 0 := by
      intro x
      obtain ⟨y,rfl⟩ := ht x
      exact hz y
    let : Subsingleton M := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    simp only [finrank_zero_of_subsingleton] at hd
    omega

/-- Fixed-free point permutation quotients are natural or point-core modules. -/
theorem whole_models (f : A →* Group) (hf : Function.Surjective f)
    (ρ : Representation (ZMod 2) A M)
    (q : Representation.IntertwiningMap (pointRepresentation.comp f) ρ)
    (hq : Function.Surjective q) (hd : 0 < finrank (ZMod 2) M)
    (hfixed : ∀ m : M, (∀ a : A, ρ a m = m) → m = 0) :
    Nonempty (Representation.Equiv (W.comp f) ρ) ∨
      Nonempty (Representation.Equiv (U₂.comp f) ρ) := by
  have hconst : q (BinaryPermutation.allOne Point) = 0 := hfixed _ (by
    intro a
    rw [← q.isIntertwining]
    rfl)
  let t : Representation.IntertwiningMap (U₂.comp f) ρ := {
    toLinearMap := q.toLinearMap.comp (BinaryPermutation.core Point).subtype
    isIntertwining' a := by
      apply LinearMap.ext
      intro x
      exact IntertwiningMap.isIntertwining _ _ q a x.val }
  apply core_models f hf ρ t ?_ hd
  intro m
  obtain ⟨v,rfl⟩ := hq m
  refine ⟨(pointSplit v).1, ?_⟩
  have he := congrArg q (pointSplit.symm_apply_apply v)
  change q ((pointSplit v).1.val + (pointSplit v).2 • BinaryPermutation.allOne Point) = q v at he
  change q (pointSplit v).1.val = q v
  simpa only [map_add,map_smul,hconst,smul_zero,add_zero] using he

end BinaryLinearThree.FanoPointFixedFree
