module
public import Theory.Representation.PSL3Two.FanoLineQuotients
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The moved submodule of a Fano-line permutation quotient

The augmentation-core image of a surjective permutation-module map is
exactly the commutator subspace. Transitivity identifies the images of
all basis vectors modulo that subspace. Conversely, every displacement
lifts to an augmentation-zero vector.

The native three-submodule classification of the Fano core then identifies
this image, as a representation under the original actor, with either
the dual natural module or the six-dimensional line core. In particular
its dimension is three or six. The original surjection and every quotient
map are retained; no semisimplicity of the full permutation core is assumed.
Source: Aschbacher–Smith H.5.3, printed pp.385–386, used in 13.4.7 on
printed p.901. FixedParabolicQuotient and the original LinearFixedLine
consumer apply these facts to the source parabolic and fixed-line orbit.
-/

@[expose] public noncomputable section
open Representation Module
namespace BinaryLinearThree.FanoLineMoved
open FanoDecomposition FanoCoreStructure FanoLineQuotients Representation.BinaryOffender
local instance : Nonempty Line := ⟨Matrix.PSL3Two.flagLine⟩
variable {A M : Type*} [_root_.Group A] [AddCommGroup M] [Module (ZMod 2) M]
variable (f : A →* Group) (hf : Function.Surjective f) (ρ : Representation (ZMod 2) A M)
  (q : Representation.IntertwiningMap (lineRepresentation.comp f) ρ)

/-- The core restriction of the literal permutation quotient. -/
def coreMap : Representation.IntertwiningMap (lineCoreRepresentation.comp f) ρ where
  toLinearMap := q.toLinearMap.comp inclusion.toLinearMap
  isIntertwining' a := by
    apply LinearMap.ext
    intro v
    change q (inclusion (lineCoreRepresentation (f a) v)) = ρ a (q (inclusion v))
    rw [inclusion.isIntertwining]
    exact IntertwiningMap.isIntertwining _ _ q a (inclusion v)

include hf
/-- The augmentation-core image equals the full commutator subspace. -/
theorem core_image_eq_moved (hq : Function.Surjective q) :
    (coreMap f ρ q).range.toSubmodule = subspaceCommutator ρ ⊤ ⊤ := by
  classical
  let D := subspaceCommutator ρ ⊤ ⊤
  have hb (l : Line) : D.mkQ (q (Pi.single l 1)) =
      D.mkQ (q (Pi.single Matrix.PSL3Two.flagLine 1)) := by
    obtain ⟨g,hg⟩ := FanoLocalStructure.line_reachable l
    obtain ⟨a,rfl⟩ := hf g
    have he : lineRepresentation (f a) (Pi.single Matrix.PSL3Two.flagLine 1) =
        Pi.single l 1 := by
      rw [←hg]
      ext j
      simp [lineRepresentation,Pi.single_apply,Equiv.symm_apply_eq]
    rw [←he]
    change D.mkQ (q ((lineRepresentation.comp f) a (Pi.single Matrix.PSL3Two.flagLine 1))) = _
    rw [q.isIntertwining]
    apply (Submodule.Quotient.eq D).mpr
    exact Submodule.subset_span ⟨a,Subgroup.mem_top a,_,Submodule.mem_top,rfl⟩
  apply le_antisymm
  · rintro _ ⟨c,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero D).mp
    have hc : c.val = ∑ l : Line, c.val l • Pi.single l (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply]
    change D.mkQ (q (inclusion c)) = 0
    change D.mkQ (q c.val) = 0
    rw [hc,map_sum,map_sum]
    simp only [map_smul,hb]
    rw [←Finset.sum_smul,show (∑ l : Line, c.val l) = 0 from c.property,zero_smul]
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,_,v,_,rfl⟩
    obtain ⟨c,rfl⟩ := hq v
    have hc : lineRepresentation (f a) c - c ∈ BinaryPermutation.core Line := by
      change BinaryPermutation.augmentation Line _ = 0
      rw [map_sub]
      simp only [lineRepresentation,MonoidHom.comp_apply,BinaryPermutation.augmentation_permute,sub_self]
    refine ⟨⟨lineRepresentation (f a) c - c,hc⟩,?_⟩
    change q (lineRepresentation (f a) c - c) = ρ a (q c) - q c
    rw [map_sub]
    exact congrArg (fun m => m - q c) (IntertwiningMap.isIntertwining _ _ q a c)

private def coreKernel : Subrepresentation lineCoreRepresentation where
  toSubmodule := (coreMap f ρ q).toLinearMap.ker
  apply_mem_toSubmodule g c hc := by
    obtain ⟨a,rfl⟩ := hf g
    change coreMap f ρ q ((lineCoreRepresentation.comp f) a c) = 0
    rw [(coreMap f ρ q).isIntertwining,show coreMap f ρ q c = 0 from hc,map_zero]

private theorem kernel_ne_top (hq : Function.Surjective q)
    (hd : 1 < finrank (ZMod 2) M) : coreKernel f hf ρ q ≠ ⊤ := by
  intro he
  have hz (c : LineCore) : q (inclusion c) = 0 := by
    have hm : c ∈ coreKernel f hf ρ q := he ▸ Submodule.mem_top
    exact hm
  have hs : (⊤ : Submodule (ZMod 2) M) ≤
      Submodule.span (ZMod 2) {q (BinaryPermutation.allOne Line)} := by
    intro m _
    obtain ⟨c,rfl⟩ := hq m
    rw [←decomposition c,map_add,hz,zero_add,map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hh := Submodule.finrank_mono hs
  rw [finrank_top] at hh
  exact (not_le_of_gt hd) (hh.trans (by simpa using finrank_span_le_card ({q (BinaryPermutation.allOne Line)} : Set M)))

/-- A nontrivial-action quotient has a moved space of dimension three or six. -/
theorem moved_dimension (hq : Function.Surjective q)
    (hd : 1 < finrank (ZMod 2) M) :
    finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⊤) = 3 ∨
      finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⊤) = 6 := by
  have he := (coreMap f ρ q).toLinearMap.finrank_range_add_finrank_ker
  have hc : finrank (ZMod 2) LineCore = 6 := by
    rw [BinaryPermutation.finrank_core,Matrix.PSL3Two.Fano.card_line]
  rw [hc] at he
  have hr : finrank (ZMod 2) ((coreMap f ρ q).toLinearMap.range) =
      finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⊤) := by
    rw [←core_image_eq_moved f hf ρ q hq]
    rfl
  rw [hr] at he
  rcases lineCore_subrepresentations (coreKernel f hf ρ q) with hn | hn | hn
  · have hk : (coreMap f ρ q).toLinearMap.ker = ⊥ := congrArg Subrepresentation.toSubmodule hn
    rw [hk,finrank_bot] at he
    exact Or.inr (by omega)
  · have hk : (coreMap f ρ q).toLinearMap.ker = lineKernel.toSubmodule :=
      congrArg Subrepresentation.toSubmodule hn
    have hdim : finrank (ZMod 2) lineKernel.toSubmodule = 3 := by
      rw [←lineKernelEquiv.toLinearEquiv.finrank_eq]
      exact Module.finrank_fin_fun (ZMod 2)
    rw [hk,hdim] at he
    exact Or.inl (by omega)
  · exact False.elim (kernel_ne_top f hf ρ q hq hd hn)
end BinaryLinearThree.FanoLineMoved

@[expose] public noncomputable section
open Representation Module
namespace BinaryLinearThree.FanoLineMoved
open FanoDecomposition FanoCoreStructure FanoLineQuotients Representation.BinaryOffender
local instance : Nonempty Line := ⟨Matrix.PSL3Two.flagLine⟩
variable {A M : Type*} [_root_.Group A] [AddCommGroup M] [Module (ZMod 2) M]
variable (f : A →* Group) (hf : Function.Surjective f) (ρ : Representation (ZMod 2) A M)
  (q : Representation.IntertwiningMap (lineRepresentation.comp f) ρ)

include hf
/-- The moved space has the actual dual-natural or indecomposable Fano-core action. -/
theorem core_image_models (hq : Function.Surjective q)
    (hd : 1 < finrank (ZMod 2) M) :
    Nonempty (Representation.Equiv (W.dual.comp f) (coreMap f ρ q).range.toRepresentation) ∨
    Nonempty (Representation.Equiv (lineCoreRepresentation.comp f)
      (coreMap f ρ q).range.toRepresentation) := by
  let t := coreMap f ρ q
  let R := t.range
  let c : Representation.IntertwiningMap (lineCoreRepresentation.comp f) R.toRepresentation := {
    toLinearMap := t.toLinearMap.rangeRestrict
    isIntertwining' a := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact IntertwiningMap.isIntertwining _ _ t a x }
  have hcs : Function.Surjective c := by
    rintro ⟨y,x,rfl⟩
    exact ⟨x,rfl⟩
  rcases lineCore_subrepresentations (coreKernel f hf ρ q) with hn | hn | hn
  · have hk : t.toLinearMap.ker = ⊥ := congrArg Subrepresentation.toSubmodule hn
    have hi : Function.Injective c := fun x y he =>
      (LinearMap.ker_eq_bot.mp hk) (congrArg Subtype.val he)
    exact Or.inr ⟨c.ofBijective ⟨hi,hcs⟩⟩
  · have hk : t.toLinearMap.ker = lineWeightedSum.toLinearMap.ker :=
      congrArg Subrepresentation.toSubmodule hn
    have hkc : lineWeightedSum.toLinearMap.ker ≤ c.toLinearMap.ker := by
      intro x hx
      apply Subtype.ext
      change t x = 0
      exact (show x ∈ t.toLinearMap.ker from hk.symm ▸ hx)
    let e := lineWeightedSum.toLinearMap.quotKerEquivOfSurjective lineWeightedSum_surjective
    let z := lineWeightedSum.toLinearMap.ker.liftQ c.toLinearMap hkc
    let r := z.comp e.symm.toLinearMap
    have hr (x : LineCore) : r (lineWeightedSum x) = c x := by
      change z (e.symm (lineWeightedSum x)) = c x
      rw [show lineWeightedSum x = e (Submodule.Quotient.mk x) from rfl,e.symm_apply_apply]
      rfl
    let s : Representation.IntertwiningMap (W.dual.comp f) R.toRepresentation := {
      toLinearMap := r
      isIntertwining' a := by
        apply LinearMap.ext
        intro φ
        obtain ⟨x,rfl⟩ := lineWeightedSum_surjective φ
        change r (W.dual (f a) (lineWeightedSum x)) = R.toRepresentation a (r (lineWeightedSum x))
        rw [←lineWeightedSum.isIntertwining,hr,hr]
        exact IntertwiningMap.isIntertwining _ _ c a x }
    have hs : Function.Surjective s := by
      intro y
      obtain ⟨x,rfl⟩ := hcs y
      exact ⟨lineWeightedSum x,hr x⟩
    have hi : Function.Injective s := by
      intro φ ψ he
      obtain ⟨x,rfl⟩ := lineWeightedSum_surjective φ
      obtain ⟨y,rfl⟩ := lineWeightedSum_surjective ψ
      change r (lineWeightedSum x) = r (lineWeightedSum y) at he
      rw [hr,hr] at he
      have hz : x - y ∈ t.toLinearMap.ker := by
        change t (x-y) = 0
        rw [map_sub,sub_eq_zero]
        exact congrArg Subtype.val he
      rw [hk] at hz
      change lineWeightedSum (x-y) = 0 at hz
      rwa [map_sub,sub_eq_zero] at hz
    exact Or.inl ⟨s.ofBijective ⟨hi,hs⟩⟩
  · exact False.elim (kernel_ne_top f hf ρ q hq hd hn)
end BinaryLinearThree.FanoLineMoved
