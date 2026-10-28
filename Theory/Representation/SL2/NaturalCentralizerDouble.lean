module
public import Theory.Representation.SL2.NaturalHomogeneous
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Two identical summands for a natural component centralizer

The two SL₂ root displacements satisfy r² = s² = 0 and rs + sr = 1
on every natural copy. Homogeneity extends these identities to the whole
module. Their kernel and image give an actual decomposition into two
isomorphic modules for every commuting action, allowing arbitrary mixing
among the original natural copies.

The literal Chapter 10 action-kernel consumer uses this to turn a cubic
actor into an FF-offender on one summand. Source: Aschbacher--Smith,
D.3.9(2) and D.3.21, printed pp.200--201,205--206.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender
namespace Representation
variable {C V : Type*} [Group C] [AddCommGroup V] [Module (ZMod 2) V]

private theorem double_of_square_zero_pair
    (ρ : Representation (ZMod 2) C V) (r s : Module.End (ZMod 2) V)
    (hr : ∀ v, r (r v) = 0) (hs : ∀ v, s (s v) = 0)
    (hpair : ∀ v, r (s v) + s (r v) = v)
    (hcr : ∀ c v, r (ρ c v) = ρ c (r v))
    (hcs : ∀ c v, s (ρ c v) = ρ c (s v)) :
    ∃ U : Subrepresentation ρ, Nonempty (ρ.Equiv (U.toRepresentation.prod U.toRepresentation)) := by
  let U : Subrepresentation ρ := {
    toSubmodule := r.ker
    apply_mem_toSubmodule c v hv := by
      change r (ρ c v) = 0
      rw [hcr,show r v = 0 from hv,map_zero] }
  have hrs (v : U.toSubmodule) : r (s v) = v := by
    have h := hpair v
    rw [show r v = 0 from v.property,map_zero,add_zero] at h
    exact h
  let e : V ≃ₗ[ZMod 2] U.toSubmodule × U.toSubmodule := {
    toFun v := (⟨r v,hr v⟩,⟨r (s v),hr (s v)⟩)
    invFun w := s w.1 + w.2
    left_inv v := by
      change s (r v) + r (s v) = v
      rw [add_comm,hpair]
    right_inv w := by
      apply Prod.ext
      · apply Subtype.ext
        change r (s w.1 + w.2) = w.1
        rw [map_add,hrs,show r w.2 = 0 from w.2.property,add_zero]
      · apply Subtype.ext
        change r (s (s w.1 + w.2)) = w.2
        rw [map_add,hs,zero_add,hrs]
    map_add' x y := by ext <;> simp [map_add]
    map_smul' a v := by ext <;> simp [map_smul] }
  refine ⟨U,⟨.mk e ?_⟩⟩
  intro c
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · exact Subtype.ext (hcr c v)
  · exact Subtype.ext (by change r (s (ρ c v)) = ρ c (r (s v)); rw [hcs,hcr])
end Representation

open scoped MatrixGroups
namespace Representation.SL2AutomorphismNatural
open Representation.BinaryOffender.Homogeneous
variable {F K C V : Type*} [Field F] [CharP F 2] [Group K] [Group C]
  [AddCommGroup V] [Module (ZMod 2) V]
local instance naturalCentralizerDoubleAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- A commuting action on a homogeneous natural SL₂ module is a double
of one actual invariant subspace. No invariant natural copy is assumed. -/
theorem natural_commuting_double
    (σ : Representation (ZMod 2) K V) (q : K →* SL(2,F))
    (hq : Function.Surjective q)
    (I : Subrepresentation σ) (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ k v, E ((q k).val.mulVec v) = I.toRepresentation k (E v))
    (hhom : homogeneousPart I ⊤ = ⊤)
    (τ : Representation (ZMod 2) C V)
    (hcomm : ∀ c k v, τ c (σ k v) = σ k (τ c v)) :
    ∃ U : Subrepresentation τ, Nonempty (τ.Equiv (U.toRepresentation.prod U.toRepresentation)) := by
  let a : SL(2,F) := ⟨!![1,1;0,1],by simp [Matrix.det_fin_two]⟩
  let b : SL(2,F) := ⟨!![1,0;1,1],by simp [Matrix.det_fin_two]⟩
  obtain ⟨u,hu⟩ := hq a
  obtain ⟨v,hv⟩ := hq b
  let r := σ u - 1
  let s := σ v - 1
  let Z := (r * r).ker ⊓ (s * s).ker ⊓ (r * s + s * r - 1).ker
  have hZ : homogeneousPart I ⊤ ≤ Z := by
    apply iSup_le
    intro J
    apply iSup_le
    rintro ⟨_,hJ⟩
    obtain ⟨e,he⟩ := hJ
    let E' := E.trans e
    have hE' (k : K) (w : Fin 2 → F) :
        E' ((q k).val.mulVec w) = J.toRepresentation k (E' w) := by
      change e (E ((q k).val.mulVec w)) = _
      rw [hE,he]
      rfl
    have hr' (w : Fin 2 → F) : r (E' w : V) = (E' ![w 1,0] : V) := by
      change σ u (E' w : V) - (E' w : V) = _
      have hh := congrArg (fun z : J.toSubmodule => (z : V)) (hE' u w)
      change (E' ((q u).val.mulVec w) : V) = σ u (E' w) at hh
      rw [hu] at hh
      rw [←hh,←Submodule.coe_sub,←map_sub]
      congr 2
      ext i
      fin_cases i <;> simp [a,dotProduct,Fin.sum_univ_two]
    have hs' (w : Fin 2 → F) : s (E' w : V) = (E' ![0,w 0] : V) := by
      change σ v (E' w : V) - (E' w : V) = _
      have hh := congrArg (fun z : J.toSubmodule => (z : V)) (hE' v w)
      change (E' ((q v).val.mulVec w) : V) = σ v (E' w) at hh
      rw [hv] at hh
      rw [←hh,←Submodule.coe_sub,←map_sub]
      congr 2
      ext i
      fin_cases i <;> simp [b,dotProduct,Fin.sum_univ_two]
    intro w hw
    obtain ⟨x,hx⟩ := E'.surjective ⟨w,hw⟩
    have hx' : (E' x : V) = w := congrArg Subtype.val hx
    rw [←hx']
    refine ⟨⟨?_,?_⟩,?_⟩
    · change r (r (E' x)) = 0
      rw [hr',hr']
      simp
    · change s (s (E' x)) = 0
      rw [hs',hs']
      simp
    · change r (s (E' x)) + s (r (E' x)) - (E' x : V) = 0
      rw [hs',hr',hr',hs']
      rw [←Submodule.coe_add,←map_add]
      apply sub_eq_zero.mpr
      congr 2
      ext i
      fin_cases i <;> simp
  have htop : ∀ w : V, w ∈ Z := fun w => hZ (hhom.symm ▸ Submodule.mem_top)
  apply double_of_square_zero_pair τ r s
    (fun w => (htop w).1.1) (fun w => (htop w).1.2)
    (fun w => sub_eq_zero.mp (htop w).2)
  · intro c w
    change σ u (τ c w) - τ c w = τ c (σ u w - w)
    rw [map_sub,hcomm]
  · intro c w
    change σ v (τ c w) - τ c w = τ c (σ v w - w)
    rw [map_sub,hcomm]
end Representation.SL2AutomorphismNatural
