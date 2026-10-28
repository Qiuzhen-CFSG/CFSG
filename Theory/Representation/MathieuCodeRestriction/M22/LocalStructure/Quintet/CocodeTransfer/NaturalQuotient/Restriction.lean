module

public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.Quotient
public import Theory.Representation.RepEquiv
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Restricting the six-point natural module at a fixed point

Delete the distinguished coordinate from an even word on six points and
pass to the deleted module on the other five points. The kernel is exactly
the constant line: parity determines the omitted coordinate. Equal dimensions
then give a linear equivalence. Its equivariance retains the actual embedding
of the five-point action in the six-point permutation group.

Source: Aschbacher--Smith, H.15.4, printed p.400; the binary permutation
module conventions are those of B.3.1.
-/

@[expose] public section

open scoped BigOperators
namespace BinaryPermutation.PointedSix
noncomputable section
variable {Ω : Type*} [Fintype Ω] (e : Fin 6 ≃ Ω)

def restrictFull : Full Ω →ₗ[ZMod 2] Full (Fin 5) where
  toFun v i := v (e i.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def restrictDeleted : Deleted Ω →ₗ[ZMod 2] Deleted (Fin 5) :=
  (constants Ω).mapQ (constants (Fin 5)) (restrictFull e) (by
    intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩)

def restrictNatural : natural Ω →ₗ[ZMod 2] natural (Fin 5) :=
  ((restrictDeleted e).comp (natural Ω).subtype).codRestrict _ (by
    intro v
    rw [natural_eq_top (Fin 5) (by decide)]
    trivial)

lemma restrictNatural_injective : Function.Injective (restrictNatural e) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  rintro ⟨x, w, hw, rfl⟩ hx
  have hr : restrictFull e w ∈ constants (Fin 5) :=
    (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hx)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hr
  have hs (i : Fin 5) : w (e i.succ) = c := by
    have h := congrFun hc i
    simpa [restrictFull, allOne] using h.symm
  have h0 : w (e 0) = c := by
    have hsum : ∑ i : Fin 6, w (e i) = 0 := (e.sum_comp w).trans hw
    rw [Fin.sum_univ_succ] at hsum
    simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsum
    have hc5 : (5 : ℕ) • c = c := by
      exact (by decide : ∀ c : ZMod 2, (5 : ℕ) • c = c) c
    rw [hc5] at hsum
    have hneg : -c = c := CharTwo.neg_eq c
    exact (eq_neg_of_add_eq_zero_left hsum).trans hneg
  have he : w = c • allOne Ω := by
    ext x
    obtain ⟨i,rfl⟩ := e.surjective x
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [allOne] using h0
    · simpa [allOne] using hs i
  apply Subtype.ext
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton.mpr ⟨c, he.symm⟩)

lemma restrictNatural_bijective : Function.Bijective (restrictNatural e) := by
  have hc : Fintype.card Ω = 6 := (Fintype.card_congr e).symm
  let : Nonempty Ω := ⟨e 0⟩
  have hd : Module.finrank (ZMod 2) (natural Ω) =
      Module.finrank (ZMod 2) (natural (Fin 5)) := by
    rw [finrank_natural_even Ω (by rw [hc]; decide),
      finrank_natural_odd (Fin 5) (by decide), hc]
    rfl
  exact ⟨restrictNatural_injective e,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp
      (restrictNatural_injective e)⟩

def naturalEquiv : natural Ω ≃ₗ[ZMod 2] natural (Fin 5) :=
  LinearEquiv.ofBijective (restrictNatural e) (restrictNatural_bijective e)

lemma naturalEquiv_equivariant (g : Equiv.Perm Ω) (h : Equiv.Perm (Fin 5))
    (hcompat : ∀ i : Fin 5, e (h i).succ = g (e i.succ))
    (v : natural Ω) :
    naturalEquiv e (naturalRepresentation Ω g v) =
      naturalRepresentation (Fin 5) h (naturalEquiv e v) := by
  obtain ⟨w,hw,he⟩ := v.property
  have hv : v = ⟨(constants Ω).mkQ w, w, hw, rfl⟩ := Subtype.ext he.symm
  subst v
  apply Subtype.ext
  change (constants (Fin 5)).mkQ (restrictFull e (representation Ω g w)) =
    (constants (Fin 5)).mkQ (representation (Fin 5) h (restrictFull e w))
  congr 1
  ext i
  change w (g.symm (e i.succ)) = w (e (h.symm i).succ)
  congr 1
  apply g.injective
  simpa using hcompat (h.symm i)
end
end BinaryPermutation.PointedSix
