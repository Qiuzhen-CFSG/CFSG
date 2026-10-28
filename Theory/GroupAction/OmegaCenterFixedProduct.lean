module

public import Stellmacher.OmegaOneCenterMap
public import Theory.GroupTheory.InvariantLeviDecomposition

/-!
# Omega-center factors in a commuting product

Let S be a finite group, with commuting disjoint factors U and D whose join
contains Ω₁(Z(S)). If U and D are both normalized by S, every omega-central
element splits into a U-part and a D-part, and each factor is fixed by S.
This is the elementary factor step used in the two-block branch of
Aschbacher–Smith C.5.6(7): `Q = U × D` and `E = Ω₁(Z(S))`.
-/

public section
open Subgroup Stellmacher
open scoped Pointwise

variable {G : Type*} [Group G]

/-- Omega-central elements split into fixed pieces in commuting disjoint
factors. -/
public theorem omegaOneCenterAmbient_le_fixed_factors
    (S U D : Subgroup G) (_hUS : U ≤ S) (_hDS : D ≤ S)
    (hUD : Disjoint U D) (hUn : S ≤ normalizer (U : Set G))
    (hDn : S ≤ normalizer (D : Set G))
    (hcomm : U ≤ centralizer (D : Set G))
    (hspan : omegaOneCenterAmbient S ≤ U ⊔ D) :
    omegaOneCenterAmbient S ≤
      (U ⊓ centralizer (S : Set G)) ⊔ (D ⊓ centralizer (S : Set G)) := by
  intro e he
  have hm : e ∈ (U : Set G) * (D : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right U D
      (hcomm.trans (Subgroup.centralizer_le_normalizer _))]
    exact hspan he
  obtain ⟨u, hu, d, hd, rfl⟩ := hm
  have hfix (s : G) (hs : s ∈ S) :
      MulAut.conj s u = u ∧ MulAut.conj s d = d := by
    apply fixed_factors_of_disjoint (MulAut.conj s).toMonoidHom U D hUD
      (fun u hu => (mem_normalizer_iff.mp (hUn hs) u).mp hu)
      (fun d hd => (mem_normalizer_iff.mp (hDn hs) d).mp hd) hu hd
    change s * (u * d) * s⁻¹ = u * d
    rw [((mem_omegaOneCenterAmbient_iff _ _).mp he).2.2 s hs, mul_inv_cancel_right]
  apply mul_mem_sup
  · refine ⟨hu, ?_⟩
    intro s hs
    exact mul_inv_eq_iff_eq_mul.mp (hfix s hs).1
  · refine ⟨hd, ?_⟩
    intro s hs
    exact mul_inv_eq_iff_eq_mul.mp (hfix s hs).2
