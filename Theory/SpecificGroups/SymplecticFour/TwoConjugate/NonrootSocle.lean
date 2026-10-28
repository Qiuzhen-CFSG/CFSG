module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.OddCore
public import Theory.GroupTheory.GeneralizedFitting.TwoCentralizers
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.NormalForms

/-!
# The simple socle of a root-free symplectic opposite pair

The Suzuki involution trichotomy puts every nonroot involution in class c₂.
The standard central-root element with parameters (1,1) has this type, so
normal forms conjugate its unipotent centralizer to the centralizer of every
nonroot involution. Restriction makes the involution centralizers of a
root-free subgroup two-groups. For the literal opposite pair, the elementary
central plane kills the odd core, and triviality of the two-core then gives
a simple generalized Fitting subgroup.

Source: Aschbacher--Smith E.2.7, printed p.220, the all-c₂ simple-socle step.
The known-simple shortlist and its marked recognition are later obligations.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

omit [Finite F] in
private theorem movedSpace_upper_one : movedSpace (upper (1:F) 1) = plane F := by
  ext x
  constructor
  · rintro ⟨v,rfl⟩
    intro i
    fin_cases i <;> simp [upper_apply]
  · intro hx
    refine ⟨Sum.elim ![0,0] ![x b,x a+x b],?_⟩
    change upper (1:F) 1 • _ - _ = x
    rw [upper_apply]
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [hx 0,hx 1,CharTwo.add_self_eq_zero,add_left_comm]

omit [Finite F] in
private theorem upper_one_isC2 : IsC2 (upper (1:F) 1) := by
  refine ⟨upper_orderOf 1 1 one_ne_zero, ?_, ?_⟩
  · rw [movedSpace_upper_one, finrank_plane]
  · refine ⟨Pi.single c 1, ?_⟩
    simp [form_apply,upper_apply,Fin.sum_univ_two,Pi.single_apply,CharTwo.neg_eq]

/-- Every c₂ involution has a two-group centralizer in the full symplectic group. -/
theorem isPGroup_centralizer_of_isC2 {n : ℕ} (hF : Nat.card F=2^n)
    (g : Sp F) (hg : IsC2 g) : IsPGroup 2 (centralizer ({g} : Set (Sp F))) := by
  obtain ⟨h,hh⟩ := isC2_conjugate_c2 g hg
  obtain ⟨k,hk⟩ := isC2_conjugate_c2 (upper (1:F) 1) upper_one_isC2
  let e := MulAut.conj (h*k⁻¹)
  have he : e (upper (1:F) 1) = g := by
    simp [e, MulAut.conj_apply, hk,hh,mul_assoc]
  have hmap : (centralizer ({upper (1:F) 1} : Set (Sp F))).map e.toMonoidHom =
      centralizer ({g} : Set (Sp F)) := by
    apply le_antisymm
    · have hm := map_centralizer_le_centralizer_image ({upper (1:F) 1} : Set (Sp F)) e.toMonoidHom
      simp only [Set.image_singleton] at hm
      change _ ≤ centralizer ({e (upper (1:F) 1)} : Set (Sp F)) at hm
      rwa [he] at hm
    · intro x hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply,he] using mem_centralizer_singleton_iff.mp hx
  rw [←hmap,centralizer_upper_eq_unipotent 1 1 one_ne_zero one_ne_zero]
  exact (isPGroup_unipotent hF).map e.toMonoidHom

/-- The full centralizer of a nonroot involution is a two-group. -/
theorem isPGroup_centralizer_of_nonroot_involution {n : ℕ} (hF : Nat.card F=2^n)
    (g : Sp F) (hg : orderOf g=2) (hnr : ¬IsRootElement g) :
    IsPGroup 2 (centralizer ({g} : Set (Sp F))) := by
  rcases involution_types g hg with hb | ha | hc
  · exact (hnr ((isRootElement_iff g).mpr (Or.inl hb))).elim
  · exact (hnr ((isRootElement_iff g).mpr (Or.inr ha))).elim
  · exact isPGroup_centralizer_of_isC2 hF g hc

/-- Root-free literal subgroups inherit two-group involution centralizers. -/
theorem subgroup_isPGroup_involution_centralizers_of_nonroot {n : ℕ}
    (hF : Nat.card F=2^n) (I : Subgroup (Sp F))
    (hnr : ∀ g ∈ I, ¬IsRootElement g) (t : I) (ht : orderOf t=2) :
    IsPGroup 2 (centralizer ({t} : Set I)) := by
  have hp := isPGroup_centralizer_of_nonroot_involution hF t
    ((orderOf_coe t).trans ht) (hnr t t.property)
  have he : centralizer ({t} : Set I) = (centralizer ({(t : Sp F)} : Set (Sp F))).comap I.subtype := by
    ext x
    rw [mem_centralizer_singleton_iff,mem_comap,mem_centralizer_singleton_iff,←Subtype.coe_inj]
    rfl
  rw [he]
  exact hp.comap_subtype
/-- The original noncyclic central subgroup makes a root-free opposite pair
nontrivial, while its two-core and odd core vanish. Hence F* is simple. -/
theorem oppositePair_generalizedFitting_simple_of_nonroot_central {n : ℕ}
    (hF : Nat.card F=2^n) (V : Subgroup (Sp F)) [IsElementaryAbelian 2 V]
    (hr : 2 < Nat.card V)
    (hc : V ≤ (CentralRootGeometry.parameter (F := F)).range)
    (h2 : pCore 2 (oppositePair V)=⊥)
    (hnr : ∀ g ∈ oppositePair V, ¬IsRootElement g) :
    IsSimpleGroup (Theory.GroupTheory.generalizedFitting (oppositePair V)) := by
  have hne : oppositePair V ≠ ⊥ := by
    intro he
    have hV : V=⊥ := le_bot_iff.mp (he ▸ (show V ≤ oppositePair V from le_sup_left))
    subst V
    simp at hr
  let : Nontrivial (oppositePair V) := (nontrivial_iff_ne_bot _).mpr hne
  exact Theory.GroupTheory.simple_generalizedFitting_of_two_involution_centralizers
    h2 (oppositePair_oddCore_eq_bot_of_nonroot_central hF V hr hc hnr)
    (subgroup_isPGroup_involution_centralizers_of_nonroot hF (oppositePair V) hnr)

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
