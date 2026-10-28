module

public import Theory.Mathieu.M22.Properties.Design
public import Theory.Mathieu.M22.Properties.LocalSubgroups

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open Equiv Equiv.Perm MulAction
open scoped Pointwise

namespace Sporadic.Mathieu

noncomputable section

private abbrev M22InDesignAut : Subgroup m22DesignAut :=
  M22.subgroupOf m22DesignAut

private instance : M22InDesignAut.Normal :=
  M22_normal_in_m22DesignAut

private def m22InDesignAutEquivM22 : M22InDesignAut ≃* M22 :=
  Subgroup.subgroupOfEquivOfLe M22_le_hexadDesignAut

private def m22AutEquiv : MulAut M22InDesignAut ≃* MulAut M22 where
  toFun φ := m22InDesignAutEquivM22.symm.trans (φ.trans m22InDesignAutEquivM22)
  invFun φ := m22InDesignAutEquivM22.trans (φ.trans m22InDesignAutEquivM22.symm)
  left_inv φ := by ext x; rfl
  right_inv φ := by ext x; rfl
  map_mul' φ ψ := by ext x; rfl

private theorem m22DesignAut_centralizer_trivial
    (g : m22DesignAut)
    (hcomm : ∀ h : M22InDesignAut,
      (g.1 : Perm (Fin 22)) * (h.1.1 : Perm (Fin 22)) =
        (h.1.1 : Perm (Fin 22)) * (g.1 : Perm (Fin 22))) :
    g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_contra hx
  obtain ⟨z, hzx, hzgx⟩ :=
    Fin.exists_ne_and_ne_of_two_lt x ((g.1 : Perm (Fin 22)) x) (by omega)
  let source : Fin 2 ↪ Fin 22 :=
    { toFun := fun i => if i = 0 then x else (g.1 : Perm (Fin 22)) x
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · simp only [Fin.zero_eta, ↓reduceIte] at hij
          exact (Ne.symm hx hij).elim
        · simp only [Fin.zero_eta, ↓reduceIte] at hij
          exact (hx hij).elim
        · rfl }
  let target : Fin 2 ↪ Fin 22 :=
    { toFun := fun i => if i = 0 then x else z
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · simp only [Fin.zero_eta, ↓reduceIte] at hij
          exact (hzx hij.symm).elim
        · simp only [Fin.zero_eta, ↓reduceIte] at hij
          exact (hzx hij).elim
        · rfl }
  obtain ⟨k, hk⟩ := m22_isTwoPretransitive.exists_smul_eq source target
  have hk0 : k • x = x := by
    have hi := congrArg (fun e : Fin 2 ↪ Fin 22 => e 0) hk
    change k • source 0 = target 0 at hi
    rw [show source 0 = x by rfl, show target 0 = x by rfl] at hi
    exact hi
  have hk1 : k • ((g.1 : Perm (Fin 22)) x) = z := by
    have hi := congrArg (fun e : Fin 2 ↪ Fin 22 => e 1) hk
    change k • source 1 = target 1 at hi
    rw [show source 1 = (g.1 : Perm (Fin 22)) x by rfl,
      show target 1 = z by rfl] at hi
    exact hi
  change (k.1 : Perm (Fin 22)) x = x at hk0
  change (k.1 : Perm (Fin 22)) ((g.1 : Perm (Fin 22)) x) = z at hk1
  let k' : M22InDesignAut := m22InDesignAutEquivM22.symm k
  have hc := hcomm k'
  have hc' :
      (g.1 : Perm (Fin 22)) * (k.1 : Perm (Fin 22)) =
        (k.1 : Perm (Fin 22)) * (g.1 : Perm (Fin 22)) := by
    change (g.1 : Perm (Fin 22)) * (k.1 : Perm (Fin 22)) =
      (k.1 : Perm (Fin 22)) * (g.1 : Perm (Fin 22)) at hc
    exact hc
  have happly := congrArg (fun p : Perm (Fin 22) => p x) hc'
  simp only [Equiv.Perm.mul_apply] at happly
  rw [hk0, hk1] at happly
  exact hzgx happly.symm

private theorem m22DesignAut_conjNormal_injective :
    Function.Injective (MulAut.conjNormal (H := M22InDesignAut)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply m22DesignAut_centralizer_trivial g
  intro h
  have hfix := DFunLike.congr_fun hg h
  change (MulAut.conjNormal g) h = h at hfix
  have hfix' :
      g * (h.1 : m22DesignAut) * g⁻¹ = (h.1 : m22DesignAut) := by
    have hval := congrArg Subtype.val hfix
    simpa only [MulAut.conjNormal_apply] using hval
  have hmul := congrArg (fun x : m22DesignAut => x * g) hfix'
  have hcomm' :
      g * (h.1 : m22DesignAut) = (h.1 : m22DesignAut) * g := by
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
  exact congrArg Subtype.val hcomm'

/-- Conjugation gives a faithful map from the full hexad-design automorphism
 group into the abstract automorphism group of M22. -/
public noncomputable def m22DesignAutToAut : m22DesignAut →* MulAut M22 :=
  m22AutEquiv.toMonoidHom.comp (MulAut.conjNormal (H := M22InDesignAut))

public theorem m22DesignAutToAut_injective :
    Function.Injective m22DesignAutToAut :=
  m22AutEquiv.injective.comp m22DesignAut_conjNormal_injective

/-- The abstract automorphism group contains the full design automorphism group. -/
public theorem m22Aut_card_lower_bound :
    887040 ≤ Nat.card (MulAut M22) := by
  rw [← m22DesignAut_order]
  exact Nat.card_le_card_of_injective m22DesignAutToAut m22DesignAutToAut_injective

/-- The standard odd pair-swap, regarded as a full design automorphism. -/
@[expose] public noncomputable def m22OuterDesignAut : m22DesignAut :=
  ⟨m22OddPairSwap, m22OddPairSwap_mem_designAut⟩

public theorem m22OuterDesignAut_order :
    orderOf m22OuterDesignAut = 2 := by
  rw [← Subgroup.orderOf_coe m22OuterDesignAut]
  exact m22OddPairSwap_order

private theorem m22DesignAutToAut_even (h : M22) :
    m22DesignAutToAut
        ((m22InDesignAutEquivM22.symm h).1 : m22DesignAut) =
      MulAut.conj h := by
  ext x y
  rfl

/-- The odd design involution induces an automorphism which is not inner. -/
public theorem m22OuterAutomorphism_not_inner :
    ¬ ∃ h : M22,
      m22DesignAutToAut m22OuterDesignAut = MulAut.conj h := by
  rintro ⟨h, hh⟩
  have heven := m22DesignAutToAut_even h
  have hamb :
      m22OuterDesignAut =
        ((m22InDesignAutEquivM22.symm h).1 : m22DesignAut) :=
    m22DesignAutToAut_injective (hh.trans heven.symm)
  have hperm := congrArg Subtype.val hamb
  apply m22OddPairSwap_not_mem_M22
  change (m22OuterDesignAut.1 : Perm (Fin 22)) ∈ M22
  rw [hperm]
  exact (m22InDesignAutEquivM22.symm h).property

public theorem m22OuterAutomorphism_order :
    orderOf (m22DesignAutToAut m22OuterDesignAut) = 2 := by
  rw [orderOf_injective m22DesignAutToAut m22DesignAutToAut_injective]
  exact m22OuterDesignAut_order

/-- The subgroup of inner automorphisms of M22. -/
@[expose] public def m22InnerAut : Subgroup (MulAut M22) :=
  MonoidHom.range MulAut.conj

public instance m22InnerAut_normal : m22InnerAut.Normal where
  conj_mem n hn g := by
    rcases hn with ⟨x, rfl⟩
    refine ⟨g x, ?_⟩
    apply MulEquiv.ext
    intro y
    change g x * y * (g x)⁻¹ = g (x * g.symm y * x⁻¹)
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]

public theorem m22OuterAutomorphism_not_mem_inner :
    m22DesignAutToAut m22OuterDesignAut ∉ m22InnerAut := by
  intro hmem
  rcases hmem with ⟨h, hh⟩
  exact m22OuterAutomorphism_not_inner ⟨h, hh.symm⟩

/-- The abstract outer automorphism group of M22. -/
public abbrev M22OuterAutomorphismGroup :=
  MulAut M22 ⧸ m22InnerAut

/-- The nontrivial outer class supplied by the odd design involution. -/
@[expose] public noncomputable def m22OuterAutomorphismClass :
    M22OuterAutomorphismGroup :=
  QuotientGroup.mk' m22InnerAut
    (m22DesignAutToAut m22OuterDesignAut)

public theorem m22OuterAutomorphismClass_ne_one :
    m22OuterAutomorphismClass ≠ 1 := by
  intro h
  apply m22OuterAutomorphism_not_mem_inner
  apply (QuotientGroup.eq_one_iff
    (N := m22InnerAut)
    (m22DesignAutToAut m22OuterDesignAut)).mp
  simpa [m22OuterAutomorphismClass] using h

/-- In particular, Out(M22) has at least two elements. -/
public theorem m22Out_card_lower_bound :
    2 ≤ Nat.card M22OuterAutomorphismGroup := by
  have hnon : Nontrivial M22OuterAutomorphismGroup :=
    nontrivial_iff.mpr
      ⟨m22OuterAutomorphismClass, 1, m22OuterAutomorphismClass_ne_one⟩
  have hcard : 1 < Nat.card M22OuterAutomorphismGroup :=
    Finite.one_lt_card_iff_nontrivial.mpr hnon
  omega


/-- The concrete design automorphism acts on the natural M22 model by conjugation. -/
public theorem m22DesignAutToAut_apply_perm (g : m22DesignAut) (h : M22) :
    ((m22DesignAutToAut g) h : Equiv.Perm (Fin 22)) =
      (g : Equiv.Perm (Fin 22)) * (h : Equiv.Perm (Fin 22)) *
        Inv.inv (g : Equiv.Perm (Fin 22)) := by
  rfl
end

end Sporadic.Mathieu
