module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm.BorelKernel

/-!
# Reduction of cubic Borel generation to triangular torus comparison

Order-three generation commutes with group isomorphisms. Consequently an
inner conjugation aligning the specified Sylow subgroup with the standard
unitriangular group transports its cubic normalizer subgroup as well.
We conjugate both supplied GL₃ matrices by the same special linear lift;
their induced automorphisms, outer condition and cube identities are retained.

In the standard Borel, the root-generation inclusion and a concrete
unitriangular/cubic-torus factorization imply the required generation.
The factorization is an explicit remaining hypothesis of these reductions,
not an asserted source theorem. The identity torus factor is included.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final paragraph
of 15.3.37, printed p.1135; the torus discussion in A.3.18, pp.52--53.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions

namespace Matrix.PSL3.CubicBorel

private theorem cubicClosure_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) :
    (closure {z | z ∈ B ∧ orderOf z = 3}).map e.toMonoidHom =
      closure {z | z ∈ B.map e.toMonoidHom ∧ orderOf z = 3} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hx3⟩, rfl⟩
    exact ⟨mem_map_of_mem _ hx, (e.orderOf_eq x).trans hx3⟩
  · rintro ⟨⟨x, hx, rfl⟩, hz⟩
    exact ⟨x, ⟨hx, (e.orderOf_eq x).symm.trans hz⟩, rfl⟩

private theorem congr_conj {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem cubicInner_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (B : Subgroup G) :
    ((closure {z | z ∈ B ∧ orderOf z = 3}).map MulAut.conj).map
        (MulAut.congr e).toMonoidHom =
      (closure {z | z ∈ B.map e.toMonoidHom ∧ orderOf z = 3}).map MulAut.conj := by
  rw [← cubicClosure_map e B, Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  exact congr_conj e x

private theorem stable_congr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (U : Subgroup G) (V : Subgroup H)
    (hUV : U.map e.toMonoidHom = V) (α : MulAut H)
    (hα : V.map α.toMonoidHom = V) :
    U.map (MulAut.congr e.symm α).toMonoidHom = U := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hm : α (e x) ∈ V := hα.le (mem_map_of_mem _ (hUV ▸ mem_map_of_mem _ hx))
    rw [← hUV] at hm
    obtain ⟨y, hy, he⟩ := hm
    change e.symm (α (e x)) ∈ U
    change e y = α (e x) at he
    rw [← he, e.symm_apply_apply]
    exact hy
  · intro x hx
    have hm : e x ∈ V.map α.toMonoidHom := hα.symm ▸ (hUV ▸ mem_map_of_mem _ hx)
    obtain ⟨y, hy, he⟩ := hm
    rw [← hUV] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨z, hz, ?_⟩
    change e.symm (α (e z)) = x
    change α (e z) = e x at he
    rw [he, e.symm_apply_apply]

variable (F : Type*) [Field F]

/-- The remaining torus comparison has a concrete factorization conclusion.
The matrices need only be upper triangular; no Sylow or ambient group is an input. -/
def TriangularCubicComparison : Prop :=
  ∀ d₀ g : GL (Fin 3) F,
    (d₀.val 1 0 = 0 ∧ d₀.val 2 0 = 0 ∧ d₀.val 2 1 = 0) →
    (g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0) →
    linearConj F d₀ ∉ MulAut.innerSubgroup PSL(3,F) →
    linearConj F d₀ ^ 3 = 1 → linearConj F g ^ 3 = 1 →
    ∃ (k : ℕ) (u v z : PSL(3,F)) (α : MulAut PSL(3,F)),
      u ∈ unipotent F ∧ v ∈ unipotent F ∧ z ∈ torus F ∧ z ^ 3 = 1 ∧
      linearConj F d₀ = MulAut.conj u * α ∧
      linearConj F g = MulAut.conj v * MulAut.conj z * α ^ k

private theorem cubic_mem_closure {G : Type*} [Group G]
    (B : Subgroup G) (z : G) (hz : z ∈ B) (h3 : z ^ 3 = 1) :
    z ∈ closure {z | z ∈ B ∧ orderOf z = 3} := by
  by_cases h : z = 1
  · subst z; exact one_mem _
  · have : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact subset_closure ⟨hz, orderOf_eq_prime h3 h⟩

variable [Finite F]

/-- The root and torus calculations imply generation in the standard Borel.
The cubic torus element is allowed to be the identity. -/
theorem standard_generation_of_calculations [CharP F 2]
    (hU : unipotent F ≤ closure {z | z ∈ borel F ∧ orderOf z = 3})
    (hcompare : TriangularCubicComparison F)
    (d₀ g : GL (Fin 3) F)
    (hout : linearConj F d₀ ∉ MulAut.innerSubgroup PSL(3,F))
    (hd : linearConj F d₀ ^ 3 = 1)
    (hdU : (unipotent F).map (linearConj F d₀).toMonoidHom = unipotent F)
    (hg : linearConj F g ^ 3 = 1)
    (hgU : (unipotent F).map (linearConj F g).toMonoidHom = unipotent F) :
    linearConj F g ∈ (closure {z | z ∈ borel F ∧ orderOf z = 3}).map MulAut.conj ⊔
      zpowers (linearConj F d₀) := by
  obtain ⟨k, u, v, z, α, hu, hv, hz, hz3, hdα, he⟩ := hcompare d₀ g
    (NormalizerForm.linearConj_upperTriangular F d₀ hdU)
    (NormalizerForm.linearConj_upperTriangular F g hgU) hout hd hg
  let K := (closure {z | z ∈ borel F ∧ orderOf z = 3}).map MulAut.conj ⊔
    zpowers (linearConj F d₀)
  have hα : α ∈ K := by
    have hh : α = (MulAut.conj u)⁻¹ * linearConj F d₀ := by rw [hdα]; group
    rw [hh]
    exact K.mul_mem (K.inv_mem (Subgroup.mem_sup_left (mem_map_of_mem _ (hU hu))))
      (Subgroup.mem_sup_right (mem_zpowers _))
  rw [he]
  apply mul_mem
  · apply mul_mem
    · exact Subgroup.mem_sup_left (mem_map_of_mem _ (hU hv))
    · exact Subgroup.mem_sup_left (mem_map_of_mem _
        (cubic_mem_closure (borel F) z (torus_le_borel F hz) hz3))
  · exact K.pow_mem hα k

omit [Finite F] in
private theorem linearConj_congr (s : SL(3,F)) (g : GL (Fin 3) F) :
    MulAut.congr (MulAut.conj (projection F s)) (linearConj F g) =
      linearConj F (SpecialLinearGroup.toGL s * g * (SpecialLinearGroup.toGL s)⁻¹) := by
  rw [map_mul, map_mul, map_inv, linearConj_toGL]
  rfl

/-- Transport the actual matrices and both subgroups along Sylow conjugacy.
The root-generation and triangular torus calculations are the only extra inputs. -/
theorem generation_of_calculations {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (hU : unipotent F ≤ closure {z | z ∈ borel F ∧ orderOf z = 3})
    (hcompare : TriangularCubicComparison F)
    (T : Sylow 2 PSL(3,F)) (d₀ g : GL (Fin 3) F)
    (hout : linearConj F d₀ ∉ MulAut.innerSubgroup PSL(3,F))
    (hd : linearConj F d₀ ^ 3 = 1)
    (hdT : (T : Subgroup PSL(3,F)).map (linearConj F d₀).toMonoidHom = T)
    (hg : linearConj F g ^ 3 = 1)
    (hgT : (T : Subgroup PSL(3,F)).map (linearConj F g).toMonoidHom = T) :
    linearConj F g ∈
      (closure {z | z ∈ normalizer (T : Set PSL(3,F)) ∧ orderOf z = 3}).map MulAut.conj ⊔
        zpowers (linearConj F d₀) := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (Nat.ne_of_gt hn)))
  let : CharP F 2 := ringChar.of_eq hc
  obtain ⟨s, hsU, hsB⟩ := BorelQuotient.sylow_normalizer_conjugate F hn hF T
  obtain ⟨a, rfl⟩ := projection_surjective F s
  let c := MulAut.conj (projection F a)
  let d' := SpecialLinearGroup.toGL a⁻¹ * d₀ * (SpecialLinearGroup.toGL a⁻¹)⁻¹
  let g' := SpecialLinearGroup.toGL a⁻¹ * g * (SpecialLinearGroup.toGL a⁻¹)⁻¹
  have htransport (m : GL (Fin 3) F) :
      MulAut.congr c.symm (linearConj F m) =
        linearConj F (SpecialLinearGroup.toGL a⁻¹ * m * (SpecialLinearGroup.toGL a⁻¹)⁻¹) := by
    simpa only [map_inv, MulAut.inv_def, c] using linearConj_congr F a⁻¹ m
  have hd' : linearConj F d' = MulAut.congr c.symm (linearConj F d₀) :=
    (htransport d₀).symm
  have hg' : linearConj F g' = MulAut.congr c.symm (linearConj F g) :=
    (htransport g).symm
  have hinv (α : MulAut PSL(3,F)) : MulAut.congr c (MulAut.congr c.symm α) = α := by
    ext x
    simp [MulAut.congr_apply]
  have hout' : linearConj F d' ∉ MulAut.innerSubgroup PSL(3,F) := by
    rintro ⟨z, hz⟩
    apply hout
    refine ⟨c z, ?_⟩
    rw [hd'] at hz
    have hh := congrArg (MulAut.congr c) hz
    simpa only [congr_conj, hinv] using hh
  have hd3' : linearConj F d' ^ 3 = 1 := by rw [hd', ← map_pow, hd, map_one]
  have hg3' : linearConj F g' ^ 3 = 1 := by rw [hg', ← map_pow, hg, map_one]
  have hdU' : (unipotent F).map (linearConj F d').toMonoidHom = unipotent F := by
    rw [hd']
    exact stable_congr c _ _ hsU _ hdT
  have hgU' : (unipotent F).map (linearConj F g').toMonoidHom = unipotent F := by
    rw [hg']
    exact stable_congr c _ _ hsU _ hgT
  have hm := standard_generation_of_calculations F hU hcompare d' g' hout' hd3' hdU' hg3' hgU'
  have hm' := mem_map_of_mem (MulAut.congr c).toMonoidHom hm
  rw [Subgroup.map_sup, cubicInner_map, hsB, MonoidHom.map_zpowers] at hm'
  simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hd', hg', hinv] using hm'

end Matrix.PSL3.CubicBorel
