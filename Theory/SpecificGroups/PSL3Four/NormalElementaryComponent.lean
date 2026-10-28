module
public import Theory.SpecificGroups.PSL3Four.NormalElementarySylow
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport.DiagramEquivalence

/-!
# Normal elementary Sylow actors on a PSL₃(4) component

If a Sylow two-subgroup acts nontrivially on the diagram of a normal
PSL₃(4) subgroup, every normal elementary subgroup of that Sylow induces
inner automorphisms on the component. Thus it lies in the product of the
component and its centralizer. The argument transports the literal action
to the concrete model, applies normal-elementary placement, and lifts the
inner image back through the actual conjugation kernel.

Source: Aschbacher--Smith E.2.7 and 14.2.13, printed pp.219 and 984;
used for the opposite actor of 5.1.23, printed p.645, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
open Matrix.PSL3.LinearThree.OuterExtensions
namespace Matrix.PSL3Four.NormalElementarySylow
variable {X : Type*} [Group X] [Finite X]

/-- A normal elementary Sylow subgroup acts by inner automorphisms on a
normal PSL₃(4) component whenever the original Sylow has a diagram actor. -/
theorem le_component_sup_centralizer_of_diagram
    (K : Subgroup X) [K.Normal] (S : Sylow 2 X)
    (E : Subgroup X) [IsElementaryAbelian 2 E]
    (hES : E ≤ (S : Subgroup X))
    (hn : (S : Subgroup X) ≤ normalizer (E : Set X))
    {F₀ : Type*} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = 4)
    (e : K ≃* PSL(3,F₀)) (t : X) (ht : t ∈ (S : Subgroup X))
    (a : MulAut K) (b : MulAut PSL(3,F₀))
    (ha : ∀ k : K, (a k : X) = t * k * t⁻¹)
    (hb : ∀ k, e (a k) = b (e k)) (hd : b ∉ diagramTrivial F₀) :
    E ≤ K ⊔ centralizer (K : Set X) := by
  let : Fintype F₀ := Fintype.ofFinite F₀
  let : Fintype F := Fintype.ofFinite F
  let s : F₀ ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF₀, card_F])
  let i := Atlas.fieldEquivPSL 3 s
  let j : K ≃* PSL := e.trans i
  let f : X →* MulAut PSL := (MulAut.congr j).toMonoidHom.comp MulAut.conjNormal
  have hf_inner (k : K) : f (k : X) = MulAut.conj (j k) := by
    ext y
    change j (k * j.symm y * k⁻¹) = j k * y * (j k)⁻¹
    simp only [map_mul,map_inv,j.apply_symm_apply]
  have hinner : MulAut.innerSubgroup PSL ≤ f.range := by
    rintro _ ⟨k,rfl⟩
    refine ⟨(j.symm k : X),?_⟩
    rw [hf_inner,j.apply_symm_apply]
  have ht_map : f t = MulAut.congr i b := by
    ext y
    change j (MulAut.conjNormal t (j.symm y)) = i (b (i.symm y))
    have ha' : MulAut.conjNormal t (j.symm y) = a (j.symm y) :=
      Subtype.ext (ha (j.symm y)).symm
    rw [ha']
    change i (e (a (j.symm y))) = _
    rw [hb]
    change i (b (e (e.symm (i.symm y)))) = _
    rw [e.apply_symm_apply]
  have hswap : ∃ t ∈ (S : Subgroup X),
      diagramAction F (n := 2) (by decide) (by simpa using card_F) (f t) ≠ 1 := by
    refine ⟨t,ht,?_⟩
    intro he
    apply hd
    apply diagramTrivial_of_equiv_four hF₀ card_F i b
    rw [← ht_map,← diagramAction_ker F (n := 2) (by decide) card_F]
    exact he
  have hEinner := normal_elementary_image_le_inner f hinner S E hES hn hswap
  have hker : f.ker = centralizer (K : Set X) := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.congr j).injective,
      MulAut.conjNormal_ker_eq_centralizer]
  intro x hx
  obtain ⟨k,hk⟩ := hEinner (mem_map_of_mem f hx)
  let k₀ : K := j.symm k
  have hfx : f (k₀ : X) = f x := by
    rw [hf_inner]
    exact (congrArg MulAut.conj (j.apply_symm_apply k)).trans hk
  have hz : (k₀ : X)⁻¹ * x ∈ centralizer (K : Set X) := by
    rw [← hker]
    change f ((k₀ : X)⁻¹ * x) = 1
    rw [map_mul,map_inv,hfx,inv_mul_cancel]
  have hh := (K ⊔ centralizer (K : Set X)).mul_mem
    (mem_sup_left k₀.property) (mem_sup_right hz)
  simpa only [mul_inv_cancel_left] using hh

end Matrix.PSL3Four.NormalElementarySylow
