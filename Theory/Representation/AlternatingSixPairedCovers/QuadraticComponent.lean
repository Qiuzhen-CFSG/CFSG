module
public import Theory.Representation.AlternatingSixPairedCovers.Inputs
public import Theory.Representation.BinaryPermutationSixCover.Movement
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.ElementaryAbelian.Injective
/-!
# Simultaneous quadratic actors inside the marked A₆ component

Fix one component involution and conjugate it to (01)(23). Its commuting
involutions form two Klein-four classes. The second displacement of the pair
04 detects one class in the first natural quotient; the pair 02 detects the
other after the specified diagram automorphism. Thus a subgroup quadratic on
both quotients has order at most two. Surjective equivariant quotient maps
carry the same calculation to either permitted covering support, including
covers with intersecting central kernels.

Source: Aschbacher–Smith, original 14.6.24(2), printed p.1041. This proves the
component-intersection bound, not the whole-actor classification. The source
consumer is ComponentCriticalPair.AlternatingSix.QuadraticActors.
-/

public section
open Representation Representation.BinaryOffender BinaryPermutation Subgroup
namespace AlternatingSixPairedCovers
private abbrev S := Equiv.Perm (Fin 6)
private abbrev A := alternatingGroup (Fin 6)
private def t : S := Equiv.swap 0 1 * Equiv.swap 2 3
private def b₁ : S := Equiv.swap 0 2 * Equiv.swap 1 3
private def b₂ : S := Equiv.swap 0 3 * Equiv.swap 1 2
private def b₃ : S := Equiv.swap 0 1 * Equiv.swap 4 5
private def b₄ : S := Equiv.swap 2 3 * Equiv.swap 4 5
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem centralizer_cases : ∀ b : S, b.sign = 1 → b ^ 2 = 1 → t*b = b*t →
    b = 1 ∨ b = t ∨ b = b₁ ∨ b = b₂ ∨ b = b₃ ∨ b = b₄ := by
  decide +kernel

private def d : S := Equiv.swap 2 4 * Equiv.swap 3 5
private def e₃ : S := Equiv.swap 2 5 * Equiv.swap 3 4
private def e₄ : S := Equiv.swap 2 3 * Equiv.swap 4 5
private theorem outer_t : GLS3.Chapter5.outerHom t = Equiv.swap 0 1 * Equiv.swap 3 5 := by
  apply Equiv.ext
  intro i
  apply GLS3.Chapter5.pentadAt_injective
  change GLS3.Chapter5.pentadAt (GLS3.Chapter5.outerAct t i) = _
  rw [GLS3.Chapter5.outerAct_spec]
  fin_cases i <;> decide +kernel
private theorem outer_b₃ : GLS3.Chapter5.outerHom b₃ = Equiv.swap 0 3 * Equiv.swap 1 5 := by
  apply Equiv.ext
  intro i
  apply GLS3.Chapter5.pentadAt_injective
  change GLS3.Chapter5.pentadAt (GLS3.Chapter5.outerAct b₃ i) = _
  rw [GLS3.Chapter5.outerAct_spec]
  fin_cases i <;> decide +kernel
private theorem outer_b₄ : GLS3.Chapter5.outerHom b₄ = Equiv.swap 0 5 * Equiv.swap 1 3 := by
  apply Equiv.ext
  intro i
  apply GLS3.Chapter5.pentadAt_injective
  change GLS3.Chapter5.pentadAt (GLS3.Chapter5.outerAct b₄ i) = _
  rw [GLS3.Chapter5.outerAct_spec]
  fin_cases i <;> decide +kernel
private theorem diagram_values : BinaryAlternatingSix.diagramAut t = d ∧
    BinaryAlternatingSix.diagramAut b₃ = e₃ ∧ BinaryAlternatingSix.diagramAut b₄ = e₄ := by
  change BinaryAlternatingSix.align * GLS3.Chapter5.outerHom t * BinaryAlternatingSix.align⁻¹ = d ∧
    BinaryAlternatingSix.align * GLS3.Chapter5.outerHom b₃ * BinaryAlternatingSix.align⁻¹ = e₃ ∧
    BinaryAlternatingSix.align * GLS3.Chapter5.outerHom b₄ * BinaryAlternatingSix.align⁻¹ = e₄
  rw [outer_t,outer_b₃,outer_b₄]
  decide +kernel

private def pair (j : Fin 6) : core (Fin 6) :=
  ⟨Pi.single 0 1 + Pi.single j 1, by simp [mem_core,Finset.sum_add_distrib,CharTwo.add_self_eq_zero]⟩
private def delta (a b : S) (v : core (Fin 6)) : core (Fin 6) :=
  coreRepresentation (Fin 6) a (coreRepresentation (Fin 6) b v - v) -
    (coreRepresentation (Fin 6) b v - v)

private theorem delta_constant (a b : S)
    (hq : ∀ v, naturalRepresentation (Fin 6) a (naturalRepresentation (Fin 6) b v - v) =
      naturalRepresentation (Fin 6) b v - v) (v : core (Fin 6)) (i j : Fin 6) :
    (delta a b v).val i = (delta a b v).val j := by
  have hz : coreToNatural (Fin 6) (delta a b v) = 0 := by
    simp only [delta,map_sub,coreToNatural_equivariant]
    rw [← map_sub,hq,sub_self]
  have hz' := congrArg Subtype.val hz
  have hc : (delta a b v).val ∈ constants (Fin 6) :=
    (Submodule.Quotient.mk_eq_zero _).mp hz'
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hc
  exact (congrFun hc i).symm.trans (congrFun hc j)

private theorem standard_pair (b : S) (hb : b.sign = 1) (hb2 : b ^ 2 = 1)
    (hcomm : t*b = b*t)
    (h₁ : ∀ v, naturalRepresentation (Fin 6) t (naturalRepresentation (Fin 6) b v-v) =
      naturalRepresentation (Fin 6) b v-v)
    (h₂ : ∀ v, naturalRepresentation (Fin 6) (BinaryAlternatingSix.diagramAut t)
      (naturalRepresentation (Fin 6) (BinaryAlternatingSix.diagramAut b) v-v) =
      naturalRepresentation (Fin 6) (BinaryAlternatingSix.diagramAut b) v-v) :
    b = 1 ∨ b = t := by
  rcases centralizer_cases b hb hb2 hcomm with h | h | rfl | rfl | rfl | rfl
  · exact Or.inl h
  · exact Or.inr h
  · have hc := delta_constant t b₁ h₁ (pair 4) 0 4
    exact (show (delta t b₁ (pair 4)).val 0 ≠ (delta t b₁ (pair 4)).val 4 by decide +kernel) hc |>.elim
  · have hc := delta_constant t b₂ h₁ (pair 4) 0 4
    exact (show (delta t b₂ (pair 4)).val 0 ≠ (delta t b₂ (pair 4)).val 4 by decide +kernel) hc |>.elim
  · rw [diagram_values.1,diagram_values.2.1] at h₂
    have hc := delta_constant d e₃ h₂ (pair 2) 0 2
    exact (show (delta d e₃ (pair 2)).val 0 ≠ (delta d e₃ (pair 2)).val 2 by decide +kernel) hc |>.elim
  · rw [diagram_values.1,diagram_values.2.2] at h₂
    have hc := delta_constant d e₄ h₂ (pair 2) 0 2
    exact (show (delta d e₄ (pair 2)).val 0 ≠ (delta d e₄ (pair 2)).val 2 by decide +kernel) hc |>.elim

private theorem quadratic_pair_conj {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) D V) (a b c : D)
    (h : ∀ v, σ a (σ b v-v) = σ b v-v) :
    ∀ v, σ (c*a*c⁻¹) (σ (c*b*c⁻¹) v-v) = σ (c*b*c⁻¹) v-v := by
  intro v
  rw [← σ.self_inv_apply c v]
  simp only [map_mul,Module.End.mul_apply,σ.inv_self_apply,map_sub]
  simp only [← map_sub,h]

/-- A common quadratic pair in the two differently marked natural A₆ modules
has at most one nonidentity involution. -/
theorem quadratic_pair_eq (a b : alternatingGroup (Fin 6)) (ha : orderOf a = 2) (hb : b ^ 2 = 1)
    (hc : a*b = b*a)
    (h₁ : ∀ v, naturalRepresentation (Fin 6) a.val (naturalRepresentation (Fin 6) b.val v-v) =
      naturalRepresentation (Fin 6) b.val v-v)
    (h₂ : ∀ v, naturalRepresentation (Fin 6) (BinaryAlternatingSix.diagramAut a.val)
      (naturalRepresentation (Fin 6) (BinaryAlternatingSix.diagramAut b.val) v-v) =
      naturalRepresentation (Fin 6) (BinaryAlternatingSix.diagramAut b.val) v-v) :
    b = 1 ∨ b = a := by
  let tA : A := ⟨t,by decide +kernel⟩
  have ht : orderOf tA = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  obtain ⟨c,hc'⟩ := isConj_iff.mp (AlternatingSix.ShadowLocal.involutions_isConj a tA ha ht)
  have he : c.val * a.val * c.val⁻¹ = t := congrArg Subtype.val hc'
  have hq₁ := quadratic_pair_conj (naturalRepresentation (Fin 6)) a.val b.val c.val h₁
  have hq₂ := quadratic_pair_conj
    ((naturalRepresentation (Fin 6)).comp BinaryAlternatingSix.diagramAut.toMonoidHom)
    a.val b.val c.val h₂
  change ∀ v, naturalRepresentation (Fin 6) (BinaryAlternatingSix.diagramAut (c.val*a.val*c.val⁻¹))
    (naturalRepresentation (Fin 6) (BinaryAlternatingSix.diagramAut (c.val*b.val*c.val⁻¹)) v-v) = _ at hq₂
  rw [he] at hq₁ hq₂
  have hb' : (c.val*b.val*c.val⁻¹) ^ 2 = 1 := by
    rw [← MulAut.conj_apply, ← map_pow, show b.val ^ 2 = 1 from congrArg Subtype.val hb,map_one]
  have hc'' : t*(c.val*b.val*c.val⁻¹) = (c.val*b.val*c.val⁻¹)*t := by
    rw [← he]
    calc
      _ = c.val * (a.val*b.val) * c.val⁻¹ := by group
      _ = c.val * (b.val*a.val) * c.val⁻¹ :=
        congrArg (fun x : S => c.val*x*c.val⁻¹) (congrArg Subtype.val hc)
      _ = _ := by group

  rcases standard_pair _ ((inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ b.property c.val)
    hb' hc'' hq₁ hq₂ with hz | hz
  · left
    apply Subtype.ext
    exact (MulAut.conj c.val).injective (hz.trans (map_one _).symm)
  · right
    apply Subtype.ext
    exact (MulAut.conj c.val).injective (hz.trans he.symm)

/-- An elementary subgroup quadratic on both marked natural quotients has
order at most two. -/
theorem simultaneous_quadratic_card_le_two (B : Subgroup (alternatingGroup (Fin 6)))
    [IsElementaryAbelian 2 B]
    (h₁ : IsQuadratic ((naturalRepresentation (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype) B)
    (h₂ : IsQuadratic ((naturalRepresentation (Fin 6)).comp
      (BinaryAlternatingSix.diagramAut.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype)) B) :
    Nat.card B ≤ 2 := by
  classical
  by_cases he : ∃ a : B, a ≠ 1
  · obtain ⟨a,ha⟩ := he
    have ha' : (a : alternatingGroup (Fin 6)) ≠ 1 := fun h => ha (Subtype.ext h)
    have ho : orderOf (a : alternatingGroup (Fin 6)) = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ a.property) ha'
    have hall (b : B) : b = 1 ∨ b = a := by
      have hc : (a : alternatingGroup (Fin 6))*b = b*a :=
        congrArg Subtype.val ((IsMulCommutative.is_comm (M := B)).comm a b)
      exact (quadratic_pair_eq a b ho
        (elemPow_eq_one_of_isElementaryAbelian _ b.property) hc
        (h₁ a a.property b b.property) (h₂ a a.property b b.property)).imp Subtype.ext Subtype.ext
    let f : B → Bool := fun b => decide (b = 1)
    have hf : Function.Injective f := by
      intro b c h
      rcases hall b with rfl | rfl <;> rcases hall c with rfl | rfl <;> simp_all [f]
    exact (Nat.card_le_card_of_injective f hf).trans (by simp [Nat.card_eq_fintype_card])
  · have hb : B = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      apply mem_bot.mpr
      have hx' : (⟨x,hx⟩ : B) = 1 := by by_contra hn; exact he ⟨⟨x,hx⟩,hn⟩
      exact congrArg Subtype.val hx'
    rw [hb,Subgroup.card_bot]
    decide

namespace Data
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) H E} (C : Data ρ)

/-- Simultaneous quadraticity on the whole module bounds the actual
intersection with the same embedded A₆, including augmentation covers. -/
theorem quadratic_component_card (B : Subgroup H) [IsElementaryAbelian 2 B]
    (hq : IsQuadratic ρ B) : Nat.card (B.comap C.component) ≤ 2 := by
  let D := B.comap C.component
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.comap_of_injective C.component C.injective B
  have hqc : IsQuadratic (ρ.comp C.component) D := fun a ha b hb v =>
    hq (C.component a) ha (C.component b) hb v
  obtain ⟨p,hp,he⟩ := C.first_model.natural_quotient
  obtain ⟨q,hq',he'⟩ := C.second_model.natural_quotient
  exact simultaneous_quadratic_card_le_two D
    (quadratic_of_equivariant_surjection _ _ p hp he D
      (quadratic_subrepresentation _ C.first hqc))
    (quadratic_of_equivariant_surjection _ _ q hq' he' D
      (quadratic_subrepresentation _ C.second hqc))
end Data
end AlternatingSixPairedCovers
