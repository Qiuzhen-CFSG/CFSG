module
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PCoreSurjective

/-!
# Inner actions on a centerless product in a two-extension

A normal centerless subgroup with two-group quotient has trivial
centralizer when the ambient two-core is trivial: its centralizer injects
into that quotient. For a commuting direct product of two centerless
factors, canceling the two specified inner actions leaves an element of
this trivial centralizer. Thus the original actor belongs to the product.

The statement retains both actual factor embeddings and conjugation
identities. The Chapter14 consumer applies it after quotienting by the
ambient two-core, rather than lifting quotient commutation to the group.
Source application: Aschbacher--Smith 14.6.14(4)--15, printed pp.1033--1034.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem centralizer_normal_centerless_eq_bot
    (N : Subgroup G) [N.Normal] (hN : center N = ⊥)
    (hq : IsPGroup 2 (G ⧸ N)) (hcore : pCore 2 G = ⊥) :
    centralizer (N : Set G) = ⊥ := by
  let C := centralizer (N : Set G)
  let f := (QuotientGroup.mk' N).comp C.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp hx
    have hz : (⟨x,hxN⟩ : N) ∈ center N := mem_center_iff.mpr fun y =>
      Subtype.ext (x.property y y.property)
    have he : (⟨x,hxN⟩ : N) = 1 := mem_bot.mp (hN ▸ hz)
    change x = 1
    apply Subtype.ext
    exact congrArg (fun z : N => (z : G)) he
  have hc : IsPGroup 2 C := hq.of_injective f hf
  exact bot_unique ((show C ≤ pCore 2 G from le_sSup ⟨inferInstance,hc⟩).trans_eq hcore)

private theorem cancel_inner_action (A : Subgroup G) (x a b : G)
    (hi : ∀ y ∈ A, x * y * x⁻¹ = a * y * a⁻¹)
    (hb : b ∈ centralizer (A : Set G)) :
    (a*b)⁻¹*x ∈ centralizer (A : Set G) := by
  apply mem_centralizer_iff.mpr
  intro y hy
  have he : ((a*b)⁻¹*x) * y * ((a*b)⁻¹*x)⁻¹ = y := by
    calc
      _ = b⁻¹ * (a⁻¹ * (x*y*x⁻¹) * a) * b := by group
      _ = b⁻¹ * y * b := by rw [hi y hy]; group
      _ = y := by rw [mul_assoc,hb y hy,inv_mul_cancel_left]
  exact ((mul_inv_eq_iff_eq_mul).mp he).symm

/-- In a core-free two-extension of a centerless product, an actor inner on
both literal factors belongs to their product. -/
theorem mem_product_of_paired_inner_actions
    (A B : Subgroup G) [(A ⊔ B).Normal]
    (hdis : Disjoint A B) (hcomm : A ≤ centralizer (B : Set G))
    (hzA : center A = ⊥) (hzB : center B = ⊥)
    (hq : IsPGroup 2 (G ⧸ (A ⊔ B))) (hcore : pCore 2 G = ⊥)
    (x : G)
    (hiA : ∃ a ∈ A, ∀ y ∈ A, x*y*x⁻¹ = a*y*a⁻¹)
    (hiB : ∃ b ∈ B, ∀ y ∈ B, x*y*x⁻¹ = b*y*b⁻¹) : x ∈ A ⊔ B := by
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hdis hcomm
  have hz : center (A ⊔ B : Subgroup G) = ⊥ := by
    apply card_eq_one.mp
    rw [←Nat.card_congr (centerCongr e).toEquiv,Subgroup.center_prod,hzA,hzB]
    simp only [bot_prod_bot,card_bot]
  have hC := centralizer_normal_centerless_eq_bot (A ⊔ B) hz hq hcore
  obtain ⟨a,ha,hiA⟩ := hiA
  obtain ⟨b,hb,hiB⟩ := hiB
  have h1 := cancel_inner_action A x a b hiA (le_centralizer_iff.mp hcomm hb)
  have h2 := cancel_inner_action B x b a hiB (hcomm ha)
  rw [hcomm ha b hb] at h2
  have hd : (a*b)⁻¹*x ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    have hab : A ⊔ B ≤ centralizer ({(a*b)⁻¹*x} : Set G) :=
      sup_le (fun y hy => mem_centralizer_singleton_iff.mpr (h1 y hy))
        (fun y hy => mem_centralizer_singleton_iff.mpr (h2 y hy))
    exact fun y hy => mem_centralizer_singleton_iff.mp (hab hy)
  have he : x = a*b := (inv_mul_eq_one.mp (mem_bot.mp (hC ▸ hd))).symm
  rw [he]
  exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
end Theory.GroupTheory
