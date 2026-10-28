module

public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Transport
public import Theory.GroupAction.QuadraticFieldQuotient

/-!
# Reduction of Cartan rigidity to a standard root group

Conjugate the specified Sylow subgroup to the standard root group and carry
the complement and the same automorphism through that equivalence. Both
normalization conditions and the quadratic identity transport literally.
This supplies the common assembly for the linear and Suzuki cases of the
field-automorphism argument in F.1.3(5), printed p.260.
-/

public section
namespace CFSG.Quasithin.ChapterF.Source
open Subgroup

theorem CartanQuadraticRigidity.of_standard
    {H : Type*} [Group H] [Finite H] (U B : Subgroup H)
    (hB : normalizer (U : Set H) = B)
    (hc : ∀ T : Sylow 2 H, ∃ e : MulAut H, (T : Subgroup H).map e.toMonoidHom = U)
    (hr : ∀ D : Subgroup H, D ≤ B → Nat.Coprime 2 (Nat.card D) →
      Disjoint U D → U ⊔ D = B →
      ∀ a : MulAut H, Odd (orderOf a) → U.map a.toMonoidHom = U →
        D.map a.toMonoidHom = D →
        (∀ x ∈ D, a (a x * x⁻¹) = a x * x⁻¹) → ∀ x ∈ D, a x = x) :
    CartanQuadraticRigidity H := by
  intro T D hDN ho hd hs a hao haT haD hquad
  obtain ⟨e, hU⟩ := hc T
  let E := D.map e.toMonoidHom
  let b := MulAut.congr e a
  have hN : (normalizer (T : Set H)).map e.toMonoidHom = B := by
    change (normalizer ((T : Subgroup H) : Set H)).map e.toMonoidHom = B
    rw [Subgroup.map_equiv_normalizer_eq, hU, hB]
  have hEN : E ≤ B := hN ▸ Subgroup.map_mono hDN
  have hEo : Nat.Coprime 2 (Nat.card E) := by
    rwa [← Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
  have hEd : Disjoint U E := hU ▸ disjoint_map e.injective hd
  have hEs : U ⊔ E = B := by
    rw [← hU, ← Subgroup.map_sup, hs, hN]
  have hb : Odd (orderOf b) := by rwa [(MulAut.congr e).orderOf_eq]
  have hbq (x : H) : b (e x) = e (a x) := by
    change e (a (e.symm (e x))) = e (a x)
    rw [e.symm_apply_apply]
  have hmap (V : Subgroup H) :
      (V.map e.toMonoidHom).map b.toMonoidHom = (V.map a.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact hbq x
  have hbU : U.map b.toMonoidHom = U := by rw [← hU, hmap, haT]
  have hbE : E.map b.toMonoidHom = E := by
    change (D.map e.toMonoidHom).map b.toMonoidHom = D.map e.toMonoidHom
    rw [hmap, haD]
  have hf := hr E hEN hEo hEd hEs b hb hbU hbE (by
    rintro z ⟨x, hx, rfl⟩
    change b (b (e x) * (e x)⁻¹) = b (e x) * (e x)⁻¹
    rw [hbq, ← map_inv, ← map_mul, hbq, hquad x hx])
  intro x hx
  apply e.injective
  rw [← hbq]
  exact hf (e x) (mem_map_of_mem e.toMonoidHom hx)

end CFSG.Quasithin.ChapterF.Source
