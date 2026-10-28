module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.Ambient

/-!
# Field–Cartan products in the automorphism overgroup

The factors F and H of A.3.15(5) live in Aut(D); they need not be subgroups of
the ambient J. This adapter retains that convention. The trace test makes the
actual coefficient field subgroup disjoint from the inner subgroup. Therefore
an inner element of FH lies in H when H acts by inner automorphisms. If H
preserves the image of S ∩ D, the same holds for the image of B, giving the
intrinsic normalizer containment required by the action theorem.

The raw-source proof must establish the field and inner realizations of F and
H. In particular the inner realization is not a definition of inner-diagonal.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed pp.50–51
and p.511; GLS III, §2.5 (2.5.8 and 2.5.13), for the automorphism conventions.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieAutomorphismExtensions
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
variable {E : Type*} [Field E] [CharP E 2]

theorem field_disjoint_inner :
    Disjoint (fieldAction (F := E)).range (MulAut.conj : Model E →* MulAut (Model E)).range := by
  apply disjoint_iff_inf_le.mpr
  rintro a ⟨⟨σ, rfl⟩, ⟨d, hd⟩⟩
  have hσ := fieldAction_eq_conj_implies_one σ d hd.symm
  change fieldAction σ = 1
  rw [hσ, map_one]

theorem inner_mem_cartan_of_field_product
    (F H : Subgroup (MulAut (Model E)))
    (hF : F ≤ (fieldAction (F := E)).range)
    (hH : H ≤ (MulAut.conj : Model E →* MulAut (Model E)).range)
    (a : MulAut (Model E))
    (ha : a ∈ (MulAut.conj : Model E →* MulAut (Model E)).range)
    (hprod : ∃ f ∈ F, ∃ h ∈ H, a = f * h) : a ∈ H := by
  obtain ⟨f, hf, h, hh, he⟩ := hprod
  have hfinner : f ∈ (MulAut.conj : Model E →* MulAut (Model E)).range := by
    have hm := (MulAut.conj : Model E →* MulAut (Model E)).range.mul_mem
      ha ((MulAut.conj : Model E →* MulAut (Model E)).range.inv_mem (hH hh))
    rw [he] at hm
    simpa only [mul_inv_cancel_right] using hm
  have hf1 : f = 1 := field_disjoint_inner.le_bot ⟨hF hf, hfinner⟩
  simpa only [he, hf1, one_mul] using hh

variable {J : Type*} [Group J] (D : Subgroup J) [D.Normal]

theorem normalizes_sylow_of_automorphism_cartan
    (e : D ≃* Model E) (S B : Subgroup J)
    (F H : Subgroup (MulAut (Model E)))
    (hprod : ∀ b ∈ B, ∃ f ∈ F, ∃ h ∈ H, modelAction D e b = f * h)
    (hF : F ≤ (fieldAction (F := E)).range)
    (hH : H ≤ (MulAut.conj : Model E →* MulAut (Model E)).range)
    (hHN : ∀ h ∈ H, ((S.subgroupOf D).map e.toMonoidHom).map h.toMonoidHom =
      (S.subgroupOf D).map e.toMonoidHom) :
    B.subgroupOf D ≤ normalizer (S.subgroupOf D) := by
  apply le_normalizer_iff.mpr
  intro b hb x hx
  have hbH : modelAction D e b ∈ H :=
    inner_mem_cartan_of_field_product F H hF hH _
      ⟨e b, (modelAction_inner D e b).symm⟩ (hprod b hb)
  have hm := mem_map_of_mem (modelAction D e b).toMonoidHom
    (mem_map_of_mem e.toMonoidHom hx)
  rw [hHN _ hbH] at hm
  change modelAction D e b (e x) ∈ (S.subgroupOf D).map e.toMonoidHom at hm
  rw [modelAction_apply] at hm
  obtain ⟨y, hy, he⟩ := hm
  have he' : y = MulAut.conjNormal (b : J) x := e.injective he
  rw [he'] at hy
  exact hy

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
