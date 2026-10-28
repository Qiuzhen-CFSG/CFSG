module

public import Theory.SpecificGroups.OrthogonalFourBinary.NaturalAction
public import Theory.GroupTheory.IntersectingConjugateFusion
public import Theory.GroupTheory.ConjugateSpanOrder
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Intersecting conjugates commute: Lemma 15.3.62

The inputs are the genuine natural orthogonal action, the centralizer
identity 15.3.4, the element-fusion and totally singular intersection
conclusions of 15.3.46, and the abelianness conclusion of 15.3.50.

Fusion corrects a conjugator into `C_G(Z)`. The concrete binary
orthogonal action transports a nonidentity intersection vector to the
fixed singular involution. We identify the centralizer-generated closure
with the source's conjugate span, apply the abelianness hypothesis there,
and then transport commutation back. Thus neither an intersection-orbit
hypothesis nor a separate abelian-closure hypothesis is left over.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 15.3.62, printed p.1151.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam

open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] {V M Mc : Subgroup G} {z : G}

/-- The transporter assertion in 15.3.62(1), from the fusion conclusion of
15.3.46(1) and the centralizer identity 15.3.4. -/
theorem lemma_15_3_62_1
    (hM : M ≤ normalizer (V : Set G))
    (hMc : Mc = centralizer (zpowers z : Set G))
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ m ∈ M, MulAut.conj m z = MulAut.conj a z)
    (g : G) (hZ : zpowers z ≤ V.map (MulAut.conj g).toMonoidHom) :
    ∃ c ∈ Mc, V.map (MulAut.conj c).toMonoidHom =
      V.map (MulAut.conj g).toMonoidHom := by
  have hf : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n z = MulAut.conj a z := by
    intro a ha
    obtain ⟨m, hm, he⟩ := hfusion a ha
    exact ⟨m, hM hm, he⟩
  obtain ⟨c, hc⟩ := exists_centralizer_conjugator_of_element_fusion hf
    (hZ (mem_zpowers z))
  refine ⟨c, ?_, hc⟩
  simpa only [hMc, zpowers_eq_closure, centralizer_closure] using c.property

/-- The centralizer-generated group is exactly the span supplied by 15.3.50. -/
theorem centralizerConjugateClosure_eq_localSpan
    (hMc : Mc = centralizer (zpowers z : Set G)) :
    centralizerConjugateClosure V z = conjugateSpanBy V Mc := by
  rw [centralizerConjugateClosure_eq_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨c, v, hv, he⟩
    refine ⟨c, ?_, v, hv, he⟩
    simpa only [hMc, zpowers_eq_closure, centralizer_closure] using c.property
  · rintro ⟨c, hc, v, hv, he⟩
    have hc' : c ∈ centralizer ({z} : Set G) := by
      simpa only [hMc, zpowers_eq_closure, centralizer_closure] using hc
    exact ⟨⟨c, hc'⟩, v, hv, he⟩

/-- Lemma 15.3.62(2). The singular orbit is derived from the full natural
orthogonal action; the abelian closure is transported from 15.3.50. -/
theorem lemma_15_3_62_2
    (d : OrthogonalFourBinary.NaturalAction V M)
    (hzV : z ∈ V) (hz : z ≠ 1) (hzs : d.singular ⟨z, hzV⟩)
    (hMc : Mc = centralizer (zpowers z : Set G))
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ m ∈ M, MulAut.conj m z = MulAut.conj a z)
    (hsingular : ∀ g : G, g ∉ M →
      ∀ x : ↥(V ⊓ V.map (MulAut.conj g).toMonoidHom),
        d.singular ⟨x, x.property.1⟩)
    [IsMulCommutative (conjugateSpanBy V Mc)]
    (g : G) (hinter : V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hclosure := centralizerConjugateClosure_eq_localSpan (V := V) hMc
  let : IsMulCommutative (centralizerConjugateClosure V z) := hclosure.symm ▸ inferInstance
  by_cases hg : g ∈ M
  · have hVg : V.map (MulAut.conj g).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (d.normalizes hg)
    rw [hVg]
    apply le_bot_iff.mp
    exact (commutator_mono (le_conjugateSpanBy V Mc) (le_conjugateSpanBy V Mc)).trans_eq
      (commutator_self_eq_bot_iff.mpr inferInstance)
  · refine commutator_conjugate_eq_bot_of_intersection_fusion V z g ?_ hinter ?_
    · intro a ha
      obtain ⟨m, hm, he⟩ := hfusion a ha
      exact ⟨m, d.normalizes hm, he⟩
    · intro x hx hx1
      obtain ⟨m, hm, he⟩ := d.exists_conjugator_of_singular
        ⟨x, hx.1⟩ ⟨z, hzV⟩
        (fun h => hx1 (congrArg Subtype.val h))
        (fun h => hz (congrArg Subtype.val h))
        (hsingular g hg ⟨x, hx⟩) hzs
      exact ⟨m, d.normalizes hm, he⟩

/-- Pairwise transitivity on the conjugates containing `Z`, the set-action
form of 15.3.62(1). -/
theorem lemma_15_3_62_1_transitive
    (hM : M ≤ normalizer (V : Set G))
    (hMc : Mc = centralizer (zpowers z : Set G))
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ m ∈ M, MulAut.conj m z = MulAut.conj a z)
    (g h : G)
    (hg : zpowers z ≤ V.map (MulAut.conj g).toMonoidHom)
    (hh : zpowers z ≤ V.map (MulAut.conj h).toMonoidHom) :
    ∃ c ∈ Mc, (V.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj c).toMonoidHom = V.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨a, ha, haV⟩ := lemma_15_3_62_1 hM hMc hfusion g hg
  obtain ⟨b, hb, hbV⟩ := lemma_15_3_62_1 hM hMc hfusion h hh
  refine ⟨b * a⁻¹, Mc.mul_mem hb (Mc.inv_mem ha), ?_⟩
  rw [← haV, map_map]
  have he : (MulAut.conj (b * a⁻¹)).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj b).toMonoidHom := by
    ext v
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, hbV]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
