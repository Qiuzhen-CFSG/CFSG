module

public import Theory.Representation.BinaryPermutation.FiveGeometry
public import Theory.GroupTheory.ElementFusionWeakClosure
public import Theory.GroupTheory.IntersectingConjugateFusion

/-!
# Singular intersections in the A₅ case

This proves both conclusions of 13.6.24 from the actual earlier inputs:
the four-dimensional binary core coordinates and its two nonzero normalizer
orbits, fusion control from 13.2.6(2), abelian centralizer span from 13.6.2,
and `C_G(v) ≤ N_G(V)` from 13.6.7(1). No intersection or commutation
conclusion is included among the inputs.

Uniqueness through a nonsingular vector excludes all such vectors from a
proper conjugate intersection. The concrete minus form then makes the
intersection an order-two singular subgroup. Its generator can be moved
to `z`, where abelian centralizer generation forces commutation. The final
lemma supplies clause (f) of F.9.8, including conjugators normalizing V.

Conjugation is left conjugation; invert the source's conjugator to use
the displayed formulas. The parent §13.6 assembly must discharge every
earlier input and provide the actual module coordinates.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 13.6.24, printed p.933, and p.935.
-/

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction

open Subgroup BinaryPermutation.FiveGeometry

variable {G : Type*} [Group G]

/-- The two orbits of the actual orthogonal A₅-module, expressed using its
quadratic form and an actual additive-group identification. This is the
earlier module geometry, not an assertion about conjugate intersections. -/
@[expose] public def HasFiveModuleOrbits (V : Subgroup G)
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 5))) : Prop :=
  ∀ x y : V, x ≠ 1 → y ≠ 1 → form (e x).toAdd = form (e y).toAdd →
    ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = y.val

/-- The nonsingular part of 13.6.24(1), from fusion and 13.6.7(1). -/
public theorem intersection_singular
    (V : Subgroup G) (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (v : V) (hv : form (e v).toAdd ≠ 0)
    (horbit : HasFiveModuleOrbits V e)
    (hfusion : ∀ a : G, MulAut.conj a v.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = MulAut.conj a v.val)
    (hCv : centralizer ({v.val} : Set G) ≤ normalizer (V : Set G))
    (g : G) (hg : g ∉ normalizer (V : Set G))
    (x : (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    form (e ⟨x.val, x.property.1⟩).toAdd = 0 := by
  by_contra hx
  have hv1 : v ≠ 1 := by
    intro heq
    apply hv
    simp [heq]
  have hx1 : (⟨x.val, x.property.1⟩ : V) ≠ 1 := by
    intro heq
    apply hx
    rw [heq, map_one]
    exact QuadraticMap.map_zero _
  have he : form (e v).toAdd = form (e ⟨x.val, x.property.1⟩).toAdd := by
    have hb : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b := by decide
    exact hb _ _ hv hx
  obtain ⟨n, hn, hnx⟩ := horbit v ⟨x.val, x.property.1⟩ hv1 hx1 he
  have hmem : MulAut.conj n v.val ∈ V.map (MulAut.conj g).toMonoidHom :=
    hnx ▸ x.property.2
  exact hg (mem_normalizer_iff_map_conj_eq.mpr
    (conjugate_eq_of_fusion_of_mem_normalizer_orbit V v.val hfusion hCv g n hn hmem))

/-- Lemma 13.6.24, conditional only on its preceding fusion, module,
abelian-span and centralizer-containment facts. The first two conclusions
say literally that the intersection is a singular point. -/
public theorem source_13_6_24_from_earlier
    (V : Subgroup G) (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (v z : V) (hv : form (e v).toAdd ≠ 0) (hz : z ≠ 1)
    (hqz : form (e z).toAdd = 0)
    (horbit : HasFiveModuleOrbits V e)
    (hfusion : ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val)
    [IsMulCommutative (centralizerConjugateClosure V z.val)]
    (hCv : centralizer ({v.val} : Set G) ≤ normalizer (V : Set G))
    (g : G) (hg : g ∉ normalizer (V : Set G))
    (hinter : V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) = 2 ∧
      (∀ x : (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G),
        form (e ⟨x.val, x.property.1⟩).toAdd = 0) ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hv1 : v ≠ 1 := by
    intro heq
    apply hv
    simp [heq]
  have hs := intersection_singular V e v hv horbit (hfusion v hv1) hCv g hg
  refine ⟨card_eq_two_of_singular V _ inf_le_left e hinter hs, hs, ?_⟩
  apply commutator_conjugate_eq_bot_of_intersection_fusion V z.val g
    (hfusion z hz) hinter
  intro x hx hx1
  exact horbit ⟨x, hx.1⟩ z (fun heq => hx1 (congrArg Subtype.val heq)) hz
    ((hs ⟨x, hx⟩).trans hqz.symm)

/-- Clause (f) of F.9.8 from the same earlier data. The case where the
conjugator normalizes V uses its abelianness, rather than excluding that case. -/
public theorem commuting_of_contains_singular_point
    (V : Subgroup G) (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (v z : V) (hv : form (e v).toAdd ≠ 0) (hz : z ≠ 1)
    (hqz : form (e z).toAdd = 0)
    (horbit : HasFiveModuleOrbits V e)
    (hfusion : ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val)
    [IsMulCommutative (centralizerConjugateClosure V z.val)]
    (hCv : centralizer ({v.val} : Set G) ≤ normalizer (V : Set G))
    (g : G) (hzg : zpowers z.val ≤ V.map (MulAut.conj g).toMonoidHom) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  by_cases hg : g ∈ normalizer (V : Set G)
  · have hgV : V.map (MulAut.conj g).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp hg
    rw [hgV]
    exact le_bot_iff.mp ((commutator_mono (le_centralizerConjugateClosure V z.val)
      (le_centralizerConjugateClosure V z.val)).trans_eq
        (commutator_self_eq_bot_iff.mpr inferInstance))
  · apply (source_13_6_24_from_earlier V e v z hv hz hqz horbit hfusion hCv g hg ?_).2.2
    intro heq
    have hmem : z.val ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom :=
      ⟨z.property, hzg (mem_zpowers _)⟩
    exact hz (Subtype.ext (mem_bot.mp (heq ▸ hmem)))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
