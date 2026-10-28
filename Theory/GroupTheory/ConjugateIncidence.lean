module

public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Conjugate subgroups through a fixed element

Transitivity of a normalizer on the nonidentity elements of a subgroup allows
one to adjust a conjugating element to centralize a prescribed common element.
Also, bounds on intersections with distinct conjugates give bounds on
centralizers of subgroups which cannot lie in those intersections.

These are the elementary group-theoretic steps used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemmas 11.5.2(1) and 11.5.3(2),
combined 1 March 2004 manuscript, printed p. 779. We use left conjugation
`x ↦ g * x * g⁻¹`; replacing `g` by `g⁻¹` gives the source convention.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- If the normalizer can carry `z` to each nonidentity element of `V`,
every conjugate of `V` containing `z` is obtained by an element centralizing `z`.
The adjustment is on the right of the original conjugating element. -/
public theorem exists_centralizer_conjugator (V : Subgroup G) {z : G}
    (hz1 : z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 →
      ∃ l ∈ normalizer (V : Set G), (MulAut.conj l) z = u)
    (g : G) (hg : z ∈ V.map (MulAut.conj g).toMonoidHom) :
    ∃ c ∈ centralizer ({z} : Set G),
      V.map (MulAut.conj c).toMonoidHom = V.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨u, hu, hgu⟩ := hg
  have hu1 : u ≠ 1 := by
    intro heq
    apply hz1
    simpa [heq] using hgu.symm
  obtain ⟨l, hl, hlz⟩ := htrans u hu hu1
  refine ⟨g * l, ?_, ?_⟩
  · apply mem_centralizer_singleton_iff.mpr
    have hc : (MulAut.conj (g * l)) z = z := by
      simpa only [map_mul, MulAut.mul_apply, hlz, MulEquiv.coe_toMonoidHom] using hgu
    simpa only [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] using hc
  · have hfix := mem_normalizer_iff_map_conj_eq.mp hl
    calc
      V.map (MulAut.conj (g * l)).toMonoidHom =
          (V.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
        rw [map_map]
        congr 1
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply, mul_inv_rev, mul_assoc]
      _ = V.map (MulAut.conj g).toMonoidHom := congrArg _ hfix

/-- Suppose intersections of `V` with its distinct conjugates lie in members
of `family`. If `U ≤ V` lies in no member of that family, every element
centralizing `U` normalizes `V`. -/
public theorem centralizer_le_normalizer_of_conjugate_intersection
    (V U : Subgroup G) (family : Set (Subgroup G)) (hUV : U ≤ V)
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ W ∈ family, V ⊓ V.map (MulAut.conj g).toMonoidHom ≤ W)
    (havoid : ∀ W ∈ family, ¬ U ≤ W) :
    centralizer (U : Set G) ≤ normalizer (V : Set G) := by
  intro c hc
  by_contra hcn
  obtain ⟨W, hW, hVW⟩ := hbound c hcn
  apply havoid W hW
  apply le_trans _ hVW
  refine le_inf hUV ?_
  have hfix := mem_normalizer_iff_map_conj_eq.mp
    (centralizer_le_normalizer (U : Set G) hc)
  rw [← hfix]
  exact map_mono hUV

end Subgroup
