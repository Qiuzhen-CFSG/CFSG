module
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.Initial
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.Algebra
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.CoreReduction.Transport

/-!
# Changing the crossing representative in the terminal A₆ construction

Source: Aschbacher–Smith, printed pp.554 and 569–570. The crossing element
is chosen in `N_T(S) \ S`. Replacing it by `xs`, with `s ∈ S`, preserves
the incoming setup and the cyclic-core reduction. Normality of the conjugate
core preserves disjointness; conjugating the inversion identity preserves the
reduction. These results justify a later compatible choice without changing
any of the original records. They do not assert square stability.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction
open Subgroup
variable {G : Type*} [Group G]

private theorem conjugate_mul (a b : G) (L : Subgroup G) :
    conjugate (a * b) L = conjugate b (conjugate a L) := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext g
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, mul_inv_rev, inv_inv]
  group

private theorem center_zK (d : Setup G) (s : d.S) :
    (s : G) * d.zK = d.zK * s := by
  have hz : d.zK ∈ (center d.S).map d.S.subtype := by
    rw [d.center_s]
    exact mem_sup_right (mem_zpowers _)
  obtain ⟨z, hz, hval⟩ := hz
  simpa only [coe_mul, show (z : G) = d.zK from hval] using
    congrArg Subtype.val (mem_center_iff.mp hz s)

private theorem conjugate_core_mul (d : Setup G) (s : d.S) :
    conjugate (d.x * s) d.core = conjugate d.x d.core := by
  have hn : (d.core.subgroupOf d.S).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      ((CoreReduction.s_le_h d).trans (NormalizerCalculation.core_normalized d))
  have hnX := CoreReduction.conjugate_normal d (L := d.core) inf_le_left hn
  have hsN := (normal_subgroupOf_iff_le_normalizer
    (CoreReduction.conjugate_le d (L := d.core) inf_le_left)).mp hnX s.property
  rw [conjugate_mul]
  exact mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (conjugate d.x d.core : Set G)).inv_mem hsN)

/-- Replace the crossing element by any representative of its right `S`-coset.
All incoming source hypotheses, including disjointness and commutation of the
conjugate cores, are preserved. -/
@[expose] public def Setup.replaceX (d : Setup G) (s : d.S) : Setup G :=
  { d with
    x := d.x * s
    x_mem := d.T.mul_mem d.x_mem (d.s_le_t s.property)
    x_normalizes := (normalizer (d.S : Set G)).mul_mem d.x_normalizes
      (d.S.le_normalizer s.property)
    x_outside := by
      intro h
      apply d.x_outside
      simpa only [mul_inv_cancel_right] using d.S.mul_mem h (d.S.inv_mem s.property)
    square_mem := by
      have hsx : d.x⁻¹ * (s : G) * d.x ∈ d.S :=
        by simpa only [inv_inv] using
          (mem_normalizer_iff.mp ((normalizer (d.S : Set G)).inv_mem d.x_normalizes) s).mp
            s.property
      have heq : (d.x * (s : G)) ^ 2 = d.x ^ 2 * (d.x⁻¹ * s * d.x) * s := by simp only [pow_two]; group
      rw [heq]
      exact d.S.mul_mem (d.S.mul_mem d.square_mem hsx) s.property
    core_disjoint := by
      change Disjoint d.core (conjugate (d.x * s) d.core)
      rw [conjugate_core_mul]
      exact d.core_disjoint
    core_commutes := by
      change d.core ≤ centralizer (conjugate (d.x * s) d.core : Set G)
      rw [conjugate_core_mul]
      exact d.core_commutes
    t_conjugate := by
      calc
        (d.x * (s : G))⁻¹ * d.t * (d.x * s) = (s : G)⁻¹ * (d.x⁻¹ * d.t * d.x) * s := by group
        _ = d.zK := by rw [d.t_conjugate, mul_assoc, ← center_zK d s]; group }

/-- The conjugate core is independent of the representative of `xS`. -/
public theorem Setup.replaceX_conjugate_core (d : Setup G) (s : d.S) :
    conjugate (d.replaceX s).x (d.replaceX s).core = conjugate d.x d.core :=
  conjugate_core_mul d s

/-- The cyclic-core reduction is preserved when the crossing element is
replaced by `xs`. Inversion is transported by conjugation inside the normal
core; it is not assumed for the new representative. -/
public theorem CoreReduction.replaceX (d : Setup G) (r : CoreReduction d) (s : d.S) :
    CoreReduction (d.replaceX s) where
  cyclic := r.cyclic
  card_s := r.card_s
  inverts := by
    intro E hE hfour e he heout v hv
    have hsN := NormalizerCalculation.core_normalized d
      (CoreReduction.s_le_h d s.property)
    have hv' : (s : G) * v * (s : G)⁻¹ ∈ d.core := (mem_normalizer_iff.mp hsN v).mp hv
    have hi := r.inverts E hE hfour e he heout ((s : G) * v * (s : G)⁻¹) hv'
    change ((d.x * (s : G))⁻¹ * e * (d.x * s))⁻¹ * v *
      ((d.x * s)⁻¹ * e * (d.x * s)) = v⁻¹
    calc
      _ = (s : G)⁻¹ * ((d.x⁻¹ * e * d.x)⁻¹ * ((s : G) * v * (s : G)⁻¹) *
        (d.x⁻¹ * e * d.x)) * s := by group
      _ = v⁻¹ := by rw [hi]; group

end CFSG.Quasithin.Chapter2.A6ShadowConstruction
