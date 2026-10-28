module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.Initial
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.Algebra
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.ActionNormalizer
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowConstruction.NormalizerGeometry.FourGroupChoice

/-!
# Assembly for the terminal A₆ normalizer geometry

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
p.570, following Lemma 2.5.27.

The algebra module proves the dihedral factor, disjointness, recovery of `E`
from `EEˣ`, and the Sylow order calculation. The assembly combines these
results with the compatible four-group choice and the action-normalizer lift
to construct every field of `NormalizerGeometry`.

The choice may replace `x` by `xs`, where `s ∈ S`; the resulting geometry
retains this representative. `CoreReduction.replaceX` preserves the cyclic
core reduction, so the unchanged `terminal_pair_of_geometry` applies to the
replacement setup. Square stability follows from the source centralizer
premise `C_G(t) ≤ H` and the fusion calculation, not from `x² ∈ S` alone.

`Setup.exists_normalizer_geometry_of_source` takes exactly that centralizer
premise, `CoreReduction`, and the three concrete A₆ model inputs. The source
assembly must discharge these inputs before claiming the book theorem.
The fixed-setup construction `geometry_of_local_calculations` is preserved.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowConstruction
open Subgroup NormalizerCalculation
variable {G : Type*} [Group G] [Finite G]

/-- Assemble all fields of the published geometry target from local
calculations for a fixed setup. The source construction below supplies these
calculations after choosing a compatible crossing representative. -/
public noncomputable def geometry_of_local_calculations (d : Setup G) (r : CoreReduction d)
    (E : Subgroup G) [IsKleinFour E] (hE : E ≤ d.sk)
    (hz : d.zK ∈ E) (e : G) (he : e ∈ E) (heout : e ∉ zpowers d.zK)
    (hsquare : d.x ^ 2 ∈ normalizer (E : Set G))
    (hcentralizes : d.x⁻¹ * e * d.x ∈
      centralizer ((d.K ⊓ normalizer (E : Set G) : Subgroup G) : Set G))
    (hgenerate : d.H ⊓ normalizer (E : Set G) =
      (zpowers (d.x⁻¹ * e * d.x) ⊔ d.core) ⊔ (d.K ⊓ normalizer (E : Set G)))
    (hsymmetric : Nonempty ((d.K ⊓ normalizer (E : Set G) : Subgroup G) ≃*
      Equiv.Perm (Fin 4))) : NormalizerGeometry d := by
  have hdisj : Disjoint (zpowers (d.x⁻¹ * e * d.x) ⊔ d.core)
      (d.K ⊓ normalizer (E : Set G)) :=
    (factors_disjoint d r E hE he heout).mono le_rfl inf_le_left
  have hcomm := factors_commute d E hcentralizes
  have hdihedral := conjugate_dihedral d r E hE he heout
  have hnorm : d.H ⊓ normalizer (E : Set G) ≤
      normalizer ((E ⊔ conjugate d.x E : Subgroup G) : Set G) := by
    rw [hgenerate]
    refine sup_le (sup_le (zpowers_le.mpr ?_)
      (core_normalizes_product d r E hE hz he heout))
      (k_normalizer_normalizes_product d E hz he heout hcentralizes)
    apply (E ⊔ conjugate d.x E).le_normalizer
    apply mem_sup_right
    exact ⟨e, he, by simp⟩
  have hsame : d.H ⊓ normalizer ((E ⊔ conjugate d.x E : Subgroup G) : Set G) =
      d.H ⊓ normalizer (E : Set G) :=
    le_antisymm (normalizer_le d r E hE) (le_inf inf_le_left hnorm)
  have hmodel : Nonempty ((d.H ⊓ normalizer (E : Set G) : Subgroup G) ≃*
      DihedralGroup 4 × Equiv.Perm (Fin 4)) := by
    obtain ⟨m, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
      (zpowers (d.x⁻¹ * e * d.x) ⊔ d.core) (d.K ⊓ normalizer (E : Set G)) hdisj hcomm
    obtain ⟨a⟩ := hdihedral
    obtain ⟨b⟩ := hsymmetric
    exact ⟨(MulEquiv.subgroupCongr hgenerate).trans (m.symm.trans (a.prodCongr b))⟩
  exact {
    E := E
    four := inferInstance
    le_sk := hE
    zK_mem := hz
    e := e
    e_mem := he
    e_outside := heout
    square_normalizes := hsquare
    same_normalizer := hsame
    product_normalizer := hsame.trans hgenerate
    factors_disjoint := hdisj
    factors_commute := hcomm
    dihedral := hdihedral
    symmetric := hsymmetric
    card_base := card_base_of_normalizer_model d E hE hmodel }

/-- Construct the terminal normalizer geometry after a permissible change
`x ↦ xs`. The four-group, reflection, square stability, normalizer equalities,
commuting disjoint factors, their actual model isomorphisms, and the base
order 64 are all derived. The explicit inputs are the cyclic-core reduction,
the three concrete A₆ model calculations, and `C_G(t) ≤ H` from 2.5.22(2).

For the terminal-pair assembly use `CoreReduction.replaceX d r s` together
with the resulting geometry. `Setup.replaceX` leaves `H`, `K`, `S`, `T`,
`M`, `t`, and `z` unchanged; the crossing element is `d.x * s`. -/
public theorem Setup.exists_normalizer_geometry_of_source (d : Setup G)
    (r : CoreReduction d)
    (m : SquareMembership.Fusion.ModelFacts)
    (n : ActionNormalizer.ModelFacts)
    (o : FourGroupChoice.ReflectionOrbit (CoreReduction.imageSylow d))
    (hC : centralizer ({d.t} : Set G) ≤ d.H) :
    ∃ s : d.S, Nonempty (NormalizerGeometry (d.replaceX s)) := by
  obtain ⟨s, E, e, hfour, hE, hz, he, heout, hsquare, hcentralizes⟩ :=
    d.exists_compatible_four_of_source r m n o hC
  let : IsKleinFour E := hfour
  have r' := CoreReduction.replaceX d r s
  have hgenerate :=
    ActionNormalizer.normalizer_eq_of_model (d.replaceX s) r' n E hE he heout
  have hsymmetric :=
    ActionNormalizer.normalizer_symmetric_of_model (d.replaceX s) n E hE
  exact ⟨s, ⟨geometry_of_local_calculations (d.replaceX s) r' E hE hz e he heout
    hsquare hcentralizes hgenerate hsymmetric⟩⟩

end CFSG.Quasithin.Chapter2.A6ShadowConstruction
