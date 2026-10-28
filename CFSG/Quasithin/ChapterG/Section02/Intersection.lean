module

public import CFSG.Quasithin.ChapterG.Section02.Setup
public import Theory.GroupTheory.AlmostSpecialIntersection
public import Theory.GroupTheory.IrreducibleNormalizerCore

/-!
# The intersection layer in the rank-one almost-special argument

The two Frattini images lie in disjoint conjugate points, so their common
subgroup is elementary abelian. Its commutators with the two generators
lie in V; the normality of V extends this bound to the generated group.
Consequently the intersection is normal and lies in the two-core.
Irreducibility on V then makes that two-core centralize V.

This proves the layer calculations of G.2.3(4–5) from the earlier
Frattini, invariance and point-disjointness inputs. Those inputs, quotient
recognition and the natural-module decomposition remain separate source
obligations. Every subgroup below is the literal construction in Setup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of G.2.3, printed pp.333–334, PDF pp.344–345.
-/

open Subgroup

namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]

/-- The normal elementary intersection in the actual two-conjugate group.
The Frattini input is G.2.2(2); the point disjointness comes from the
rank-one natural action. No conclusion about this intersection is assumed. -/
public theorem rank_one_intersection_layer (D : Setup G) (g : G)
    (hp : IsPGroup 2 D.U)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hpoint : D.V₁ ≤ D.V)
    (hIV : D.I g ≤ normalizer (D.V : Set G))
    (hg : g ∈ normalizer (D.V : Set G))
    (hdis : Disjoint D.V₁ (conjugate D.V₁ g)) :
    D.V ≤ D.S₂ g ∧ D.S₂ g ≤ D.S g ∧
    (D.S₂ g |>.subgroupOf (D.I g)).Normal ∧
    ⁅D.S₂ g, D.I g⁆ ≤ D.V ∧ IsElementaryAbelian 2 (D.S₂ g) := by
  let f := (MulAut.conj g⁻¹).toMonoidHom
  have hVg : D.V.map f = D.V :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (D.V : Set G)).inv_mem hg)
  have hVU : D.V ≤ D.U := le_conjugateSpanBy _ _
  have hVE : D.V ≤ D.S₂ g := le_inf hVU (by
    change D.V ≤ D.U.map f
    rw [← hVg]
    exact map_mono hVU)
  have hderived := derived_le_of_frattini_image_le hp hf
  have hother : ⁅conjugate D.U g, conjugate D.U g⁆ ≤ D.V := by
    have hm := map_mono (f := f) (hderived.trans hpoint)
    rwa [map_commutator, hVg] at hm
  have hcomm : ⁅D.S₂ g, D.I g⁆ ≤ D.V :=
    intersection_commutator_sup_le (hderived.trans hpoint) hother hIV
  have hnorm : D.I g ≤ normalizer (D.S₂ g : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans hVE)
  have hEI : D.S₂ g ≤ D.I g := inf_le_left.trans le_sup_left
  have helem : IsElementaryAbelian 2 (D.S₂ g) :=
    conjugate_intersection_elementary hp hf g⁻¹ hdis
  let := helem
  exact ⟨hVE, le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _) hEI hnorm,
    (normal_subgroupOf_iff_le_normalizer hEI).mpr hnorm, hcomm, helem⟩

/-- The central first layer in G.2.3(4), with the source irreducible action
on V expressed by invariant subgroups. Normality is relative to I. -/
public theorem rank_one_central_first_layer (D : Setup G) (g : G)
    (hp : IsPGroup 2 D.U)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hpoint : D.V₁ ≤ D.V)
    (hIV : D.I g ≤ normalizer (D.V : Set G))
    (hg : g ∈ normalizer (D.V : Set G))
    (hdis : Disjoint D.V₁ (conjugate D.V₁ g))
    (hLI : D.L ≤ D.I g)
    (hirr : ∀ A : Subgroup G, A ≤ D.V → D.L ≤ normalizer (A : Set G) →
      A = ⊥ ∨ A = D.V) :
    D.V ≤ D.S g ⊓ centralizer (D.S g : Set G) := by
  have h := D.rank_one_intersection_layer g hp hf hpoint hIV hg hdis
  have hVU : D.V ≤ D.U := le_conjugateSpanBy _ _
  have hVI : D.V ≤ D.I g := hVU.trans le_sup_left
  have hc := pCoreIn_le_centralizer_of_irreducible D.V D.L (D.I g)
    (hp.of_injective (inclusion hVU) (inclusion_injective hVU)) hVI hIV hLI hirr
  exact le_inf (h.1.trans h.2.1) (le_centralizer_iff.mp hc)

end CFSG.Quasithin.ChapterG.Section02.Setup
