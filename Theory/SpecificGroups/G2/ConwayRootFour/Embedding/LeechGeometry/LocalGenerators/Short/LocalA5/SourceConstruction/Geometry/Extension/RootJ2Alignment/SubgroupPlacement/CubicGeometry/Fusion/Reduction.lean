module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.LocalData

/-!
# Correcting ambient cubic fusion into the tetrahedral centralizer

An ambient conjugator between cyclic subgroups need not centralize the literal
scalar tetrahedral subgroup `I`. If its transported copy of `I` is conjugate
back inside the cubic centralizer, the corrected conjugator normalizes `I`.
Realizing that normalizer action inside the same cubic centralizer then corrects
it to fix `I` pointwise. Thus the cyclic subgroup image is preserved throughout.
The final conjugator is `d⁻¹ * (c * g)` for Lean's left-conjugation convention.

The three explicit propositions below separate the concrete model obligations:
ambient fusion of fixed-free cubics, the tetrahedral orbit in a cubic centralizer,
and realization of the ambient normalizer action there. They are not proved
by this module. In particular, setwise tetrahedral conjugacy alone does not
supply the pointwise-centralizer conclusion. The orbit and action obligations
refer to `I = scalarFour.range`, not an unmarked abstract alternating group.

Source: Aschbacher, *Sporadic Groups* (1994), 48.3, 49.1–49.2 (p.280),
and the proof of 49.5 (pp.283–284). The source root-A₄ class and cubic class
must be identified on the actual Leech central quotient before using those
source facts to discharge the model obligations. No G₂(4) identification,
faithfulness premise, long frame, or root-J₂ placement enters this reduction.
-/

@[expose] public noncomputable section

open Atlas.Conway Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction

namespace CubicFusion

/-- The ambient fixed-free class, with no tetrahedral-centralizer restriction. -/
def AmbientFusion : Prop :=
  ∀ a b : LeechCentralQuotient, orderOf a = 3 → orderOf b = 3 →
    CubicFixedFree a → CubicFixedFree b →
    ∃ g : LeechCentralQuotient,
      Subgroup.zpowers a = (Subgroup.zpowers b).map (MulAut.conj g).toMonoidHom

/-- Setwise conjugacy of the literal tetrahedral subgroup inside a cubic centralizer. -/
def TetrahedralOrbit : Prop :=
  ∀ a : LeechCentralQuotient, a ∈ centralizerI → orderOf a = 3 → CubicFixedFree a →
    ∀ g : LeechCentralQuotient,
      Subgroup.zpowers a ≤ Subgroup.centralizer
        (I.map (MulAut.conj g).toMonoidHom : Set LeechCentralQuotient) →
      ∃ c ∈ Subgroup.centralizer (Subgroup.zpowers a : Set LeechCentralQuotient),
        (I.map (MulAut.conj g).toMonoidHom).map (MulAut.conj c).toMonoidHom = I

/-- The cubic centralizer realizes the ambient normalizer's action on the literal I. -/
def TetrahedralNormalizerAction : Prop :=
  ∀ a : LeechCentralQuotient, a ∈ centralizerI → orderOf a = 3 → CubicFixedFree a →
    ∀ n ∈ Subgroup.normalizer (I : Set LeechCentralQuotient),
      ∃ d ∈ Subgroup.centralizer (Subgroup.zpowers a : Set LeechCentralQuotient),
        ∀ i ∈ I, MulAut.conj d i = MulAut.conj n i

private theorem map_conj_mul {G : Type*} [Group G] (P : Subgroup G) (g h : G) :
    P.map (MulAut.conj (g * h)).toMonoidHom =
      (P.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_eq_self {G : Type*} [Group G] (P : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.centralizer (P : Set G)) :
    P.map (MulAut.conj g).toMonoidHom = P :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ hg)

/-- Setwise orbit control and normalizer action control correct an ambient conjugator
into the pointwise centralizer. No oriented conjugacy of cyclic generators is needed. -/
private theorem correct_conjugator {G : Type*} [Group G] (J P Q : Subgroup G)
    (hQ : Q ≤ Subgroup.centralizer (J : Set G)) (g : G)
    (hPQ : P = Q.map (MulAut.conj g).toMonoidHom)
    (horbit : ∀ x : G,
      P ≤ Subgroup.centralizer (J.map (MulAut.conj x).toMonoidHom : Set G) →
      ∃ c ∈ Subgroup.centralizer (P : Set G),
        (J.map (MulAut.conj x).toMonoidHom).map (MulAut.conj c).toMonoidHom = J)
    (haction : ∀ n ∈ Subgroup.normalizer (J : Set G),
      ∃ d ∈ Subgroup.centralizer (P : Set G),
        ∀ i ∈ J, MulAut.conj d i = MulAut.conj n i) :
    ∃ x ∈ Subgroup.centralizer (J : Set G),
      P = Q.map (MulAut.conj x).toMonoidHom := by
  have hPg : P ≤ Subgroup.centralizer
      (J.map (MulAut.conj g).toMonoidHom : Set G) := by
    rw [hPQ]
    rintro _ ⟨q, hq, rfl⟩ _ ⟨i, hi, rfl⟩
    exact (MulAut.conj g).map_mul i q ▸ (MulAut.conj g).map_mul q i ▸
      congrArg (MulAut.conj g) (hQ hq i hi)
  obtain ⟨c, hc, hcJ⟩ := horbit g hPg
  have hn : c * g ∈ Subgroup.normalizer (J : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change J.map (MulAut.conj (c * g)).toMonoidHom = J
    rw [map_conj_mul]
    exact hcJ
  obtain ⟨d, hd, hdJ⟩ := haction (c * g) hn
  refine ⟨d⁻¹ * (c * g), ?_, ?_⟩
  · intro i hi
    have he : MulAut.conj (d⁻¹ * (c * g)) i = i := by
      calc
        MulAut.conj (d⁻¹ * (c * g)) i =
            MulAut.conj d⁻¹ (MulAut.conj (c * g) i) := by
          simp [MulAut.conj_apply, mul_assoc]
        _ = i := by rw [← hdJ i hi]; simp [MulAut.conj_apply, mul_assoc]
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · rw [map_conj_mul, map_conj_mul, ← hPQ, map_conj_eq_self P hc,
      map_conj_eq_self P ((Subgroup.centralizer (P : Set G)).inv_mem hd)]

/-- Conditional relative fusion; all three concrete conjugacy obligations remain explicit. -/
theorem fixedFreeCubicFusion_of_conjugacy_data (hamb : AmbientFusion)
    (horbit : TetrahedralOrbit) (haction : TetrahedralNormalizerAction) :
    FixedFreeCubicFusion := by
  intro a b ha hb hoa hob hfa hfb
  obtain ⟨g, hg⟩ := hamb a b hoa hob hfa hfb
  exact correct_conjugator I (Subgroup.zpowers a) (Subgroup.zpowers b)
    (Subgroup.zpowers_le.mpr hb) g hg (horbit a ha hoa hfa) (haction a ha hoa hfa)

end CubicFusion
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
