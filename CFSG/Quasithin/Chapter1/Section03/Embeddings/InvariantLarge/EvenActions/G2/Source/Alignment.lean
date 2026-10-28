module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.Model
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Simultaneous Sylow and torus placement in G₂

Sylow conjugacy first places the Sylow two-subgroup in the standard unipotent
subgroup. Its normalizer is the Borel. An odd-prime subgroup of this normalizer
can then be conjugated into the split torus by an element of the Borel, preserving
the first placement. This uses the subgroup's normalizer containment explicitly;
the source application must derive that containment from A.3.15(5).

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed pp.50–51
and p.511. The actual octonion model and normalizer proof are imported from Model.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
variable {G E : Type*} [Group G] [Finite G] [Field E] [Finite E] [CharP E 2]
variable {p : ℕ} [Fact p.Prime]

theorem sylow_torus_alignment (e : G ≃* Model E) (R : Sylow 2 G)
    (B : Subgroup G) (hB : IsPGroup p B) (hp : p ≠ 2)
    (hBN : B ≤ normalizer (R : Set G)) :
    ∃ e' : G ≃* Model E,
      (R : Subgroup G).map e'.toMonoidHom = unipotent ∧
      B.map e'.toMonoidHom ≤ splitTorus := by
  let Q := R.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model E) Q (sylow (F := E))
  let e₁ : G ≃* Model E := e.trans (MulAut.conj g)
  have hR : (R : Subgroup G).map e₁.toMonoidHom = unipotent := by
    change (R : Subgroup G).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map]
    exact congrArg Sylow.toSubgroup hg
  have hBB : B.map e₁.toMonoidHom ≤ borel := by
    rw [← normalizer_unipotent, ← hR, ← map_equiv_normalizer_eq]
    exact map_mono hBN
  obtain ⟨u, hu, hBu⟩ := conjugate_borel_pSubgroup_into_torus
    (B.map e₁.toMonoidHom) (hB.map e₁.toMonoidHom) hp hBB
  refine ⟨e₁.trans (MulAut.conj u), ?_, ?_⟩
  · change (R : Subgroup G).map ((MulAut.conj u).toMonoidHom.comp e₁.toMonoidHom) = _
    rw [← map_map, hR]
    exact mem_normalizer_iff_map_conj_eq.mp ((normalizer_unipotent (E := E)).symm ▸ hu)
  · change B.map ((MulAut.conj u).toMonoidHom.comp e₁.toMonoidHom) ≤ _
    rwa [← map_map]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source
