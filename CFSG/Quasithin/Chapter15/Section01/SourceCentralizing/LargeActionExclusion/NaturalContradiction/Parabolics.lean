module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.Projection

/-!
# The three parabolics in original 15.1.29

The selected parabolics live in the original ambient group. Their residuals
are O²(Pᵢ), whereas Q₂ is O₂(P₂). The geometric input below separates the
construction of these subgroups from the Sylow argument: Q is Sylow in QY₃
and is not Sylow in QY₂. Consequently no element normalizing Q can exchange
Y₂ and Y₃. This proves T-normalization of Y₂, P₂ and Q₂.

`NaturalParabolicGeometry` is an explicit input, not a construction of the
parabolics from the natural module. That construction remains a separate
source obligation.

Source: Aschbacher--Smith, 15.1.29, printed pp.1103--1104.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The selected end node, its neighbor, and the other end node.
The source construction must choose these inside the actual LS. -/
structure NaturalParabolics (d : CaseIComponentData T M Mc V) where
  P0 : Subgroup G
  P2 : Subgroup G
  P3 : Subgroup G

namespace NaturalParabolics
variable {d : CaseIComponentData T M Mc V}

def Y0 (p : NaturalParabolics d) : Subgroup G :=
  (pResidual 2 p.P0).map p.P0.subtype
def Y2 (p : NaturalParabolics d) : Subgroup G :=
  (pResidual 2 p.P2).map p.P2.subtype
def Y3 (p : NaturalParabolics d) : Subgroup G :=
  (pResidual 2 p.P3).map p.P3.subtype
def K (p : NaturalParabolics d) : Subgroup G := p.Y0 ⊔ p.Y2
def Q2 (p : NaturalParabolics d) : Subgroup G := p.P2.pCoreIn 2

end NaturalParabolics

/-- Source geometry preceding the C.1.34 application. The product clause
is the literal M = ⟨Y₀,T⟩ C_M(V), not uniqueness of an overgroup. -/
structure NaturalParabolicGeometry {d : CaseIComponentData T M Mc V}
    (p : NaturalParabolics d) : Prop where
  parabolics_le : p.P0 ≤ d.L ⊔ d.S ∧ p.P2 ≤ d.L ⊔ d.S ∧ p.P3 ≤ d.L ⊔ d.S
  sylow_le : d.S ≤ p.P0 ∧ d.S ≤ p.P2 ∧ d.S ≤ p.P3
  first_le : p.P0 ≤ M
  first_core : p.P0.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G)
  second_supplement : p.P2 = p.Y2 ⊔ d.S
  second_join : p.P2 = ((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊔ p.Y2
  adjacent_not_sylow :
    ¬ Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (V : Set G)) p.P2
  remote_sylow : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (V : Set G))
    (((T : Subgroup G) ⊓ centralizer (V : Set G)) ⊔ p.Y3)
  end_orbit : ∀ t ∈ (T : Subgroup G),
    p.Y2.map (MulAut.conj t).toMonoidHom = p.Y2 ∨
      p.Y2.map (MulAut.conj t).toMonoidHom = p.Y3
  perfect : Group.IsPerfect p.K
  moving : ⁅d.nineMovingPlane,p.Y0⁆ = d.nineMovingPlane
  product : ∀ m ∈ M, ∃ x ∈ p.Y0 ⊔ (T : Subgroup G),
    ∃ c ∈ M ⊓ centralizer (V : Set G), x * c = m

namespace NaturalParabolicGeometry
variable {d : CaseIComponentData T M Mc V} {p : NaturalParabolics d}

/-- The Sylow distinction prevents the proposed exchange of the two ends. -/
theorem normalizes_second_residual (a : NaturalParabolicGeometry p)
    (hM : IsOrderingMaximal T M) (h : PreparedChosenModule T M V) :
    (T : Subgroup G) ≤ normalizer (p.Y2 : Set G) := by
  let Q := (T : Subgroup G) ⊓ centralizer (V : Set G)
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      ((hM.1.2.trans h.normalized).trans (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases a.end_orbit t ht with he | he
  · exact he
  · exfalso
    have hQ : Q.map (MulAut.conj t).toMonoidHom = Q :=
      mem_normalizer_iff_map_conj_eq.mp (hTQ ht)
    have hjoin : p.P2.map (MulAut.conj t).toMonoidHom = Q ⊔ p.Y3 := by
      rw [a.second_join, Subgroup.map_sup, hQ, he]
    apply a.adjacent_not_sylow
    apply (Chapter1.IsSylowIn.map_iff (MulAut.conj t).toMonoidHom
      (MulAut.conj t).injective).mp
    rw [hQ, hjoin]
    exact a.remote_sylow

/-- Since P₂=Y₂S, normalization of the residual and S preserves O₂(P₂). -/
theorem normalizes_second_core (a : NaturalParabolicGeometry p)
    (s : d.ExchangedSource) (hM : IsOrderingMaximal T M)
    (h : PreparedChosenModule T M V) :
    (T : Subgroup G) ≤ normalizer (p.Q2 : Set G) := by
  have hTS : (T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer d.S_le_T).mp s.sylow_normal
  have hTP : (T : Subgroup G) ≤ normalizer (p.P2 : Set G) := by
    rw [a.second_supplement]
    exact (le_inf (a.normalizes_second_residual hM h) hTS).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact hTP.trans (normalizer_le_normalizer_characteristic_image p.P2 (pCore 2 p.P2))

end NaturalParabolicGeometry
end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
