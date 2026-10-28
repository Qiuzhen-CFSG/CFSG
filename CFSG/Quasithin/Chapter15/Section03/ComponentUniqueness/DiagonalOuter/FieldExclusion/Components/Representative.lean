module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Transport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# The field residual in the representative centralizer

The normalizer of L, intersected with C_G(f), normalizes O²(C_L(f)).
Consequently the source bound C_G(v) ≤ I and the marked central four-group
make this residual normal in C_K(v) whenever K ≤ C_G(f) contains it.
Its actual PSL₃(2) equivalence supplies quasisimplicity, so it is an ordinary
component of that centralizer. No local-component embedding is assumed.

The construction of K and its model classification are separate obligations.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137, using the representative geometry on p.1136.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion

/-- Conjugation preserving L and fixing f preserves its intrinsic two-residual. -/
theorem fieldResidual_normalized_by {G : Type*} [Group G] (I L : Subgroup G) (f : G)
    (hIL : I ≤ normalizer (L : Set G)) :
    I ⊓ centralizer ({f} : Set G) ≤
      normalizer ((fieldResidual L f).map (centralizer ({f} : Set G)).subtype : Set G) := by
  rw [map_fieldResidual]
  exact ((le_inf (inf_le_left.trans hIL)
    (inf_le_right.trans (centralizer ({f} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image
        (L ⊓ centralizer ({f} : Set G)) (pResidual 2 _))

/-- The given PSL₃(2) equivalence makes the field residual quasisimple. -/
theorem fieldResidual_quasisimple {G : Type*} [Group G] (L : Subgroup G) (f : G)
    (e : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    IsQuasisimple (fieldResidual L f) := by
  let B := fieldResidual L f
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup B := (MulEquiv.isSimpleGroup_congr
    (fieldResidualEquivModel L f e)).mpr inferInstance
  let : Group.IsPerfect B := fieldResidual_perfect L f e
  have hc : center B = ⊥ := by
    rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp h)).elim
  exact { simple := (MulEquiv.isSimpleGroup_congr
    ((QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot (G := B)))).mpr inferInstance }

/-- The representative bound gives relative normality and an ordinary component
in the actual intersection K ∩ C_G(v). -/
theorem fieldResidual_component_in_representative_centralizer
    {G : Type*} [Group G] (I L K : Subgroup G) (f v : G)
    (hIL : I ≤ normalizer (L : Set G))
    (hCv : centralizer ({v} : Set G) ≤ I)
    (hLv : L ≤ centralizer ({v} : Set G))
    (hKH : K ≤ centralizer ({f} : Set G))
    (hFK : fieldResidual L f ≤ K.subgroupOf (centralizer ({f} : Set G)))
    (e : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    let A := (fieldResidual L f).map (centralizer ({f} : Set G)).subtype
    let C := K ⊓ centralizer ({v} : Set G)
    A ≤ C ∧ (A.subgroupOf C).Normal ∧ IsComponent C (A.subgroupOf C) := by
  let H := centralizer ({f} : Set G)
  let A := (fieldResidual L f).map H.subtype
  let C := K ⊓ centralizer ({v} : Set G)
  have hAK : A ≤ K := by
    have h := map_mono (f := H.subtype) hFK
    rwa [map_subgroupOf_eq_of_le hKH] at h
  have hAL : A ≤ L := by
    dsimp only [A, H]
    rw [map_fieldResidual]
    exact (map_subtype_le _).trans inf_le_left
  have hAC : A ≤ C := le_inf hAK (hAL.trans hLv)
  have hCN : C ≤ normalizer (A : Set G) :=
    (le_inf (inf_le_right.trans hCv) (inf_le_left.trans hKH)).trans
      (fieldResidual_normalized_by I L f hIL)
  let hn : (A.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer hCN
  let : IsQuasisimple (fieldResidual L f) := fieldResidual_quasisimple L f e
  let eqA : fieldResidual L f ≃* A :=
    (fieldResidual L f).equivMapOfInjective H.subtype H.subtype_injective
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv eqA
  let : IsQuasisimple (A.subgroupOf C) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hAC).symm
  exact ⟨hAC, hn, hn.isSubnormal, inferInstance⟩

/-- The marked center supplies the centralization premise in the preceding theorem. -/
theorem fieldResidual_component_of_marked_center
    {G : Type*} [Group G] (I L K V : Subgroup G) (f v : G)
    (hIL : I ≤ normalizer (L : Set G))
    (hCv : centralizer ({v} : Set G) ≤ I)
    (hZ : (center L).map L.subtype = V) (hv : v ∈ V)
    (hKH : K ≤ centralizer ({f} : Set G))
    (hFK : fieldResidual L f ≤ K.subgroupOf (centralizer ({f} : Set G)))
    (e : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    let A := (fieldResidual L f).map (centralizer ({f} : Set G)).subtype
    let C := K ⊓ centralizer ({v} : Set G)
    A ≤ C ∧ (A.subgroupOf C).Normal ∧ IsComponent C (A.subgroupOf C) := by
  apply fieldResidual_component_in_representative_centralizer I L K f v hIL hCv
    ?_ hKH hFK e
  obtain ⟨z, hz, hzv⟩ := mem_map.mp (hZ.symm ▸ hv)
  intro l hl
  apply mem_centralizer_singleton_iff.mpr
  have he := congrArg Subtype.val (mem_center_iff.mp hz ⟨l, hl⟩)
  change (z : G) = v at hzv
  change l * (z : G) = (z : G) * l at he
  rwa [hzv] at he

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
