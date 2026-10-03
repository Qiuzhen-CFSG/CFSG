module
public import ABG.ChapterII.Section1.WreathedBaseStructure
public import ABG.ChapterII.Section1.WreathedQuaternionConjugacy
public import ABG.ChapterII.Section1.FusionPatterns

/-!
# Comparing a wreathed fusion frame with a chosen presentation

For an arbitrary wreathed fusion frame inside a finite group, its abelian
subgroup is the ambient image of the base of any chosen presentation of the
specified Sylow subgroup. Its quaternion central product is conjugate to the
ambient image of the presentation's canonical central product by an element
of that same Sylow subgroup. This connects the canonical calculations to the
arbitrary representatives in ABG Chapter II Section 1 Proposition 2, article
p.11, `refs/latex/alperin-brauer-gorenstein-pages/page-012.tex`.

The unique abelian maximal subgroup clause identifies the restricted base;
mapping along the Sylow inclusion recovers the original ambient subgroup.
Restrict the frame's quaternion witness to the Sylow subgroup and use the
proved quaternion subgroup conjugacy theorem there. Conjugation fixes the
Sylow center. Mapping the resulting join equality into the ambient group
commutes with conjugation and retains exactly the factor `subgroupCenter S`.
-/

namespace ABG.WreathedFusionFrame

/-- The base is canonical and the quaternion central product is canonical up to Sylow conjugacy. -/
public theorem presentation_representatives
    {G : Type*} [Group G] [Finite G]
    {S : Sylow 2 G} {n : ℕ} {U V : Subgroup G}
    (hframe : WreathedFusionFrame S n U V) (P : Wreathed.Presentation S n) :
    U = P.U.map (S : Subgroup G).subtype ∧
      ∃ s : S, (P.V.map (S : Subgroup G).subtype).map
        (MulAut.conj (s : G)).toMonoidHom = V := by
  rcases hframe with ⟨_, hUS, _, _, huniq, Q, hQS, hQ, hV⟩
  constructor
  · have hU : P.U = U.subgroupOf S := huniq P.U P.base_structure.2.2.1 P.U_isCoatom
    rw [hU, Subgroup.map_subgroupOf_eq_of_le hUS]
  · have hQ' : IsQuaternionGroup (Q.subgroupOf S) := by
      obtain ⟨e⟩ := hQ
      exact ⟨(Subgroup.subgroupOfEquivOfLe hQS).trans e⟩
    obtain ⟨s, hs⟩ := P.quaternion_subgroup_conjugacy (Q.subgroupOf S) hQ'
    have hlocal : P.V.map (MulAut.conj s).toMonoidHom =
        Q.subgroupOf S ⊔ Subgroup.center S := by
      rw [Wreathed.Presentation.V, Subgroup.map_sup, hs,
        Subgroup.characteristic_iff_map_eq.mp (inferInstance : (Subgroup.center S).Characteristic)]
    refine ⟨s, ?_⟩
    calc
      (P.V.map (S : Subgroup G).subtype).map (MulAut.conj (s : G)).toMonoidHom =
          (P.V.map (MulAut.conj s).toMonoidHom).map (S : Subgroup G).subtype := by
        rw [Subgroup.map_map, Subgroup.map_map]
        congr 1
      _ = (Q.subgroupOf S ⊔ Subgroup.center S).map (S : Subgroup G).subtype := by rw [hlocal]
      _ = Q ⊔ subgroupCenter (S : Subgroup G) := by
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hQS]
        rfl
      _ = V := hV.symm

end ABG.WreathedFusionFrame
