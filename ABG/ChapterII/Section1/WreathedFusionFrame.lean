module
public import ABG.ChapterII.Section1.WreathedBaseStructure
public import ABG.ChapterII.Section1.WreathedQuaternionCore
public import ABG.ChapterII.Section1.FusionPatterns

/-!
# Choosing the wreathed fusion frame

A finite group with a specified wreathed Sylow two-subgroup of height `n`
admits actual ambient subgroups forming the frame for ABG Chapter II
Section 1 Proposition 2. The abelian subgroup restricts to the unique
abelian maximal subgroup of the specified Sylow subgroup. The second
subgroup is the join of an actual quaternion subgroup with the Sylow
center viewed in the ambient group. Source: the opening of Proposition 2,
article p.11, in `refs/latex/alperin-brauer-gorenstein-pages/page-012.tex`.

Choose a wreathed presentation and map its base and canonical quaternion
central product along the Sylow subtype homomorphism. Injectivity identifies
the restricted image of the base with the original base, so its maximality
and uniqueness transfer from Lemma 2(ii). It also transports the quaternion
core isomorphism. Preservation of joins identifies the second image with
the quaternion image joined with exactly `subgroupCenter S`. The canonical
theorem retains any specified presentation, and the existence theorem chooses
one and invokes it. This lets the focal case calculations use the exact same
base and quaternion factor as their presentation.
-/

namespace ABG

namespace Wreathed.Presentation

/-- A chosen presentation supplies its canonical ambient fusion frame. -/
public theorem fusionFrame {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {n : ℕ} (P : Presentation S n) :
    WreathedFusionFrame S n (P.U.map (S : Subgroup G).subtype)
      (P.V.map (S : Subgroup G).subtype) := by
  have hS : IsWreathedOfHeight S n :=
    ⟨P.height, P.card, P.s, P.t, P.z, P.s_pow, P.t_pow, P.z_sq,
      P.conj_s, P.conj_t, P.commute, P.generate⟩
  let i := (S : Subgroup G).subtype
  let U := P.U.map i
  let Q := P.quaternionCore.map i
  have hU : U.subgroupOf S = P.U :=
    Subgroup.comap_map_eq_self_of_injective (S : Subgroup G).subtype_injective P.U
  let : IsMulCommutative P.U := P.base_structure.2.2.1
  refine ⟨hS, Subgroup.map_subtype_le P.U, inferInstance, ?_, ?_, Q,
    Subgroup.map_subtype_le P.quaternionCore, ?_, ?_⟩
  · change IsCoatom (U.subgroupOf S)
    rw [hU]
    exact P.U_isCoatom
  · intro W hW hmax
    change W = U.subgroupOf S
    rw [hU]
    exact P.abelian_eq_U_of_isCoatom W hW hmax
  · obtain ⟨e⟩ := P.quaternion_core_model.1
    exact ⟨(P.quaternionCore.equivMapOfInjective i
      (S : Subgroup G).subtype_injective).symm.trans e⟩
  · change (P.quaternionCore ⊔ Subgroup.center S).map i =
      P.quaternionCore.map i ⊔ (Subgroup.center S).map i
    exact Subgroup.map_sup _ _ _

end Wreathed.Presentation

/-- A wreathed Sylow subgroup admits the actual subgroup choices used in Proposition 2. -/
public theorem exists_wreathedFusionFrame
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (n : ℕ)
    (hS : IsWreathedOfHeight S n) :
    ∃ U V : Subgroup G, WreathedFusionFrame S n U V := by
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hS
  exact ⟨P.U.map (S : Subgroup G).subtype, P.V.map (S : Subgroup G).subtype,
    P.fusionFrame S⟩

end ABG
