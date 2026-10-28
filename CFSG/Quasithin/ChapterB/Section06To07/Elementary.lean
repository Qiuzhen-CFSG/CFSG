module

public import Theory.GroupTheory.MinimalParabolicGeneration
public import Mathlib.GroupTheory.Sylow

/-!
# Minimal parabolics and elementary generation

A minimal parabolic over a fixed ambient Sylow 2-subgroup `T` has a unique
maximal subgroup containing `T`, and `T` is not normal in it. Relative maximal
subgroups are expressed by covers in the ambient subgroup lattice, so the
subgroup and its embedding are retained throughout.

McBride's finite-lattice argument and the normalizer action on the nonnormal
overgroups give the generation results. The normal-closure version explicitly
requires `T` to be proper, as in B.6.4(2); this excludes the degenerate case
`T = H` in the printed formulation of B.6.5. The normalizer-plus-parabolics
generation statement has no properness restriction.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), B.6.1–B.6.7, pp. 112–113.
-/

namespace CFSG.Quasithin.ChapterB
variable {H : Type*} [Group H]
/-- Aschbacher–Smith B.6.1, over a specified Sylow 2-subgroup of the ambient group. -/
@[expose] public def IsMinimalParabolicOver (T : Sylow 2 H) (P : Subgroup H) : Prop :=
  P ∈ Subgroup.nonNormalUniqueMaximalOvergroups (T : Subgroup H)

/-- The normality exclusion is internal to the parabolic, as required by B.6.1. -/
public theorem isMinimalParabolicOver_iff (T : Sylow 2 H) (P : Subgroup H) :
    IsMinimalParabolicOver T P ↔
      Order.HasUniqueMaximalOver (T : Subgroup H) P ∧
        ¬ ((T : Subgroup H).subgroupOf P).Normal := by
  constructor
  · intro h
    exact ⟨h.1, fun hn => h.2
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h.1.1.le).mp hn)⟩
  · rintro ⟨h, hn⟩
    exact ⟨h, fun hnorm => hn
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h.1.le).mpr hnorm)⟩

/-- The whole group is a minimal parabolic precisely when the Sylow subgroup has a
unique maximal overgroup and is not normal. -/
public theorem isMinimalParabolicOver_top_iff (T : Sylow 2 H) :
    IsMinimalParabolicOver T ⊤ ↔
      (∃! M : Subgroup H, IsCoatom M ∧ (T : Subgroup H) ≤ M) ∧
        ¬ (T : Subgroup H).Normal := by
  constructor
  · intro h
    obtain ⟨M, hM, huniq⟩ := h.1.2
    refine ⟨⟨M, ⟨hM.2.isCoatom, hM.1⟩, fun N hN =>
      huniq N ⟨hN.2, hN.1.covBy_top⟩⟩, ?_⟩
    intro hn
    have : (T : Subgroup H).Normal := hn
    exact h.2 Subgroup.le_normalizer_of_normal
  · rintro ⟨⟨M, hM, huniq⟩, hn⟩
    refine ⟨⟨lt_of_le_of_lt hM.2 hM.1.lt_top,
      M, ⟨hM.2, hM.1.covBy_top⟩, fun N hN => huniq N ⟨hN.2.isCoatom, hN.1⟩⟩, ?_⟩
    intro hnorm
    exact hn (Subgroup.normalizer_eq_top_iff.mp (top_unique hnorm))

/-- McBride’s lemma B.6.3: the unique-maximal overgroups of a proper subgroup generate. -/
public theorem mcBride [Finite H] (X : Subgroup H) (hX : X < ⊤) :
    sSup {U : Subgroup H | Order.HasUniqueMaximalOver X U} = ⊤ := by
  simpa using (Order.eq_sSup_hasUniqueMaximalOver hX).symm

/-- B.6.4(2) for a Sylow subgroup: properness and normal generation imply
generation by the minimal parabolics over that Sylow subgroup. -/
public theorem minimalParabolics_generate_of_normalClosure_eq_top [Finite H] (T : Sylow 2 H)
    (hT : (T : Subgroup H) < ⊤)
    (hgen : Subgroup.normalClosure (T : Set H) = ⊤) :
    sSup {P : Subgroup H | IsMinimalParabolicOver T P} = ⊤ :=
  Subgroup.nonNormalUniqueMaximalClosure_eq_top (T : Subgroup H) hT hgen

/-- The unconditional generation statement used in Remark B.6.6. -/
public theorem minimalParabolics_sup_normalizer [Finite H] (T : Sylow 2 H) :
    sSup {P : Subgroup H | IsMinimalParabolicOver T P} ⊔
      Subgroup.normalizer (T : Set H) = ⊤ :=
  Subgroup.nonNormalUniqueMaximalClosure_sup_normalizer (T : Subgroup H)

end CFSG.Quasithin.ChapterB
