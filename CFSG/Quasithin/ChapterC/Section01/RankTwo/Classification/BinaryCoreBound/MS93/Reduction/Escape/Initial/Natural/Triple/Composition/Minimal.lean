module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Composition.Residual
public import Theory.Representation.NormalInvariants
public import Theory.Representation.BinaryOffender.FlagCodimension

/-!
# A minimal section moved by a normal two-perfect subgroup

Choose an ambient invariant subspace of least dimension on which K acts
nontrivially. Every proper invariant subspace is K-fixed, so the actual
quotient by its K-fixed vectors is irreducible. It is still moved by K:
otherwise its action would have fixed displacements, contrary to
two-perfectness. This argument does not split the central extension.

This supplies the section-selection step for Meierfrankenfeld–Stellmacher
(1993), (1.4)–(1.5), pp.842–843.
-/

public section

open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple.Composition
variable {G E : Type*} [Group G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- A least moving invariant subspace has an actual irreducible central quotient.
Two-perfectness ensures that this quotient is still moving. -/
theorem exists_minimal_moving_section (ρ : Representation (ZMod 2) G E)
    (K : Subgroup G) [K.Normal] (hK : IsPPerfect 2 K)
    (hn : ¬ (⊤ : Submodule (ZMod 2) E) ≤ fixedSpace ρ K) :
    ∃ F W : Subrepresentation ρ, F ≤ W ∧
      F.toSubmodule ≤ fixedSpace ρ K ∧
      IsIrreducible (sectionRepresentation ρ F W) ∧
      ∃ g ∈ K, ∃ v, sectionRepresentation ρ F W g v ≠ v := by
  classical
  let T : ℕ → Prop := fun n => ∃ W : Subrepresentation ρ,
    ¬ W.toSubmodule ≤ fixedSpace ρ K ∧ Module.finrank (ZMod 2) W.toSubmodule = n
  have ht : ∃ n, T n := ⟨_, ⊤, hn, rfl⟩
  obtain ⟨W, hnW, hdim⟩ := Nat.find_spec ht
  have hmin (J : Subrepresentation ρ) (hJW : J ≤ W)
      (hnJ : ¬ J.toSubmodule ≤ fixedSpace ρ K) : J = W := by
    apply eq_of_le_of_not_lt hJW
    intro hlt
    have hlt' : J.toSubmodule < W.toSubmodule := by
      exact lt_of_le_of_ne hJW (fun he => hlt.ne (Subrepresentation.toSubmodule_injective he))
    exact Nat.find_min ht (hdim ▸ Submodule.finrank_lt_finrank_of_lt hlt') ⟨J, hnJ, rfl⟩
  let F : Subrepresentation ρ := W ⊓ fixedSubrepresentationOfNormal ρ K
  have hFW : F ≤ W := inf_le_left
  have hF : F.toSubmodule ≤ fixedSpace ρ K := inf_le_right
  let C := sectionLower ρ F W
  have hC : C.toSubmodule ≠ ⊤ := by
    intro he
    apply hnW
    intro v hv
    have hc : (⟨v, hv⟩ : W.toSubmodule) ∈ C.toSubmodule := by rw [he]; trivial
    exact hF hc
  let : Nontrivial (W.toSubmodule ⧸ C.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hC
  have hi : IsIrreducible (sectionRepresentation ρ F W) := by
    rw [Representation.IsIrreducible, isSimpleOrder_iff]
    refine ⟨inferInstance, ?_⟩
    intro S
    let q := C.toSubmodule.mkQ
    let J : Subrepresentation ρ := {
      toSubmodule := (S.toSubmodule.comap q).map W.toSubmodule.subtype
      apply_mem_toSubmodule g := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨W.toRepresentation g v, S.apply_mem_toSubmodule g hv, rfl⟩ }
    have hJW : J ≤ W := Submodule.map_subtype_le _ _
    by_cases hfix : J.toSubmodule ≤ fixedSpace ρ K
    · left
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm _ bot_le
      intro v hv
      obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective C.toSubmodule v
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨w.property, hfix ⟨w, hv, rfl⟩⟩
    · right
      have hJW' := hmin J hJW hfix
      apply Subrepresentation.toSubmodule_injective
      apply top_unique
      intro v _
      obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective C.toSubmodule v
      have hw : (w : E) ∈ J.toSubmodule := by rw [hJW']; exact w.property
      obtain ⟨u, hu, he⟩ := hw
      have hueq : u = w := Subtype.ext he
      have huq : q u ∈ S := hu
      rw [hueq] at huq
      exact huq
  refine ⟨F, W, hFW, hF, hi, ?_⟩
  by_contra! htriv
  have hcentral : ∀ g ∈ K, ∀ v,
      W.toRepresentation g v - v ∈ fixedSpace W.toRepresentation K := by
    intro g hg v k
    apply Subtype.ext
    exact hF ((sectionRepresentation_trivial_iff ρ F W g).mp
      (htriv g hg) v v.property) k
  have hwfix := fixed_of_fixed_displacements W.toRepresentation K hK hcentral
  apply hnW
  intro v hv k
  have hh : (⟨v, hv⟩ : W.toSubmodule) ∈ fixedSpace W.toRepresentation K := by
    rw [hwfix]; trivial
  exact congrArg Subtype.val (hh k)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple.Composition
