module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFiveActors.Outer
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFiveActors.Hyperplanes

/-!
# H.9.2(1–5) on the original source group and module

All comparisons are constructed from `SourceSetup 5 M V`. The outer
involution results retain the literal diagonal map and the compatible S₆
natural-module comparison. For the supplied Sylow T, `sylow_family`
constructs its invariant three-space in the ORIGINAL natural summand and
identifies its radical with the relative two-core of its literal layer
stabilizer. The same radical classifies every rank-six and rank-five actor
and satisfies all four fixed/commutator formulas. `high_rank_family`
proves layer containment and the actual Chapter E generated-core conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.9.2(1–5), printed pp.390–391 (PDF pp.401–402).
-/

@[expose] public section
open BinaryNaturalDual Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceFiveActors
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup 5 M V)

/-- The literal source subgroup N_L(U), with U embedded in the whole module. -/
def layerStabilizer (U : Submodule (ZMod 2) S.natural) : Subgroup M :=
  componentLayer M ⊓ Representation.BinaryOffender.subspaceStabilizer
    S.representation (U.map S.natural.subtype)

/-- The geometric parabolic is the actual source layer stabilizer. -/
theorem parabolic_eq_layerStabilizer (U : Submodule (ZMod 2) S.natural) :
    parabolic S U = layerStabilizer S U := by
  have hm (u : S.natural) : (u : V) ∈ U.map S.natural.subtype ↔ u ∈ U := by
    constructor
    · rintro ⟨w,hw,he⟩
      exact (Subtype.ext he : w = u) ▸ hw
    · intro hu
      exact Submodule.mem_map_of_mem hu
  apply le_antisymm
  · apply le_inf
    · intro g hg
      exact ((mem_parabolic_iff S U g).mp hg).choose
    · apply Representation.BinaryOffender.le_subspaceStabilizer
      intro g hg v hv
      obtain ⟨hL,hg⟩ := (mem_parabolic_iff S U g).mp hg
      obtain ⟨w,hw,rfl⟩ := hv
      change S.representation (⟨g,hL⟩ : componentLayer M) (w : V) ∈ U.map S.natural.subtype
      rw [← naturalAction_apply S ⟨g,hL⟩ w, hm]
      exact (hg w).mpr hw
  · rintro g ⟨hL,hg⟩
    apply (mem_parabolic_iff S U g).mpr
    refine ⟨hL,fun w => ?_⟩
    rw [← hm, naturalAction_apply, ← hm]
    exact hg w

/-- The source radical lies in the actual source layer. -/
theorem radical_le_layer (U : Submodule (ZMod 2) S.natural) :
    radical S U ≤ componentLayer M := by
  rintro _ ⟨g,_,rfl⟩
  exact (S.layer.symm g).property

/-- A₀ is exactly O₂(N_L(U)), with relative normality and ambient embedding. -/
theorem radical_eq_stabilizer_twoCore (U : Submodule (ZMod 2) S.natural) :
    radical S U = (pCore 2 (layerStabilizer S U)).map (layerStabilizer S U).subtype := by
  rw [← parabolic_eq_layerStabilizer, radical_eq_twoCore]

/-- H.9.2(1): the literal source diagonal map, centralizer equivariance,
and equality of the actual fixed and commutator spaces. The compatible
S₆ decomposition is `outer_decomposition`; conjugacy is `outer_conjugate`. -/
theorem outer_diagonal (t : M) (ht : t ^ 2 = 1) (hout : t ∉ componentLayer M) :
    ∃ θ : S.natural ≃ₗ[ZMod 2] involutionFixed S t,
      (∀ w : S.natural, (θ w : V) = (w : V) + S.representation t w) ∧
      (∀ (a : centralizer S t) (w : S.natural),
        (θ (naturalAction S ⟨a.val,a.property.1⟩ w) : V) = S.representation a.val (θ w)) ∧
      involutionFixed S t = commutator S ⊤ (Subgroup.zpowers t) ∧
      Module.finrank (ZMod 2) (involutionFixed S t) = 5 :=
  ⟨diagonal S t ht hout, diagonal_apply S t ht hout,
    diagonal_equivariant S t ht hout, involutionFixed_eq_commutator S t ht hout,
    involutionFixed_finrank S t ht hout⟩

/-- H.9.2(3–4): a complete family at the three-space for the GIVEN Sylow.
There is no coordinate flag, radical-placement or module-space premise. -/
theorem sylow_family (T : Sylow 2 M) :
    ∃ U : Submodule (ZMod 2) S.natural,
      Module.finrank (ZMod 2) U = 3 ∧
      S.naturalSylowNormalizer T ≤ layerStabilizer S U ∧
      radical S U ≤ componentLayer M ∧
      radical S U = (pCore 2 (layerStabilizer S U)).map (layerStabilizer S U).subtype ∧
      IsElementaryAbelian 2 (radical S U) ∧ Nat.card (radical S U) = 64 ∧
      (∀ A : Subgroup M, (IsElementaryAbelian 2 A ∧ Nat.card A = 64) ↔
        ∃ a : M, A.map (MulAut.conj a).toMonoidHom = radical S U) ∧
      (∀ (A : Subgroup M) [IsElementaryAbelian 2 A],
        primeRank 2 A = 6 ↔ ∃ a : M, A.map (MulAut.conj a).toMonoidHom = radical S U) ∧
      (∀ (A : Subgroup M) [IsElementaryAbelian 2 A],
        primeRank 2 A = 5 ↔ ∃ a : M,
          A.map (MulAut.conj a).toMonoidHom ≤ radical S U ∧
          (A.map (MulAut.conj a).toMonoidHom).relIndex (radical S U) = 2) ∧
      (∀ (A : Subgroup M), A ≤ radical S U → A.relIndex (radical S U) = 2 →
        S.fixed A = commutator S ⊤ A ∧
        commutator S ⊤ A = S.fixed (radical S U) ∧
        S.fixed (radical S U) = commutator S ⊤ (radical S U) ∧
        commutator S ⊤ (radical S U) = radicalSpace S U ∧
        Module.finrank (ZMod 2) (S.fixed A) = 5) := by
  obtain ⟨U,hU,hT⟩ := exists_sylow_threeSpace S T
  obtain ⟨he,hc⟩ := radical_elementary_card S U hU
  refine ⟨U,hU,?_,radical_le_layer S U,radical_eq_stabilizer_twoCore S U,he,hc,
    elementary_card_64_iff S U hU,rank_six_iff S U hU,rank_five_iff S U hU,
    hyperplane_formulas S U hU⟩
  rwa [← parabolic_eq_layerStabilizer]

/-- H.9.2(2,5): all high-rank source actors are inner and have full actual
E.3.30 core. Only the source setup and displayed actor hypotheses are used. -/
theorem high_rank_family (A : Subgroup M) [IsElementaryAbelian 2 A]
    (hA : 5 ≤ primeRank 2 A) :
    A ≤ componentLayer M ∧ ChapterE.dualGeneratedCore
      (multiplicativeAction (S.representation.comp A.subtype)) 3 = ⊤ :=
  ⟨high_rank_inner S A hA, dualGeneratedCore_eq_top S A hA⟩

end CFSG.Quasithin.ChapterH.NaturalDual.SourceFiveActors
