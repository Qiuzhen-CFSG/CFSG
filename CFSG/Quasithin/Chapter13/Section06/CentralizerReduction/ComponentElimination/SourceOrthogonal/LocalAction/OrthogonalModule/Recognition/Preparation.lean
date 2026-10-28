module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Section
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.GroupTheory.PrimeRankCubeFree

/-!
# Preparing B.5.1 on the literal component action

The known-simple K-group condition descends from G_v through the original
component projection. The marked A₈ has no odd prime cube in its order, so
its odd-prime ranks are at most two. The plus two-core condition passes to
K⁺ by its proved subnormality. Simplicity turns an ordinary FF witness into
best-offender generation. Faithfulness on the actual moved space follows
from perfectness: central first commutators would force the entire original
component action to be trivial.

The resulting application retains all six clauses of the source-correct
projective-line B.5.1 contract. The universal theorem and the ordinary FF
witness are explicit; selecting the orthogonal alternative remains separate.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed p.99, applied following 13.6.23, printed p.933/PDF p.950.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition
open ComponentSelection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]

omit [IsElementaryAbelian 2 (WK K L T z v)] in
/-- The full source K-class passes through the literal component image, while
the marked A₈ order proves the required odd-prime rank bounds. -/
theorem component_sqtk [Finite G] {Ξ : GroupClass.{u}}
    (hY : K ∈ Yz L T z v)
    (hsource : IsKGroup Ξ (Gv v))
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8)) :
    IsSQTK Ξ (plusImage K L T z v hL hz K) := by
  have hcard : Nat.card (plusImage K L T z v hL hz K) = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  refine ⟨?_, ?_⟩
  · intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    apply primeRank_le_two_of_cube_not_dvd
    rw [hcard]
    intro hd
    have hpd : p ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 :=
      (dvd_pow_self p (by decide : 3 ≠ 0)).trans hd
    have hsmall : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 5 ∨ p ∣ 7 := by
      rcases hp.dvd_mul.mp hpd with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · exact .inl (hp.dvd_of_dvd_pow h)
          · exact .inr (.inl (hp.dvd_of_dvd_pow h))
        · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
    have heq (q : ℕ) (hq : q.Prime) (h : p ∣ q) : p = q :=
      (Nat.prime_dvd_prime_iff_eq hp hq).mp h
    rcases hsmall with h | h | h | h
    · have he := heq 2 (by decide) h
      subst p
      exact ho.not_two_dvd_nat (dvd_refl 2)
    · have he := heq 3 (by decide) h
      subst p
      norm_num at hd
    · have he := heq 5 (by decide) h
      subst p
      norm_num at hd
    · have he := heq 7 (by decide) h
      subst p
      norm_num at hd
  · exact (hsource.of_injective (inclusion hY.1.1) (inclusion_injective hY.1.1)).of_surjective
      (imageProjection K L T z v hL hz K (K_le_plusActor K L T v))
      (imageProjection_surjective K L T z v hL hz K (K_le_plusActor K L T v))

/-- The component is faithful on its literal moved space. -/
theorem component_moved_faithful [Finite G]
    (hY : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8))
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K)) :
    Function.Injective (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) := by
  let C := plusImage K L T z v hL hz K
  let ρ := representation K L T z v hL hz
  let σ : Representation (ZMod 2) C s.space.toSubmodule := s.space.toRepresentation.comp C.subtype
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup C := e.isSimpleGroup
  let : IsQuasisimple C := plusImage_K_quasisimple K L T z v hL hz hY hR
  have hker : σ.asGroupHom.ker = ⊥ := by
    rcases (inferInstance : σ.asGroupHom.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    have hcentral : moved ρ C ≤ fixedSpace ρ C := by
      intro w hw k
      have hk : k ∈ σ.asGroupHom.ker := ht ▸ mem_top k
      have he := congrArg (fun a : (Module.End (ZMod 2) s.space.toSubmodule)ˣ =>
        (a : Module.End (ZMod 2) s.space.toSubmodule) ⟨w, s.space_eq.symm ▸ hw⟩) hk
      exact congrArg Subtype.val he
    have hwhole := le_fixedSpace_of_commutator_le_fixedSpace ρ C ⊤
      (le_subspaceStabilizer ρ ⊤ (by simp)) hcentral
    obtain ⟨k, hk⟩ := exists_ne (1 : C)
    have he : ρ k = ρ 1 := by
      rw [map_one]
      apply LinearMap.ext
      intro w
      exact hwhole (Submodule.mem_top : w ∈ (⊤ : Submodule (ZMod 2) _)) k
    exact (hk (Subtype.ext ((representation_injective K L T z v hL hz) he))).elim
  have hinj := (MonoidHom.ker_eq_bot_iff _).mp hker
  intro a b hab
  exact hinj (Units.ext hab)

/-- Ordinary FF supplies generation on the simple component. The module may
be the actual U_K; generation of the larger plus actor is never assumed. -/
theorem component_module_classification [Finite G] {Ξ : GroupClass.{u}}
    (classification : ProjectiveLine.QuasisimpleClassificationInput.{u,u} Ξ)
    (hY : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8))
    (hsqtk : IsSQTK Ξ (plusImage K L T z v hL hz K))
    (U : Subrepresentation (representation K L T z v hL hz))
    (hfaith : Function.Injective (U.toRepresentation.comp (plusImage K L T z v hL hz K).subtype))
    (hff : IsFFModule (U.toRepresentation.comp (plusImage K L T z v hL hz K).subtype)) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
      (U.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) ⊤) := by
  let C := plusImage K L T z v hL hz K
  let ρ := U.toRepresentation.comp C.subtype
  let : Module.Finite (ZMod 2) (Additive (WK K L T z v)) := Module.Finite.of_finite
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup C := e.isSimpleGroup
  let : IsQuasisimple C := plusImage_K_quasisimple K L T z v hL hz hY hR
  have hgen : offenderSubgroup ρ = ⊤ := by
    exact ((offenderSubgroup_normal ρ).eq_bot_or_eq_top).resolve_left
      (offenderSubgroup_ne_bot_of_ff ρ hff)
  have hcore : pCore 2 C = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal K L T z v hL hz hY), hR]
    exact (MonoidHom.ker_eq_bot_iff C.subtype).mpr C.subtype_injective
  apply classification C U.toSubmodule ρ ⊤
  exact
    { finite_module := inferInstance
      faithful := hfaith
      quasisimple := IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm
      sqtk := (IsSQTK.equiv Subgroup.topEquiv).mpr hsqtk
      fitting := by rw [generalizedFitting_eq_top_of_quasisimple, top_sup_eq]
      twoCore := hcore
      generated := hgen }

/-- The genuine B.5.1 application to U_K, with all six clauses retained.
Its ordinary FF witness and the universal implication remain explicit. -/
theorem component_moved_classification [Finite G] {Ξ : GroupClass.{u}}
    (classification : ProjectiveLine.QuasisimpleClassificationInput.{u,u} Ξ)
    (hY : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8))
    (hsource : IsKGroup Ξ (Gv v))
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (hff : IsFFModule (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype)) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
      (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) ⊤) :=
  component_module_classification K L T z v hL hz classification hY hR e
    (component_sqtk K L T z v hL hz hY hsource e) s.space
    (component_moved_faithful K L T z v hL hz hY hR e s) hff

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition
