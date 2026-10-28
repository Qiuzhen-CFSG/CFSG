module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.Intrinsic

/-!
# Recovering the literal binary G₂ component map

The intrinsic quasisimple quotient has a perfect central projection onto
G₂(2)′. Its two-group kernel vanishes because the quotient is two-core-free.
The resulting equivalence retains every representative of the original
star-to-plus map, so C_K(W_K)=O₂(K), with no independent kernel premise.

Source: Aschbacher--Smith A.3.6 and the first paragraph of 13.6.22, p.932.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection
open ComponentSelection SourceOrthogonal.Selection
universe u
variable {G : Type u} [Group G] [Finite G]
  [IsQuasisimple (commutator (Atlas.G2.Model (ZMod 2)))]

omit [IsQuasisimple (commutator (Atlas.G2.Model (ZMod 2)))] in
private theorem twoCore_le_ker {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (hB : pCore 2 B = ⊥) :
    pCore 2 A ≤ f.ker := by
  have hm : (pCore 2 A).map f ≤ pCore 2 B :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f hf, pCore_isPGroup.map f⟩
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (hm.trans hB.le))

/-- The same plus marking identifies the intrinsic two-core quotient and
its full action kernel. Neither minimum selection nor shortness is assumed. -/
theorem exists_intrinsic_marking {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → A36Conclusion B)
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ∃ eK : K ⧸ pCore 2 K ≃* commutator (Atlas.G2.Model (ZMod 2)),
      (∀ k : K, eK (QuotientGroup.mk' _ k) =
        e (intrinsicToPlus K L T z v hK.1.1 hL hz k)) ∧
      (centralizer (WK K L T z v : Set G)).subgroupOf K = pCore 2 K := by
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    (Intrinsic.intrinsic_quasisimple_and_central_quotient hA36 K L T z v
      hlocal hL hz hK hR e).1
  have hplus : pCore 2 (plusImage K L T z v hL hz K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal K L T z v hL hz hK), hR]
    exact (plusImage K L T z v hL hz K).ker_subtype
  have hcore : pCore 2 (commutator (Atlas.G2.Model (ZMod 2))) = ⊥ := by
    rw [← pCore_map_iso 2 e, hplus, Subgroup.map_bot]
  let f := e.toMonoidHom.comp (intrinsicToPlus K L T z v hK.1.1 hL hz)
  have hf : Function.Surjective f := e.surjective.comp
    (intrinsicToPlus_surjective K L T z v hK.1.1 hL hz)
  let fQ := QuotientGroup.lift (pCore 2 K) f (twoCore_le_ker f hf hcore)
  have hfQ : Function.Surjective fQ :=
    QuotientGroup.lift_surjective_of_surjective _ _ hf _
  let a := Intrinsic.centralQuotientEquiv fQ hfQ
  obtain ⟨j, hj⟩ := Atlas.G2.FiniteCover.exists_binaryDerived_marked_equiv
    (pCore_quotient_pCore_eq_bot 2) a
  have he : ∀ k : K, j (QuotientGroup.mk' _ k) =
      e (intrinsicToPlus K L T z v hK.1.1 hL hz k) := by
    intro k
    rw [hj]
    exact Intrinsic.centralQuotientEquiv_mk fQ hfQ (QuotientGroup.mk' _ k)
  refine ⟨j, he, ?_⟩
  rw [← intrinsicToPlus_ker K L T z v hK.1.1 hL hz]
  ext k
  change intrinsicToPlus K L T z v hK.1.1 hL hz k = 1 ↔ k ∈ pCore 2 K
  calc
    _ ↔ e (intrinsicToPlus K L T z v hK.1.1 hL hz k) = 1 := e.map_eq_one_iff.symm
    _ ↔ j (QuotientGroup.mk' _ k) = 1 := by rw [he]
    _ ↔ QuotientGroup.mk' (pCore 2 K) k = 1 := j.map_eq_one_iff
    _ ↔ k ∈ pCore 2 K := QuotientGroup.eq_one_iff _

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection
