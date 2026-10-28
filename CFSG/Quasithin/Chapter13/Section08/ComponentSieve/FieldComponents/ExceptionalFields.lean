module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupTheory.Commutator.ConjugateSpan
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.Representation.BinaryPermutation.FiveSylowQuadratic

/-!
# Exceptional higher-field cases in 13.8.20

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed p.955 (PDF p.972).

The L₂(4) deduction constructs an actual H* ≃ S₅ from H = KT and the
prescribed outer actor, retaining its restriction to K* ≃ A₅. The centralizer
and two-group quotient needed for this construction are proved. On the actual
section V_H/U_H, a noncentral five-point permutation quotient cannot have the
quadratic Vγ* action: a conjugate Vα* of rank at least two fills a Sylow four-
group, and Sylow conjugacy supplies both marked double transpositions.

The L₁ containment, projective L₃(4) quadratic-ratio exclusion, unitary-eight
seed obstruction, and SL₃(4) critical-subspace obstruction remain to be proved.
In particular the source's reduction to H = KT and the identification of H∩M
with a five-point stabilizer must still be supplied in the exceptional-case
assembly. These conditional deductions do not assert completion of 13.8.20.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The source seed identity and the containment L₁ ≤ K simultaneously
give H = KT and U_H = [U_H,K]. Normality is only inside H; X can be
L₁ or the marked L₁,+ as prescribed by the source. -/
theorem reduction_of_containment
    (H K L₁ T X V₃ : Subgroup G) [(K.subgroupOf H).Normal]
    (hH : H = K ⊔ L₁ ⊔ T) (hL₁K : L₁ ≤ K) (hX : X ≤ L₁)
    (hseed : V₃ = ⁅V₃, X⁆) :
    H = K ⊔ T ∧ Source.UH H V₃ = ⁅Source.UH H V₃, K⁆ := by
  have hH' : H = K ⊔ T := by rw [hH, sup_eq_left.mpr hL₁K]
  have hKH : K ≤ H := by rw [hH']; exact le_sup_left
  exact ⟨hH', conjugateSpanBy_eq_commutator_of_seed V₃ H K X hKH
    (le_normalizer_of_normal_subgroupOf hKH) (hX.trans hL₁K) hseed⟩

/-- Once L₁ ≤ K gives H = KT, the outer actor in alternative (b) identifies
the actual H/O₂(H) with S₅. Its restriction to K* is the exceptional
PSL₂(4) ≃ A₅ identification, so it can be used for the Sylow marking. -/
theorem linear_two_four_identification
    (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hH : H = K ⊔ T) (hT : IsPGroup 2 T)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : Source.starImage H K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (t : Source.Hstar H)
    (ht : (MulAut.conjNormal t : MulAut (Source.starImage H K)) ∉
      MulAut.innerSubgroup (Source.starImage H K)) :
    ∃ (eA : Source.starImage H K ≃* alternatingGroup (Fin 5))
      (e : Source.Hstar H ≃* Equiv.Perm (Fin 5)),
      ∀ k : Source.starImage H K, e k = eA k := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := by rw [hH]; exact le_sup_left
  have hTH : T ≤ H := by rw [hH]; exact le_sup_right
  have hs : Source.starImage H K ⊔ Source.starImage H T = ⊤ := by
    unfold Source.starImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup hKH hTH, ← hH, subgroupOf_self,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hTs : IsPGroup 2 (Source.starImage H T) :=
    (hT.of_equiv (subgroupOfEquivOfLe hTH).symm).map _
  obtain ⟨e₅⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  obtain ⟨e, he⟩ := Theory.SpecificGroups.Alternating.FiveExtensionAction.exists_equiv_of_two_supplement
    (Source.starImage H K) (eK.trans e₅) (Source.starImage H T) hTs hs
    (Subgroup.pCore_quotient_pCore_eq_bot 2) t ht
  exact ⟨eK.trans e₅, e, he⟩

/-- The final permutation-module contradiction on the literal V_H/U_H.
The coset-module surjection and noncentrality are the inputs from 13.8.4(5),
quadraticity from 13.8.4(6), placement from 13.8.8(2), and the rank bound
from 13.8.18(4). The point coordinates must come from the actual H∩M
stabilizer calculation. Neither double-transposition marking is assumed. -/
theorem linear_two_four_permutation_contradiction
    (H K M V V₃ Vα Vγ : Subgroup G)
    [((Source.UH H V₃).subgroupOf (Source.VH H V)).Normal]
    [IsMulCommutative (Source.Vsection H V V₃)]
    [Module (ZMod 2) (Additive (Source.Vsection H V V₃))]
    (eA : Source.starImage H K ≃* alternatingGroup (Fin 5))
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 5))
    (he : ∀ k : Source.starImage H K, e k = eA k)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (d : (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)) ≃ Fin 5)
    (hd : ∀ h ω, d (h • ω) = e h (d ω))
    (f₀ : BinaryPermutation.Full (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)) →ₗ[ZMod 2]
      Additive (Source.Vsection H V V₃))
    (hf₀ : Function.Surjective f₀)
    (heq₀ : ∀ h v, f₀ (BinaryPermutation.representation
      (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)) (MulAction.toPerm h) v) = ρ h (f₀ v))
    (hnoncentral : ∃ h v, ρ h v ≠ v)
    (P : Sylow 2 (Source.starImage H K)) (g : Source.Hstar H)
    (hconj : (Source.starImage H Vγ).map (MulAut.conj g).toMonoidHom =
      Source.starImage H Vα)
    (hplace : Source.starImage H Vα ≤
      (P : Subgroup (Source.starImage H K)).map (Source.starImage H K).subtype)
    (hrank : 2 ≤ rank (Source.starImage H Vα))
    (hquad : IsQuadratic ρ (Source.starImage H Vγ)) : False := by
  obtain ⟨f, hf, heq⟩ := BinaryPermutation.FiveSylowQuadratic.exists_equivariant_quotient
    e d hd ρ f₀ hf₀ heq₀
  exact BinaryPermutation.FiveSylowQuadratic.not_quadratic_of_conjugate_rank_two
    (Source.starImage H K) e eA he ρ f hf heq hnoncentral P
    (Source.starImage H Vα) (Source.starImage H Vγ) g hconj hplace hrank hquad

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields
