module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.BorelLift
public import Theory.GroupTheory.PResidual.AbelianCoprimeKernel

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Borel.Quotients

/-!
# Three-parts of the four exceptional lifted Borels

Let B₀ be the inverse image inside K of the normalizer of the specified
Sylow two-subgroup of K*, and let B = O²(B₀). Actual matrix equivalences
identify the normalizer quotients with the field units for PSL₂(4), two
unit parameters for SL₃(4), and the full unitary torus for SU₃(8). In the
projective unitary case the cubic scalar kernel remains in the quotient.
Their orders are respectively 3, 9, 63 and 21.

The projection from B₀ to each odd abelian torus has two-group kernel:
compose the literal H/O₂(H) projection with the intrinsic two-core quotient.
The two-residual still surjects onto the torus. The abelian quotient and
coprime kernel also show that O³(B) has order prime to three. Thus the
calculation retains the lift's kernel and requires no full model group-order
or simplicity theorem.

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955
(combined manuscript, PDF pp.971–972).
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
open HigherFieldReduction HigherFieldReduction.TorusModels Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private noncomputable def normalizerImageEquiv {D : Type*} [Group D]
    (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K)
    (e : Source.starImage H K ≃* D) :
    componentBorelImage H K hKH S ≃*
      normalizer ((componentStarSylow H K hKH S).mapSurjective (f := e.toMonoidHom) e.surjective : Set D) := by
  let P := componentStarSylow H K hKH S
  let N := normalizer (P : Set (Source.starImage H K))
  have he : N.map e.toMonoidHom =
      normalizer (P.mapSurjective (f := e.toMonoidHom) e.surjective : Set D) :=
    map_normalizer_eq_of_bijective (P : Subgroup (Source.starImage H K)) e.bijective
  exact (equivMapOfInjective N (Source.starImage H K).subtype
    (Source.starImage H K).subtype_injective).symm.trans
      ((e.subgroupMap N).trans (MulEquiv.subgroupCongr he))

private theorem orders_of_projection {A : Type*} [CommGroup A] [Finite A]
    (B₀ : Subgroup G) (f : B₀ →* A) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hA : Nat.Coprime 2 (Nat.card A)) :
    Nat.Coprime 3 (Nat.card (residualIn 3 (borelResidual B₀))) ∧
      Nat.card A ∣ Nat.card (borelResidual B₀) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let i : borelResidual B₀ →* B₀ := inclusion (map_subtype_le _)
  have hki : IsPGroup 2 (f.comp i).ker := by
    rw [← MonoidHom.comap_ker]
    exact hk.comap_of_injective i (inclusion_injective _)
  obtain ⟨n, hn⟩ := hki.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card (f.comp i).ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  constructor
  · rw [residualIn, card_map_of_injective (borelResidual B₀).subtype_injective]
    exact coprime_card_pResidual_of_abelian_coprime_kernel 3 (f.comp i) hc
  · rw [borelResidual, residualIn, card_map_of_injective B₀.subtype_injective]
    exact card_dvd_card_pResidual_of_surjective_coprime 2 f hf hA

private theorem orders_of_torus {N A : Type*} [Group N] [CommGroup A] [Finite A]
    (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K)
    (e : componentBorelImage H K hKH S ≃* N)
    (q : N ⧸ pCore 2 N ≃* A) (hA : Nat.Coprime 2 (Nat.card A)) :
    Nat.Coprime 3 (Nat.card (residualIn 3 (borelResidual (componentBorel H K hKH S)))) ∧
      Nat.card A ∣ Nat.card (borelResidual (componentBorel H K hKH S)) := by
  have hB : componentBorelImage H K hKH S ≤ Source.starImage H K := map_subtype_le _
  let π : componentBorel H K hKH S →* componentBorelImage H K hKH S :=
    borelStarProjection H K hKH (componentBorelImage H K hKH S) hB
  have hπ : Function.Surjective π := borelStarProjection_surjective H K hKH _ hB
  have hπk : IsPGroup 2 π.ker := borelStarProjection_ker_isTwoGroup H K hKH _ hB
  let f := e.toMonoidHom.comp π
  have hf : Function.Surjective f := e.surjective.comp hπ
  have hk : IsPGroup 2 f.ker := by
    have heq : f.ker = π.ker := MonoidHom.ker_comp_of_injective π e.toMonoidHom e.injective
    rw [heq]
    exact hπk
  let t := (QuotientGroup.mk' (pCore 2 N)).comp f
  let g := q.toMonoidHom.comp t
  have hkt : IsPGroup 2 t.ker := by
    have heq : t.ker = (pCore 2 N).comap f := by
      dsimp only [t]
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [heq]
    exact pCore_isPGroup.comap_of_ker_isPGroup f hk
  apply orders_of_projection (componentBorel H K hKH S) g
    (q.surjective.comp ((QuotientGroup.mk'_surjective _).comp hf)) ?_ hA
  have heq : g.ker = t.ker := MonoidHom.ker_comp_of_injective t q.toMonoidHom q.injective
  rw [heq]
  exact hkt

private theorem linearTwo_orders (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K)
    (h : ClassicalGroup.IsPSL (Source.starImage H K) 2 4) :
    Nat.Coprime 3 (Nat.card (residualIn 3 (borelResidual (componentBorel H K hKH S)))) ∧
      3 ∣ Nat.card (borelResidual (componentBorel H K hKH S)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa [← Nat.card_eq_fintype_card] using hF)
  have hc : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have ho : Nat.Coprime 2 (Nat.card Fˣ) := by rw [hc]; decide
  simpa only [hc] using orders_of_torus H K hKH S (componentBorelImageEquiv H K hKH S e)
    (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.quotientTorusEquiv F (n := 2) (by simpa using hF)) ho

private theorem linearThree_orders (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K)
    (h : IsSL (Source.starImage H K) 3 4) :
    Nat.Coprime 3 (Nat.card (residualIn 3 (borelResidual (componentBorel H K hKH S)))) ∧
      9 ∣ Nat.card (borelResidual (componentBorel H K hKH S)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let Q := (componentStarSylow H K hKH S).mapSurjective (f := e.toMonoidHom) e.surjective
  have hc : Nat.card (Fˣ × Fˣ) = 9 := by rw [Nat.card_prod, Nat.card_units, hF]
  have ho : Nat.Coprime 2 (Nat.card (Fˣ × Fˣ)) := by rw [hc]; decide
  simpa only [hc] using orders_of_torus H K hKH S (normalizerImageEquiv H K hKH S e)
    (Matrix.PSL3.CartanActions.BorelQuotient.sylowSLNormalizerQuotientEquiv
      F (n := 2) (by decide) (by simpa using hF) Q) ho

private theorem specialUnitary_orders (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K)
    (h : IsSU (Source.starImage H K) 3 8) :
    Nat.Coprime 3 (Nat.card (residualIn 3 (borelResidual (componentBorel H K hKH S)))) ∧
      63 ∣ Nat.card (borelResidual (componentBorel H K hKH S)) := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
  let Q := (componentStarSylow H K hKH S).mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨_, _, _, q, _⟩ := UnitaryThree.su_borel_quotient J 3 (by decide) (by simpa using hF) (by simpa using hconj) Q
  have hc : Nat.card Fˣ = 63 := by rw [Nat.card_units, hF]; norm_num
  have ho : Nat.Coprime 2 (Nat.card Fˣ) := by rw [hc]; decide
  simpa only [hc] using orders_of_torus H K hKH S (normalizerImageEquiv H K hKH S e) q ho

private theorem projectiveUnitary_orders (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K)
    (h : ClassicalGroup.IsPSU (Source.starImage H K) 3 8) :
    Nat.Coprime 3 (Nat.card (residualIn 3 (borelResidual (componentBorel H K hKH S)))) ∧
      21 ∣ Nat.card (borelResidual (componentBorel H K hKH S)) := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := h
  let Q := (componentStarSylow H K hKH S).mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨_, _, _, q, _⟩ := UnitaryThree.psu_borel_quotient J 3 (by decide) (by simpa using hF) (by simpa using hconj) Q
  let J₀ := CFSG.Quasithin.ChapterF.Source.Unitary.FormTransport.standardForm J
  let A := Fˣ ⧸ (BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne J₀ ⊓ rootsOfUnity 3 F)
  have hc : Nat.card A = 21 := by
    rw [Nat.card_congr
      (BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.projectiveEquiv J₀ rfl).toEquiv,
      BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.projective_card J₀ rfl hF hconj]
    norm_num
  have ho : Nat.Coprime 2 (Nat.card A) := by rw [hc]; decide
  simpa only [hc] using orders_of_torus H K hKH S (normalizerImageEquiv H K hKH S e) q ho

/-- The four actual exceptional carriers discharge the intrinsic order premise
of the source noncontainment reduction, retaining the lift's two-group kernel. -/
theorem borelOrderFacts_of_exceptionalModels (H K : Subgroup G) (hKH : K ≤ H) (S : Sylow 2 K)
    (h : ExceptionalModels (Source.starImage H K)) : BorelOrderFacts H K hKH S := by
  have hthree : Nat.Coprime 3
      (Nat.card (residualIn 3 (borelResidual (componentBorel H K hKH S)))) ∧
      3 ∣ Nat.card (borelResidual (componentBorel H K hKH S)) := by
    rcases h with h | h | h | h
    · exact linearTwo_orders H K hKH S h
    · obtain ⟨hc, hd⟩ := linearThree_orders H K hKH S h
      exact ⟨hc, (by decide : 3 ∣ 9).trans hd⟩
    · obtain ⟨hc, hd⟩ := projectiveUnitary_orders H K hKH S h
      exact ⟨hc, (by decide : 3 ∣ 21).trans hd⟩
    · obtain ⟨hc, hd⟩ := specialUnitary_orders H K hKH S h
      exact ⟨hc, (by decide : 3 ∣ 63).trans hd⟩
  refine ⟨hthree.1, hthree.2, ?_, ?_⟩
  · intro hSL
    exact (linearThree_orders H K hKH S hSL).2
  · intro hSU
    exact (by decide : 9 ∣ 63).trans (specialUnitary_orders H K hKH S hSU).2

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.Containment.Reduction
