module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds.Suzuki
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.PrimeBounds.LinearModels
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.Contracts

/-!
# Determining the actual binary component field

Construct a Borel extension in the literal quotient Mc/O₂(Mc), pull it
back through O₂(Mc), and map it into G. This supplies the solvable
H ≤ J ≤ Mc with 2^m-1 dividing its order required by the maximal-prime
arithmetic. Consequently an actual PSL₂(2^m) component with the source
congruence has m=2 at p=3 and m=4 at p=5.

The final application retains the full source setup and consumes the
strict exchanged model on its original relative component. That model
comparison is still unproved; it remains with qt-e-suitable-odd-normalizer,
together with the whole automorphism/wreath quotient and normalizer
assembly. No Borel existence or torus divisor remains as a premise.
The earlier primitive and exchanged-factor producers remain
qt-e-quintic-recognition and qt-e-14612-singleton.

Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The concrete Borel yields an actual solvable overgroup between H and Mc. -/
theorem source_binary_component_solvable_extension
    (T : Sylow 2 G) (H Mc : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hHMc : H ≤ Mc) (hs : Group.IsSolvable H)
    (L : Subgroup G) (hL : (L.subgroupOf Mc).IsCComponent)
    (F : Type*) [Field F] [Finite F] {m : ℕ} (hm : 2 ≤ m)
    (hF : Nat.card F = 2 ^ m)
    (e : ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    ∃ J : Subgroup G, H ≤ J ∧ J ≤ Mc ∧ Group.IsSolvable J ∧
      2 ^ m - 1 ∣ Nat.card J := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let D := (L.subgroupOf Mc).map q
  let S := (T.subtype (hTH.trans hHMc)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Mc))
  let A := (H.subgroupOf Mc).map q
  let := hs
  let : Group.IsSolvable (H.subgroupOf Mc) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hHMc).toMonoidHom)
      (subgroupOfEquivOfLe hHMc).injective
  have hAs : Group.IsSolvable A :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  have hD : D.IsCComponent := hL.map_quotient (pCore 2 Mc)
  obtain ⟨B,hAB,hBs,hd⟩ := binary_psl2_component_solvable_extension S A D
    (map_mono (subgroupOf_mono Mc hTH)) hAs hD F hm hF e
  let J := (B.comap q).map Mc.subtype
  have hHJ : H ≤ J := by
    intro h hh
    exact ⟨⟨h,hHMc hh⟩,hAB (mem_map_of_mem q hh),rfl⟩
  let := hBs
  let : Group.IsSolvable q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsSolvable (B.comap q) := isSolvable_comap_of_solvable_ker q B
  refine ⟨J,hHJ,map_subtype_le _,Group.isSolvable_of_surjective
    (Mc.subtype.subgroupMap_surjective _),?_⟩
  rw [card_map_of_injective Mc.subtype_injective]
  apply hd.trans
  have hc := card_map_dvd (B.comap q) q
  rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (pCore 2 Mc))] at hc

/-- The binary component parameter, with its actual Borel extension constructed. -/
theorem source_binary_component_field_parameter
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M Mc H : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hHMc : H ≤ Mc)
    {p : ℕ} (hp : p = 3 ∨ p = 5) (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (d : PrimitiveResidual H p)
    (L : Subgroup G) (hL : (L.subgroupOf Mc).IsCComponent)
    {m : ℕ} (hm : 2 ≤ m)
    (hmodel : ClassicalGroup.IsPSL
      ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 (2 ^ m))
    (hcong : Nat.ModEq p (2 ^ m) 1) :
    (p = 3 ∧ m = 2) ∨ (p = 5 ∧ m = 4) := by
  obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := hmodel
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  obtain ⟨J,hHJ,hJMc,hJs,hd⟩ := source_binary_component_solvable_extension T H Mc hH.1.2 hHMc
    (primitiveResidual_isSolvable H d) L hL F hm hcard e
  exact source_field_parameter_of_solvable_overgroup hG T hunique hH hp hmax
    J hHJ hJMc hJs hm hd hcong

open Representation.BinaryOffender SourcePreliminaries
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative

/-- In the actual strict exchanged model, the field has order four or sixteen.
The F.9.18 model comparison remains an earlier premise of this local deduction. -/
theorem source_strict_exchanged_component_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p)
    (L : Subgroup G) (hL : (L.subgroupOf Mc).IsCComponent)
    (hmodel : StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L p) :
    (p = 3 ∧ ClassicalGroup.IsPSL
      ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 4) ∨
    (p = 5 ∧ ClassicalGroup.IsPSL
      ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 16) ∨
    (p = 3 ∧ ClassicalGroup.IsPSL
      ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 3 2) := by
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  rcases hmodel.2 with ⟨m,hm,_heven,hcong,hbin⟩ | hlin
  · rcases source_binary_component_field_parameter hG T hunique hH hHMc d.prime hmax
      hprim L hL hm hbin hcong with ⟨hp,rfl⟩ | ⟨hp,rfl⟩
    · exact Or.inl ⟨hp,by norm_num at hbin ⊢; exact hbin⟩
    · exact Or.inr (Or.inl ⟨hp,by norm_num at hbin ⊢; exact hbin⟩)
  · exact Or.inr (Or.inr hlin)
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
