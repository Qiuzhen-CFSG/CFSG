module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryLift
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFactors
public import Theory.SpecificGroups.SymmetricThree.CubicSelection
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent

/-!
# The component sieve for the actual reduced transvection factors

A subnormal symmetric factor of degree at least five contributes its literal
solvable residual, isomorphic to the alternating subgroup, as a component.
A subnormal binary linear factor of degree at least three is itself a
component. The ambient cubic exclusions therefore remove binary degrees
four and five, all symmetric degrees at least six, and both permutation-core
rows from G.6.4. The surviving factors retain their original marked actions:
the binary natural modules of degrees two and three, and the natural S₅ module.

For the S₃ row, the actual two-residual has order three. For the other rows,
the two-residual equals the solvable residual, and its central quotient is
L₃(2) or A₅. Applied to the central cover of the literal W/Z_S image, these
residuals lift to genuine components of N_G(Z_S)/O₂(N_G(Z_S)), with both
quotient maps and the inclusion in the centralizer image retained. Each lift
is identified with the literal residual of the factor preimage. The odd-rank
bounds force its ambient component orbit to have size at most two, so every
cubic in the original normalizer quotient preserves that lifted component.

The final theorem is conditional on a classified subnormal factor of this
specific image; it does not construct a complete compatible factor family.
Factor assembly, removal of the remaining central covering kernel,
normalization of the full factors (including the solvable factors), the parabolic/amalgam
contradiction, initial 6.1.4–5 and unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, printed pp.674–675; G.6.4, pp.345–346.
-/


public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFactorSieve

private theorem map_center {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (centerCongr e ⟨a,ha⟩).property
  · intro hb
    exact ⟨e.symm b,(centerCongr e.symm ⟨b,hb⟩).property,e.apply_symm_apply b⟩

private def quotientCenterEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : (A ⧸ center A) ≃* B :=
  (QuotientGroup.congr _ _ e (map_center e)).trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)

private theorem alternating_quasisimple {m : ℕ} (hm : 5 ≤ m) :
    IsQuasisimple (alternatingGroup (Fin m)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simpa using hm)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup (by simpa using hm)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ m by omega)))).trans
        QuotientGroup.quotientBot).isSimpleGroup

/-- The actual residual of a subnormal symmetric factor is a component,
with its central quotient marked by the alternating subgroup. -/
theorem symmetric_residual_component {B : Type*} [Group B] [Finite B]
    (K : Subgroup B) (hK : K.IsSubnormal) {m : ℕ} (hm : 5 ≤ m)
    (e : K ≃* Equiv.Perm (Fin m)) :
    let D := (solvableResidual K).map K.subtype
    IsComponent B D ∧ Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin m)) := by
  let := alternating_quasisimple hm
  have hr : solvableResidual (Equiv.Perm (Fin m)) = alternatingGroup (Fin m) := by
    apply le_antisymm
    · exact (solvableResidual_le_derivedSeries 1).trans_eq
        (alternatingGroup.commutator_perm_eq (by simpa using hm))
    · exact le_solvableResidual_of_isPerfect _
  let D := (solvableResidual K).map K.subtype
  let eD : D ≃* alternatingGroup (Fin m) :=
    ((solvableResidual K).equivMapOfInjective K.subtype K.subtype_injective).symm.trans
      ((e.subgroupMap (solvableResidual K)).trans (MulEquiv.subgroupCongr (by
        rw [map_solvableResidual_eq _ e.surjective,hr])))
  have hd : D.IsSubnormal :=
    ((inferInstance : (solvableResidual K).Normal).isSubnormal).trans' hK
  exact ⟨⟨hd,IsQuasisimple.of_mulEquiv eD.symm⟩,
    ⟨quotientCenterEquiv eD (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ m by omega)))⟩⟩

private theorem binary_quasisimple {m : ℕ} (hm : 3 ≤ m) :
    IsQuasisimple (BinaryLinear.OuterCyclic.LinearGroup m) := by
  let E := BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < m)
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :=
    Atlas.sl_perfect m hm
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin m) (ZMod 2)) :=
    Atlas.psl_simple_high_rank m hm
  let : IsQuasisimple (Matrix.ProjectiveSpecialLinearGroup (Fin m) (ZMod 2)) := {
    toIsPerfect := Atlas.psl_perfect m hm
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (Group.IsPerfect.center_quotient_center_eq_bot _)).trans QuotientGroup.quotientBot).isSimpleGroup }
  exact IsQuasisimple.of_mulEquiv E

private theorem binary_center {m : ℕ} (hm : 0 < m) :
    center (BinaryLinear.OuterCyclic.LinearGroup m) = ⊥ := by
  rw [←map_center (BinaryLinear.OuterCyclic.slEquivLinear m),
    BinaryLinear.OuterCyclic.binary_center_eq_bot hm,Subgroup.map_bot]

/-- A subnormal binary factor of degree at least three is itself a component. -/
theorem binary_component {B : Type*} [Group B] [Finite B]
    (K : Subgroup B) (hK : K.IsSubnormal) {m : ℕ} (hm : 3 ≤ m)
    (e : K ≃* BinaryLinear.OuterCyclic.LinearGroup m) :
    IsComponent B K ∧ Nonempty ((K ⧸ center K) ≃* BinaryLinear.OuterCyclic.LinearGroup m) := by
  let := binary_quasisimple hm
  exact ⟨⟨hK,IsQuasisimple.of_mulEquiv e.symm⟩,
    ⟨quotientCenterEquiv e (binary_center (by omega))⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFactorSieve

open CFSG.Quasithin.ChapterG.Section06
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open NaturalFactorSieve
universe u

/-- The ambient cubic's component exclusions reduce every actual subnormal
G.6.4 factor to its marked S₃, L₃(2), or natural S₅ action. -/
theorem factor_model_small_of_component_exclusions
    {B V : Type u} [Group B] [Finite B] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) B V)
    (hAlt : ∀ D : Subgroup B, IsComponent B D → ∀ m, 6 ≤ m →
      ¬ Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin m)))
    (hBin : ∀ D : Subgroup B, IsComponent B D → ∀ m, m = 4 ∨ m = 5 →
      ¬ Nonempty ((D ⧸ center D) ≃* BinaryLinear.OuterCyclic.LinearGroup m))
    (K : Subgroup B) (hK : K.IsSubnormal) (W : Submodule (ZMod 2) V)
    (hm : FactorModel ρ K W) : SmallFactorModel ρ K W := by
  rcases hm with ⟨m,hlo,hhi,hm⟩ | ⟨m,hlo,hhi,hm⟩ | ⟨m,hm,he⟩
  · by_cases h2 : m = 2
    · subst m
      exact Or.inl hm
    by_cases h3 : m = 3
    · subst m
      exact Or.inr (Or.inl hm)
    obtain ⟨e,_,_,_⟩ := hm
    obtain ⟨hcomp,he⟩ := binary_component K hK (by omega) e
    exact (hBin K hcomp m (by omega) he).elim
  · have heq : m = 5 := by
      by_contra hn
      obtain ⟨e,_,_,_⟩ := hm
      obtain ⟨hcomp,he⟩ := symmetric_residual_component K hK hlo e
      exact hAlt _ hcomp m (by omega) he
    subst m
    exact Or.inr (Or.inr hm)
  · obtain ⟨e,_,_,_⟩ := he
    obtain ⟨hcomp,he⟩ := symmetric_residual_component K hK (by omega) e
    exact (hAlt _ hcomp m (by omega) he).elim

/-- In particular each selected direct factor retains its original marked
small action on the literal transvection displacement orbit. -/
theorem TransvectionFactorModel.small_of_component_exclusions
    {B V : Type u} [Group B] [Finite B] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) B V} {t : B} (d : TransvectionFactorModel ρ t)
    (hAlt : ∀ D : Subgroup B, IsComponent B D → ∀ m, 6 ≤ m →
      ¬ Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin m)))
    (hBin : ∀ D : Subgroup B, IsComponent B D → ∀ m, m = 4 ∨ m = 5 →
      ¬ Nonempty ((D ⧸ center D) ≃* BinaryLinear.OuterCyclic.LinearGroup m)) :
    SmallFactorModel ρ (normalClosure ({t} : Set B)) d.space.toSubmodule :=
  factor_model_small_of_component_exclusions ρ hAlt hBin _
    (inferInstance : (normalClosure ({t} : Set B)).Normal).isSubnormal _ d.model

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFactorSieve
/-- The two-residual of the solvable binary degree-two factor is its actual
normal cubic, rather than a quasisimple component. -/
theorem binary_two_residual {K : Type*} [Group K] [Finite K]
    (e : K ≃* BinaryLinear.OuterCyclic.LinearGroup 2) :
    Nat.card (pResidual 2 K) = 3 ∧ Nonempty (K ≃* Equiv.Perm (Fin 3)) := by
  let E := e.trans ((BinaryLinear.OuterCyclic.slEquivLinear 2).symm.trans
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))
  have hc : Nat.card ((pResidual 2 K).map E.toMonoidHom) = Nat.card (pResidual 2 K) :=
    card_map_of_injective E.injective
  rw [map_pResidual_of_surjective 2 E.toMonoidHom E.surjective,
    Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card] at hc
  exact ⟨hc.symm,⟨E⟩⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFactorSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFactorSieve
private theorem solvableResidual_le_twoResidual {A : Type*} [Group A] [Finite A] :
    solvableResidual A ≤ pResidual 2 A := by
  apply le_sInf
  rintro N ⟨hn,hN⟩
  let := hn
  let : Group.IsNilpotent (A ⧸ N) := hN.isNilpotent
  exact solvableResidual_le_of_solvable_quotient N

private theorem symmetric_residuals {K : Type*} [Group K] [Finite K]
    {m : ℕ} (hm : 5 ≤ m) (e : K ≃* Equiv.Perm (Fin m)) :
    pResidual 2 K = solvableResidual K := by
  let := alternating_quasisimple hm
  have hr : solvableResidual (Equiv.Perm (Fin m)) = alternatingGroup (Fin m) := by
    exact le_antisymm
      ((solvableResidual_le_derivedSeries 1).trans_eq
        (alternatingGroup.commutator_perm_eq (by simpa using hm)))
      (le_solvableResidual_of_isPerfect _)
  have hp : pResidual 2 (Equiv.Perm (Fin m)) = alternatingGroup (Fin m) := by
    refine le_antisymm ?_ (hr ▸ solvableResidual_le_twoResidual)
    apply sInf_le
    refine ⟨inferInstance,IsPGroup.of_card (n := 1) ?_⟩
    let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
    change (alternatingGroup (Fin m)).index = 2^1
    simp
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,
    map_solvableResidual_eq _ e.surjective,hp,hr]
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFactorSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open NaturalFactorSieve
universe u
/-- The source residuals of every surviving factor: the S₃ row has a cubic
 two-residual; the other rows have an actual component, equal to both residuals. -/
theorem small_factor_residual_alternatives
    {B V : Type u} [Group B] [Finite B] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) B V) (K : Subgroup B) (hK : K.IsSubnormal)
    (W : Submodule (ZMod 2) V) (hm : SmallFactorModel ρ K W) :
    (Nonempty (K ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pResidual 2 K) = 3) ∨
      (let D := (solvableResidual K).map K.subtype
       IsComponent B D ∧ (pResidual 2 K).map K.subtype = D ∧
         (Nonempty ((D ⧸ center D) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
          Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin 5)))) := by
  rcases hm with ⟨e,_,_,_⟩ | ⟨e,_,_,_⟩ | ⟨e,_,_,_⟩
  · obtain ⟨hc,he⟩ := binary_two_residual e
    exact Or.inl ⟨he,hc⟩
  · obtain ⟨hcomp,he⟩ := binary_component K hK (by decide : 3 ≤ 3) e
    let := hcomp.2
    have hr : solvableResidual K = ⊤ := solvableResidual_eq_top
    have hp : pResidual 2 K = ⊤ := top_unique (hr ▸ solvableResidual_le_twoResidual)
    have hd : (solvableResidual K).map K.subtype = K := by
      rw [hr,←MonoidHom.range_eq_map,range_subtype]
    exact Or.inr ⟨hd.symm ▸ hcomp,by rw [hp,hr],Or.inl (hd.symm ▸ he)⟩
  · obtain ⟨hcomp,he⟩ := symmetric_residual_component K hK (by decide : 5 ≤ 5) e
    exact Or.inr ⟨hcomp,by rw [symmetric_residuals (by decide : 5 ≤ 5) e],Or.inr he⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFactorSieve
/-- A lifted component is the literal solvable residual of the full factor
preimage under the central covering map. -/
theorem component_eq_factor_residual_preimage
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (φ : A →* B) (hs : Function.Surjective φ) (hk : φ.ker ≤ center A)
    (K : Subgroup B) (C : Subgroup A) (hC : IsComponent A C)
    (hm : C.map φ = (solvableResidual K).map K.subtype) :
    C = (solvableResidual (K.comap φ)).map (K.comap φ).subtype := by
  let := hC.2
  let : IsMulCommutative φ.ker := ⟨⟨fun a b =>
    Subtype.ext ((mem_center_iff.mp (hk a.property) b).symm)⟩⟩
  let P := (solvableResidual (K.comap φ)).map (K.comap φ).subtype
  let : Group.IsPerfect P := Group.IsPerfect.ofSurjective
    ((K.comap φ).subtype.subgroupMap_surjective (solvableResidual (K.comap φ)))
  have hP : P.map φ = C.map φ := (map_solvableResidual_comap φ hs K).trans hm.symm
  have hPC : P ≤ C ⊔ φ.ker := by
    rw [←comap_map_eq]
    exact map_le_iff_le_comap.mp hP.le
  apply le_antisymm
  · apply le_map_solvableResidual_of_isPerfect
    apply map_le_iff_le_comap.mp
    rw [hm]
    exact map_subtype_le _
  · have hh := le_map_solvableResidual_of_isPerfect P (C ⊔ φ.ker) hPC
    rwa [hC.isCComponent.solvableResidual_sup_eq φ.ker le_normalizer_of_normal] at hh
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFactorSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
/-- Every cubic in the actual normalizer two-core quotient preserves each
ordinary component. This uses all odd-rank bounds and does not presume that
the cubic preserves W or the chosen transvection closure. -/
theorem quotient_cubic_normalizes_component
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (K : Subgroup (Escape.H (T : Subgroup G) L R ⧸ pCore 2 (Escape.H (T : Subgroup G) L R)))
    (hK : IsComponent _ K)
    (c : Escape.H (T : Subgroup G) L R ⧸ pCore 2 (Escape.H (T : Subgroup G) L R))
    (hc : c^3=1) : c ∈ normalizer (K : Set _) := by
  let N := Escape.H (T : Subgroup G) L R
  have hsq : IsSQTK KnownSimple.IsKnownSimple N := h.simpleQTKE.twoLocal_sqtk
    ⟨ZS (T : Subgroup G) L R,h.ZS_ne_bot,T.isPGroup'.to_le h.ZS_le_T,rfl⟩
  have hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p (N ⧸ pCore 2 N) ≤ 2 := by
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  rcases hK.normal_or_index_two_of_odd_rank_le_two hrank with hn | hi
  · let := hn
    rw [normalizer_eq_top]
    exact mem_top c
  · let H := normalizer (K : Set (N ⧸ pCore 2 N))
    let : H.Normal := H.normal_of_index_eq_two hi
    let q := QuotientGroup.mk' H
    have hcard : Nat.card ((N ⧸ pCore 2 N) ⧸ H) = 2 := hi
    have h2 : q c ^ 2 = 1 := by simpa only [hcard] using pow_card_eq_one' (x := q c)
    have h3 : q c ^ 3 = 1 := by rw [←map_pow,hc,map_one]
    have h1 : q c = 1 := by simpa only [pow_succ,h2,one_mul] using h3
    exact (QuotientGroup.eq_one_iff c).mp h1
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u v w
/-- Component lifting and the model sieve commute with taking the literal
factor residual. This boundary keeps the representation independent of the
ambient quotient's construction. -/
private theorem small_factor_lifts
    {B V : Type u} [Group B] [Finite B] [AddCommGroup V] [Module (ZMod 2) V]
    {A : Type v} [Group A] [Finite A] {N : Type w} [Group N]
    (ρ : Representation (ZMod 2) B V) (φ : A →* B)
    (hs : Function.Surjective φ) (hk : φ.ker ≤ center A)
    (j : A →* N) (Q : Subgroup N)
    (hnorm : ∀ K : Subgroup N, IsComponent N K → ∀ c : N,
      c ^ 3 = 1 → c ∈ normalizer (K : Set N))
    (hlift : ∀ D : Subgroup B, IsComponent B D →
      ∃ C : Subgroup A, IsComponent A C ∧ C.map φ = D ∧
        IsComponent N (C.map j) ∧
        Nonempty (((C.map j) ⧸ center (C.map j)) ≃* (D ⧸ center D)) ∧
        C.map j ≤ Q ∧
        (∀ m, 6 ≤ m → ¬ Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin m))) ∧
        (∀ m, m = 4 ∨ m = 5 →
          ¬ Nonempty ((D ⧸ center D) ≃* BinaryLinear.OuterCyclic.LinearGroup m))) :
    ∀ (K : Subgroup B), K.IsSubnormal → ∀ U : Submodule (ZMod 2) V,
      ChapterG.Section06.FactorModel ρ K U →
      ChapterG.Section06.SmallFactorModel ρ K U ∧
      ((Nonempty (K ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pResidual 2 K) = 3) ∨
       (let D := (solvableResidual K).map K.subtype
        (pResidual 2 K).map K.subtype = D ∧
        ∃ C : Subgroup A,
          C = (solvableResidual (K.comap φ)).map (K.comap φ).subtype ∧
          IsComponent A C ∧ C.map φ = D ∧
          IsComponent N (C.map j) ∧
          Nonempty (((C.map j) ⧸ center (C.map j)) ≃* (D ⧸ center D)) ∧
          C.map j ≤ Q ∧
          (∀ c : N, c ^ 3 = 1 → c ∈ Subgroup.normalizer (C.map j : Set N)) ∧
          (Nonempty ((D ⧸ center D) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
           Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin 5))))) := by
  intro K hK U hmodel
  have hsmall := factor_model_small_of_component_exclusions ρ
    (fun D hD m hm => by
      obtain ⟨C,hC,hCD,hCN,he,hCI,ha,hb⟩ := hlift D hD
      exact ha m hm)
    (fun D hD m hm => by
      obtain ⟨C,hC,hCD,hCN,he,hCI,ha,hb⟩ := hlift D hD
      exact hb m hm) K hK U hmodel
  refine ⟨hsmall,?_⟩
  rcases small_factor_residual_alternatives ρ K hK U hsmall with hthree | ⟨hD,hr,heD⟩
  · exact Or.inl hthree
  · obtain ⟨C,hC,hCD,hCN,he,hCI,ha,hb⟩ := hlift _ hD
    exact Or.inr ⟨hr,C,
      NaturalFactorSieve.component_eq_factor_residual_preimage φ hs hk K C hC hCD,
      hC,hCD,hCN,he,hCI,hnorm _ hCN,heD⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d

/-- The literal reduced image has only the three small marked factor actions.
The nonsolvable factors' actual two-residuals lift to ambient components;
the solvable row retains its normal cubic. The component lifts are the
literal preimage residuals and are normalized by every ambient cubic.
Normalization of full factors and the amalgam conclusion remain open. -/
theorem exists_ambient_reduced_small_factor_lifts
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      letI := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Surjective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧
          let θ := Representation.ofElementaryAbelianAction
            (A := g.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
          ∀ (K : Subgroup g.range), K.IsSubnormal →
            ∀ U : Submodule (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)),
              ChapterG.Section06.FactorModel θ K U →
              ChapterG.Section06.SmallFactorModel θ K U ∧
                ((Nonempty (K ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pResidual 2 K) = 3) ∨
                 (let D := (solvableResidual K).map K.subtype
                  (pResidual 2 K).map K.subtype = D ∧
                  ∃ C : Subgroup (P ⧸ pCore 2 P),
                    C = (solvableResidual (K.comap φ)).map (K.comap φ).subtype ∧
                    IsComponent _ C ∧ C.map φ = D ∧
                    IsComponent (N ⧸ pCore 2 N) (C.map j) ∧
                    Nonempty (((C.map j) ⧸ center (C.map j)) ≃* (D ⧸ center D)) ∧
                    C.map j ≤ (I.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)) ∧
                    (∀ c : N ⧸ pCore 2 N, c ^ 3 = 1 →
                      c ∈ Subgroup.normalizer (C.map j : Set (N ⧸ pCore 2 N))) ∧
                    (Nonempty ((D ⧸ center D) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
                     Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin 5))))) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIW,hZ,σ,hσ,hX,hA,hpos,hsize,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hcore,hlift⟩ :=
    d.exists_ambient_reduced_component_lifts h hnat hE hs hNS hab
  let I := Escape.I (T : Subgroup G) L R
  let Z := ZS (T : Subgroup G) L R
  let W := Escape.U (T : Subgroup G) L R ⊓
    conjugateSpanBy Z (centralizer ({z} : Set G))
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let P := conjugateSpanBy E I
  let := hZ
  let := hX
  let g := σ.comp (inclusion hPI)
  let θ := Representation.ofElementaryAbelianAction
    (A := g.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIW,hZ,σ,hσ,hX,hA,hpos,hsize,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hcore,?_⟩
  exact small_factor_lifts θ φ hφ hφc j
    ((I.subgroupOf (Escape.H (T : Subgroup G) L R)).map (QuotientGroup.mk' _))
    (quotient_cubic_normalizes_component h) hlift

end NaturalEscapeGraph.OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
