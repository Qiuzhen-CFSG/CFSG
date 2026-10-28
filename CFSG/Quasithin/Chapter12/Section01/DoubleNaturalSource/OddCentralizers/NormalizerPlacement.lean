module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.OddCentralizers.NormalizerReduction
public import CFSG.Quasithin.Chapter4.Section04.OddActorQuotient
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ComponentPlacement
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.AutomorphismModel.Structure

/-!
# Full-orbit placement in the original odd normalizer

The fixed residual inherits the literal L/O₂(L) marking, including its
formula on representatives. Its action on a selected component either is
inner or produces an actual GLₙ(2) section of the outer automorphism group.
In the inner case, residual uniqueness places the residual inside the
component. The earlier full-orbit core containment then places all of W
there, without identifying W with the chosen seed V. The component is
normal in N(A), its centralizer is the odd core, and its central quotient
has two-rank at least 2n.

NormalizerComponentModels and DoubleNaturalExcludedOddNormalizers apply
these results to the original degree-five branch. Residual uniqueness
is an explicit branch premise; this module does not assert 12.1.9(1).
Source: Aschbacher--Smith, 4.4.5 and 4.4.10--11, printed pp.620--621.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  {n : ℕ} (B : DoubledBranch T L V n)
include D h B

/-- The actual fixed residual inherits the original component marking on every representative. -/
theorem doubledOrbit_oddActorResidual_marking (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A)) :
    ∃ e : (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) ≃* LinearGroup n,
      ∀ x : oddActorResidual L A,
        e (QuotientGroup.mk' (pCore 2 (oddActorResidual L A)) x) =
          B.component (QuotientGroup.mk' (pCore 2 L)
            ⟨x.val,((oddActorResidual_le L A).trans inf_le_left) x.property⟩) := by
  obtain ⟨e,he⟩ := chosen_oddActorResidual_quotient h.toHypothesis1221 D A
    (hA.trans inf_le_left)
    ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T)))
  exact ⟨e.trans B.component, fun x => congrArg B.component (he x)⟩

/-- The literal residual either acts inner or has its marked simple quotient as an outer section. -/
theorem doubledOrbit_oddNormalizer_inner_or_outer_section (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) :
    (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G))) ∨
    ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* LinearGroup n,
      Function.Surjective f := by
  classical
  let : IsSimpleGroup (LinearGroup n) := AutomorphismModel.linear_simple (by have := B.degree; omega)
  by_cases hout : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* LinearGroup n, Function.Surjective f
  · exact Or.inr hout
  apply Or.inl
  let F := oddActorResidual L A
  let N := normalizer (A : Set G)
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let u : F.subgroupOf N ≃* F := subgroupOfEquivOfLe hFN
  obtain ⟨e,_⟩ := D.doubledOrbit_oddActorResidual_marking h B A hA ho
  let q : F.subgroupOf N →* LinearGroup n := e.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 F)).comp u.toMonoidHom)
  have hq : Function.Surjective q := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp u.surjective)
  have hk : q.ker = (pCore 2 F).comap u.toMonoidHom := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, ← MonoidHom.comap_ker,
      QuotientGroup.ker_mk']
  have hp : IsPGroup 2 q.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective u.toMonoidHom u.injective
  let : Group.IsNilpotent q.ker := hp.isNilpotent
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := u.symm.toMonoidHom) u.symm.surjective
  obtain ⟨_,hFK,_⟩ := chosen_oddNormalizer_component_normalization h.toHypothesis1221 D
    A (hA.trans inf_le_left)
    ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T))) K hK
  exact perfect_le_sup_centralizer_of_no_simple_outer_section K (F.subgroupOf N) q hq
    (fun U f hf => hout ⟨U,f,hf⟩) hFK

/-- Inner action puts the whole doubled orbit inside one normal component,
whose odd center preserves its two-rank. The seed and full orbit remain distinct. -/
theorem doubledOrbit_oddNormalizer_inner_placement (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (componentOrbit V (T : Subgroup G) : Set G))
    (ho : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hi : (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G)))) :
    K.Normal ∧ componentOrbit V (T : Subgroup G) ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) =
        pPrimeCore 2 (normalizer (A : Set G)) ∧
      2 * n ≤ primeRank 2 (K ⧸ center K) := by
  have hs : normalizer (L : Set G) ⊓ centralizer (V : Set G) ≤ sectionCentralizer L := by
    let := h.quasisimple
    apply relative_module_centralizer_le_sectionCentralizer L V D.normalizes _ D.ne_bot D.eq_commutator
    exact (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans D.core_centralizes
  obtain ⟨hn,hv,hf,hcent⟩ := normal_component_of_inner_action h.toHypothesis1221 D hs
    A (hA.trans inf_le_left)
    ((le_sectionCentralizer_iff A L).mp
      (hA.trans (D.doubledOrbit_relative_centralizer_le_sectionCentralizer h))).2 ho
    ((hA.trans inf_le_right).trans (centralizer_le (le_componentOrbit V T))) hu hout K hK houtK hi
  have hw : componentOrbit V (T : Subgroup G) ≤ K.map (normalizer (A : Set G)).subtype :=
    ((D.doubledOrbit_oddActorResidual_cover h A hA ho).2.2.1.trans (pCoreIn_le 2 _)).trans hf
  let W := componentOrbit V (T : Subgroup G)
  let N := normalizer (A : Set G)
  have hZC : (center K).map K.subtype ≤ centralizer (K : Set N) := by
    rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg K.subtype (mem_center_iff.mp hz ⟨y,hy⟩)
  have hoC : Odd (Nat.card (centralizer (K : Set N))) := by
    rw [hcent]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hoZ : Odd (Nat.card (center K)) := by
    have hh := hoC.of_dvd_nat (card_dvd_of_le hZC)
    rwa [card_map_of_injective K.subtype_injective] at hh
  have hWR : primeRank 2 W ≤ primeRank 2 K := by
    have hh := primeRank_mono 2 hw
    rwa [← primeRank_equiv 2 (K.equivMapOfInjective N.subtype N.subtype_injective)] at hh
  have hRK : primeRank 2 W ≤ primeRank 2 (K ⧸ center K) := hWR.trans
    (primeRank_le_of_coprime_ker 2 (QuotientGroup.mk' (center K)) (by
      rw [QuotientGroup.ker_mk']; exact hoZ.coprime_two_left))
  let := D.doubledOrbit_elementary h
  have hc : Nat.card W = 2 ^ (2 * n) := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_congr Additive.toMul,B.finrank_eq,Nat.card_zmod] at hh
    exact hh
  have hr : 2 * n ≤ primeRank 2 W := by
    let : IsElementaryAbelian 2 (⊤ : Subgroup W) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup W).subtype (⊤ : Subgroup W).subtype_injective
    apply IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup W)
    simpa only [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup W) ≃* W).toEquiv] using hc
  exact ⟨hn,hw,hf,hcent,hr.trans hRK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
