module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearConstrainedMoved

/-!
# Excluding every constrained component for the original nonbinary pair

The actual binary SL4/SL5 moved module contains the unchanged source orbit,
whose dimension is at least twelve. Natural, orthogonal, exterior and
natural-plus-dual rows all have dimension at most ten. Every repeated-natural
row fails the original residual's inequivalent-pair bound. These are the full
B.5.1 alternatives on the actual moved module, with its central attachment
controlled by the proved native cohomology calculation.
Source: Aschbacher--Smith B.5.1, C.4.5--8 and 7.3.4, printed pp.99,152--154,699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
private theorem moved_intertwines_original
    {W LH Kg R : Subgroup G} [IsElementaryAbelian 2 W]
    (hLW : LH ≤ normalizer (W : Set G)) (hLKg : LH ≤ Kg)
    {O : Subgroup (StarQuotient Kg R)} (hCO : starImage Kg R Kg ≤ O)
    (s : MovedSection ((starRepresentation Kg R).comp O.subtype)
      ((starImage Kg R Kg).subgroupOf O))
    (i : Additive W →ₗ[ZMod 2] s.space.toSubmodule)
    (hiambient : ∀ v, (((i v).val.toMul : (Kg ⊔ R : Subgroup G)) : G) = v.toMul) :
    let q : LH →* (starImage Kg R Kg).subgroupOf O :=
      (subgroupOfEquivOfLe hCO).symm.toMonoidHom.comp
        ((toStarImage Kg R).comp (inclusion hLKg))
    ∀ l v, i (doubledSeedAction LH W hLW l v) = s.space.toRepresentation (q l) (i v) := by
  intro q l v
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [hiambient]
  change _ = (((starRepresentation Kg R
    (QuotientGroup.mk' (starKernel Kg R) ⟨l,mem_sup_left (hLKg l.property)⟩)
    (i v).val).toMul : (Kg ⊔ R : Subgroup G)) : G)
  rw [starRepresentation_apply]
  change (l : G) * (v.toMul : G) * (l : G)⁻¹ =
    (l : G) * (((i v).val.toMul : (Kg ⊔ R : Subgroup G)) : G) * (l : G)⁻¹
  rw [hiambient]

private theorem no_repeated_source
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let ρ := starRepresentation (K.map H.subtype) (J.pCoreIn 2)
    let O := offenderSubgroup ρ
    let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
    ∀ (_hCO : C ≤ O)
      (s : MovedSection (ρ.comp O.subtype) (C.subgroupOf O))
      (i : Additive D.sourceOrbit →ₗ[ZMod 2] s.space.toSubmodule),
      (∀ v, (((i v).val.toMul : (K.map H.subtype ⊔ J.pCoreIn 2 : Subgroup G)) : G) = v.toMul) →
      Function.Injective i → ∀ n, (n = 4 ∨ n = 5) → ∀ r,
        ¬ IsRepeatedLinearNatural (s.space.toRepresentation.comp (C.subgroupOf O).subtype)
          BinaryField.two n r := by
  intro ρ O C hCO s i hiambient hi n hn r hrep
  let Kg := K.map H.subtype
  let R := J.pCoreIn 2
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_linear_witness_hypothesisC28 h hd F hmodel hw hWJ hJC
  have hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
  have hLHH : LH ≤ H := hc.component_le.trans hc.local_le
  obtain ⟨_,hLK⟩ := D.sourceOrbit_linear_witness_constrained_placement
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK
  have hLKg : LH ≤ Kg := by
    have hh := map_mono (f := H.subtype) hLK
    rwa [map_subgroupOf_eq_of_le hLHH] at hh
  let q : LH →* C.subgroupOf O := (subgroupOfEquivOfLe hCO).symm.toMonoidHom.comp
    ((toStarImage Kg R).comp (inclusion hLKg))
  have hie := moved_intertwines_original (hLH.trans D.sourceOrbit_component_normalizes)
    hLKg hCO s i hiambient
  obtain ⟨a⟩ := hrep
  let b := a.groupEquiv.toMonoidHom.comp q
  let σ : Representation (ZMod 2) LH (Fin n → BinaryField.two.Carrier) :=
    (linearNatural BinaryField.two n).comp b
  let τ : Representation (ZMod 2) LH (Fin r → Fin n → BinaryField.two.Carrier) :=
    (repeated (linearNatural BinaryField.two n) r).comp b
  apply D.sourceOrbit_linear_witness_no_small_repeated h hd F hmodel hw σ τ
    (fun _ _ _ => rfl) (by
      change Module.finrank (ZMod 2) (Fin n → ZMod 2) < 6 * F.degree
      simp only [Module.finrank_fin_fun]
      rcases hn with rfl | rfl <;> omega) (a.linearEquiv.toLinearMap.comp i) (a.linearEquiv.injective.comp hi)
  intro l v
  change a.linearEquiv (i (doubledSeedAction LH D.sourceOrbit _ l v)) = _
  rw [hie]
  exact a.intertwines (q l) (i v)

private theorem no_large_binary_moved
    {E Y : Type*} [Group E] [Finite E] [AddCommGroup Y] [Module (ZMod 2) Y]
    [FiniteDimensional (ZMod 2) Y]
    {ρ : Representation (ZMod 2) E Y} {C : Subgroup E}
    (s : MovedSection ρ C) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hc : BinaryActor.MovedCase s n)
    (hd : 12 ≤ Module.finrank (ZMod 2) s.space.toSubmodule)
    (hrep : ∀ r, ¬ IsRepeatedLinearNatural (s.space.toRepresentation.comp C.subtype)
      BinaryField.two n r) : False := by
  cases hc with
  | natural e =>
    have hh := e.linearEquiv.finrank_eq
    change Module.finrank (ZMod 2) s.space.toSubmodule =
      Module.finrank (ZMod 2) (Fin n → ZMod 2) at hh
    simp only [Module.finrank_fin_fun] at hh
    omega
  | orthogonal _ _ _ hdim => omega
  | exterior _ _ _ hdim => omega
  | naturalDual hnat =>
    obtain ⟨e⟩ := hnat
    have hh := e.linearEquiv.finrank_eq
    change Module.finrank (ZMod 2) s.space.toSubmodule =
      Module.finrank (ZMod 2) ((Fin n → ZMod 2) × Module.Dual (ZMod 2) (Fin n → ZMod 2)) at hh
    rw [Module.finrank_prod,Subspace.dual_finrank_eq] at hh
    simp only [Module.finrank_fin_fun] at hh
    omega
  | repeatedNatural r _ _ hr => exact hrep r hr

/-- Every actual constrained component in the original nonbinary reciprocal
witness is impossible; the star placement and whole moved-module embedding
are produced internally from that same witness. -/
theorem sourceOrbit_linear_witness_not_constrained
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : False := by
  obtain ⟨hCO,c,i,hiambient,hi⟩ := D.sourceOrbit_linear_witness_constrained_classified_embedding
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK
  have hdim := LinearMap.finrank_le_finrank_of_injective hi
  rw [D.sourceOrbit_linear_dimension h hd F hmodel] at hdim
  have hlarge : 12 ≤ Module.finrank (ZMod 2) c.sectionData.space.toSubmodule := by omega
  have hrep := D.no_repeated_source h hd F hF hmodel hw hWJ hJC K hK hq hout hfK
    hCO c.sectionData i hiambient hi
  rcases D.sourceOrbit_linear_witness_constrained_models
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK with hs | hs
  · obtain ⟨e8⟩ := hs
    let e4 := (subgroupOfEquivOfLe hCO).trans (e8.trans
      (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm.trans
        (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))))
    have hcase := BinaryActor.actionCase _ (Or.inl rfl : 4 = 4 ∨ 4 = 5) e4 c.clause_one
    exact no_large_binary_moved c.sectionData (Or.inl rfl)
      (BinaryActor.movedCase (Or.inl rfl) hcase) hlarge (hrep 4 (Or.inl rfl))
  · obtain ⟨e5⟩ := hs
    let e := (subgroupOfEquivOfLe hCO).trans e5
    have hcase := BinaryActor.actionCase _ (Or.inr rfl : 5 = 4 ∨ 5 = 5) e c.clause_one
    exact no_large_binary_moved c.sectionData (Or.inr rfl)
      (BinaryActor.movedCase (Or.inr rfl) hcase) hlarge (hrep 5 (Or.inr rfl))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
