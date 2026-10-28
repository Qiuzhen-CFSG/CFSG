module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdaptedPairNormality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CoreNaturalComplement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LocalExchange

/-!
# Constructing the adapted pair from one source core

A neighbor exchange in the actual middle actor sends the chosen adapted
subgroup at d to the one at beta. Conjugation transports its elementary
structure, normality, order and intersection with V. The pair theorem then
constructs the elementary normal subgroup M of order q⁴ and retains both
factor escapes. The final application starts with the original two natural
core layers and their Cartan intersection equality; no complement is assumed.

The fields at x and d remain distinct, with only their cardinalities equated.
Source: DGS, *Groups and Graphs* (1985), printed p.150, first paragraph.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Exchange one adapted factor inside the actual middle actor to construct M. -/
theorem reduced_adapted_pair_from_one
    (h : HypothesisF11 L S)
    {x beta d : Vertex (Reduction.reducedFamily L S)}
    (hb : (graph (Reduction.reducedFamily L S)).Adj x beta)
    (hd : (graph (Reduction.reducedFamily L S)).Adj x d) (hne : beta ≠ d)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ex : (graphLocalGroup (Reduction.reducedFamily L S) x ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) x)) ≃* SL(2,F))
    (Wd : Subgroup (Reduction.G₀ L S)) [IsElementaryAbelian 2 Wd]
    (hnd : graphLocalGroup (Reduction.reducedFamily L S) d ≤ normalizer (Wd : Set (Reduction.G₀ L S)))
    (hspd : Wd ⊔ V (Reduction.reducedFamily L S) d 1 = Q (Reduction.reducedFamily L S) d)
    (hVd : V (Reduction.reducedFamily L S) d 1 ≤ Q (Reduction.reducedFamily L S) x)
    (hWVd : Wd ⊓ V (Reduction.reducedFamily L S) d 1 = Z (Reduction.reducedFamily L S) d)
    (hωd : Z (Reduction.reducedFamily L S) d =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) d))
    (hZcardd : Nat.card (Z (Reduction.reducedFamily L S) d) = Nat.card F)
    (hWdcard : Nat.card Wd = Nat.card F ^ 3) :
    let Γ := Reduction.reducedFamily L S
    ∃ g : graphLocalGroup Γ x,
      (g : Reduction.G₀ L S) • d = beta ∧ (g : Reduction.G₀ L S) • beta = d ∧
      (g : Reduction.G₀ L S) * g ∈ Q Γ x ∧
      let Wb := Wd.map (MulAut.conj (g : Reduction.G₀ L S)).toMonoidHom
      let M := (Wb ⊓ Q Γ x) ⊔ (Wd ⊓ Q Γ x)
      Wb ⊓ V Γ beta 1 = Z Γ beta ∧ Wb ⊔ V Γ beta 1 = Q Γ beta ∧
      graphLocalGroup Γ beta ≤ normalizer (Wb : Set (Reduction.G₀ L S)) ∧
      IsElementaryAbelian 2 Wb ∧ M ≤ Q Γ x ∧
      graphLocalGroup Γ x ≤ normalizer (M : Set (Reduction.G₀ L S)) ∧
      IsElementaryAbelian 2 M ∧ Nat.card M = Nat.card F ^ 4 ∧
      Disjoint (Wb ⊓ Q Γ x) (Wd ⊓ Q Γ x) ∧
      (¬ Wb ⊓ Q Γ x ≤ V Γ beta 1) ∧ (¬ Wd ⊓ Q Γ x ≤ V Γ d 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  obtain ⟨g,hg,hgd,hgb,hgg⟩ : ∃ g : Reduction.G₀ L S,
      g ∈ graphLocalGroup Γ x ∧ g • d = beta ∧ g • beta = d ∧ g*g ∈ Q Γ x := by
    obtain ⟨g,hgd,hgb,hgg⟩ := linear_local_neighbor_exchange ht
      (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h) hd hb ex
    exact ⟨g,g.property,hgd,hgb,hgg⟩
  let f := (MulAut.conj g).toMonoidHom
  let Wb := Wd.map f
  have hgx : g • x = x :=
    (sylowGenerated_le _ hg)
  have hmapV : (V Γ d 1).map f = V Γ beta 1 := by rw [←V_translate,hgd]
  have hmapQ : (Q Γ d).map f = Q Γ beta := by rw [←Q_translate,hgd]
  have hmapZ : (Z Γ d).map f = Z Γ beta := by rw [←Z_translate,hgd]
  have hmapL : (graphLocalGroup Γ d).map f = graphLocalGroup Γ beta := by
    exact (graphLocalGroup_conjugate ht g d).symm.trans
      (congrArg (graphLocalGroup Γ) hgd)
  have hWVb : Wb ⊓ V Γ beta 1 = Z Γ beta := by
    change Wd.map f ⊓ V Γ beta 1 = Z Γ beta
    rw [←hmapV,←map_inf _ _ f (MulAut.conj g).injective,hWVd,hmapZ]
  have hspb : Wb ⊔ V Γ beta 1 = Q Γ beta := by
    change Wd.map f ⊔ V Γ beta 1 = Q Γ beta
    rw [←hmapV,←Subgroup.map_sup,hspd,hmapQ]
  have hnb : graphLocalGroup Γ beta ≤ normalizer (Wb : Set (Reduction.G₀ L S)) := by
    rw [←hmapL]
    exact (map_mono hnd).trans (le_normalizer_map f)
  have hVb : V Γ beta 1 ≤ Q Γ x := by
    have hh := map_mono (f := f) hVd
    rwa [hmapV,←Q_translate,hgx] at hh
  have hωb : Z Γ beta = omegaCenterIn (graphLocalGroup Γ beta) := by
    rw [←hmapZ,←hmapL,←NilesRankOneKernel.omegaCenterIn_map_injective
      f (MulAut.conj g).injective,hωd]
  have hZcardb : Nat.card (Z Γ beta) = Nat.card F := by
    rw [←hmapZ,card_map_of_injective (MulAut.conj g).injective,hZcardd]
  have hWbcard : Nat.card Wb = Nat.card F ^ 3 := by
    change Nat.card (Wd.map f) = Nat.card F ^ 3
    rw [card_map_of_injective (MulAut.conj g).injective,hWdcard]
  let : IsElementaryAbelian 2 Wb := IsElementaryAbelian.map f
  refine ⟨⟨g,hg⟩,hgd,hgb,hgg,hWVb,hspb,hnb,inferInstance,?_⟩
  exact reduced_adapted_pair_order h hb hd hne ex Wb Wd hnb hnd hspb hspd
    hVb hVd hWVb hWVd hωb hZcardb hWbcard hWdcard

/-- The source core layers and their Cartan collapse construct both adapted
factors and the elementary q⁴ subgroup of the actual middle core. -/
theorem reduced_core_adapted_pair
    (h : HypothesisF11 L S)
    {x beta d r : Vertex (Reduction.reducedFamily L S)}
    (hb : (graph (Reduction.reducedFamily L S)).Adj x beta)
    (hd : (graph (Reduction.reducedFamily L S)).Adj x d) (hne : beta ≠ d)
    {F K : Type*} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2]
    (ex : (graphLocalGroup (Reduction.reducedFamily L S) x ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) x)) ≃* SL(2,K))
    (ed : (graphLocalGroup (Reduction.reducedFamily L S) d ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) d)) ≃* SL(2,F))
    (hKF : Nat.card K = Nat.card F)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hres : NaturalResidualSection h d ed n)
    (hsec : CoreQuotientSection (Reduction.reducedFamily L S) r d x F ed)
    (hNspan : Q (Reduction.reducedFamily L S) r ⊓ Q (Reduction.reducedFamily L S) x =
      V (Reduction.reducedFamily L S) d 1)
    (hωd : Z (Reduction.reducedFamily L S) d =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) d))
    (hc : ⁅Q (Reduction.reducedFamily L S) d,V (Reduction.reducedFamily L S) d 1⁆ ≤
      Z (Reduction.reducedFamily L S) d)
    (hVcard : Nat.card (V (Reduction.reducedFamily L S) d 1) = Nat.card F ^ 3)
    (hZcard : Nat.card (Z (Reduction.reducedFamily L S) d) = Nat.card F) :
    let Γ := Reduction.reducedFamily L S
    let π := ed.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ d)))
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    ⁅Q Γ d,Q Γ d⁆ ≤ Z Γ d ∧
      ∃ Wd : Subgroup (Reduction.G₀ L S), Wd ≤ Q Γ d ∧
        Wd ⊓ V Γ d 1 = Z Γ d ∧ Wd ⊔ V Γ d 1 = Q Γ d ∧
        Nat.card Wd = Nat.card F ^ 3 ∧ ¬ Wd ≤ Q Γ x ∧ IsElementaryAbelian 2 Wd ∧
        Nonempty (BinaryConjugationSection (graphLocalGroup Γ d) Wd (Z Γ d)
          (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp π)) ∧
        ∃ g : graphLocalGroup Γ x,
          (g : Reduction.G₀ L S) • d = beta ∧ (g : Reduction.G₀ L S) • beta = d ∧
          (g : Reduction.G₀ L S) * g ∈ Q Γ x ∧
          let Wb := Wd.map (MulAut.conj (g : Reduction.G₀ L S)).toMonoidHom
          let M := (Wb ⊓ Q Γ x) ⊔ (Wd ⊓ Q Γ x)
          Wb ⊓ V Γ beta 1 = Z Γ beta ∧ Wb ⊔ V Γ beta 1 = Q Γ beta ∧
          graphLocalGroup Γ beta ≤ normalizer (Wb : Set (Reduction.G₀ L S)) ∧
          IsElementaryAbelian 2 Wb ∧ M ≤ Q Γ x ∧
          graphLocalGroup Γ x ≤ normalizer (M : Set (Reduction.G₀ L S)) ∧
          IsElementaryAbelian 2 M ∧ Nat.card M = Nat.card F ^ 4 ∧
          Disjoint (Wb ⊓ Q Γ x) (Wd ⊓ Q Γ x) ∧
          (¬ Wb ⊓ Q Γ x ≤ V Γ beta 1) ∧ (¬ Wd ⊓ Q Γ x ≤ V Γ d 1) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨hQQ,Wd,hWd,hWVd,hspd,hWdcard,hWdesc,hWE,⟨cW⟩⟩ :=
    reduced_core_natural_complement h hd.symm ed hn hF hres hsec hNspan hωd hc hVcard hZcard
  let := hWE
  refine ⟨hQQ,Wd,hWd,hWVd,hspd,hWdcard,hWdesc,hWE,⟨cW⟩,?_⟩
  have hZK : Nat.card (Z (Reduction.reducedFamily L S) d) = Nat.card K :=
    hZcard.trans hKF.symm
  have hWK : Nat.card Wd = Nat.card K ^ 3 := by rw [hKF]; exact hWdcard
  simpa only [hKF] using reduced_adapted_pair_from_one h hb hd hne ex Wd cW.normalized hspd
    (hNspan ▸ inf_le_right) hWVd hωd hZK hWK

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
