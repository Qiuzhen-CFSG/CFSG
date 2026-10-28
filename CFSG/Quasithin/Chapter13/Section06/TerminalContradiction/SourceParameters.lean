module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.WeakClosure
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.Residual
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.FiveModule
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.RelativeComponents.DirectFive

/-!
# Source assembly of 13.6.25–26

The actual A₅ quotient supplies A₅ in the five-coordinate actor. The proved
module calculation therefore gives a(M̄_V,V)=1 for the genuine automizer.
Together with the published 13.6.24 and earlier 13.6.3, the generator proof
gives r=3, Wᵢ ≤ C_T(V)=O₂(LT), Wᵢ ◁ LT for i=0,1, and w>1. Its E.3.35
application gives n(H)>1 for every H in H(T,M) and puts every solvable
member of H(T) inside M.

For each original H_z member, the direct A₅ argument excludes every relative
C-component from M. The residual argument applies the just-proved solvable
containment to XT, where X=O^{p′}(O_{2,p}(H)). The universal 13.3.8(2)
implication then gives X=1 and O_{2,p}(H)=Q_H. Here O_{2,p} is the embedded
preimage of O_p(H/O₂(H)) under H's original quotient map.

Only genuine earlier source inputs remain: `EarlierA5Setup`, constructed
by `qt-13-06`; `EarlierA38Three`, from `qt-a03-sqtk-structure`;
`EarlierE335`, from `qt-e-03`; and `Earlier1338Two`, from
`qt-13-03-preliminaries`. Their final discharge belongs to the full-source
assembly. No 13.6.25 or 13.6.26 conclusion is an input here. The legacy
`Parameters` interfaces and definitions are preserved and are not used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemmas 13.6.25–26, printed p.934. `SourceParameters.TerminalConsumer`
connects these results to the actual 13.6.27 constructions.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters

open Subgroup
open _root_.CFSG.Quasithin.ChapterE

universe u
variable {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]

/-- The numerical premise of the generator proof is computed on the actual
faithful automizer, using the source quotient action to supply its A₅ image. -/
theorem EarlierA5Setup.localA_eq_one (s : EarlierA5Setup T L V M MV) :
    localA V = 1 :=
  s.coordinates.localA_eq_one s.alternating_le_actor

/-- All four assertions of source 13.6.25, with the module calculation
discharged. The stronger core containment is retained for later uses. -/
theorem source_13_6_25 (s : EarlierA5Setup T L V M MV)
    (he : EarlierE335 (G := G)) :
    (∀ i : ℕ, i = 0 ∨ i = 1 →
      indexedWeakClosure V (T : Subgroup G) i ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter3.NormalIn (indexedWeakClosure V (T : Subgroup G) i) (L ⊔ (T : Subgroup G))) ∧
    (∀ H ∈ Chapter1.HOutside G (T : Set G) (M : Set G), 1 < generationParameter H) ∧
    (∀ H ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable H → H ≤ M) ∧
    globalR V = 3 ∧ 1 < globalW V (T : Subgroup G) :=
  source_13_6_25_from_earlier s s.localA_eq_one he

/-- Both assertions of source 13.6.26 on its full H_z family. Components
are relative to H; the core equality uses the quotient-preimage convention. -/
theorem source_13_6_26 (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA38 : EarlierA38Three.{u}) (s : EarlierA5Setup T L V M MV)
    (he : EarlierE335 (G := G)) (h1338 : Earlier1338Two T)
    (L₁ G₁ : Subgroup G) :
    ∀ H ∈ Chapter13.Section08.Source.Hz L₁ (T : Subgroup G) G₁ M,
      (∀ K ∈ Chapter1.cComponentsIn H, ¬ K ≤ M) ∧
      (∀ p : ℕ, p.Prime → 3 < p → O2p H p = Chapter13.Section08.Source.QH H) := by
  intro H hH
  refine ⟨source_13_6_26_1_of_A5_setup hG hA38 T L V M MV L₁ G₁ s hH, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  exact source_13_6_26_2_from_generators s s.localA_eq_one he h1338 L₁ G₁ hH p hlarge

/-- The complete 13.6.25(1–4)/13.6.26(1–2) family for terminal assembly,
conditional only on the genuine earlier source setup and implications. -/
theorem source_13_6_25_26 (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA38 : EarlierA38Three.{u}) (s : EarlierA5Setup T L V M MV)
    (he : EarlierE335 (G := G)) (h1338 : Earlier1338Two T)
    (L₁ G₁ : Subgroup G) :
    (∀ i : ℕ, i = 0 ∨ i = 1 →
      indexedWeakClosure V (T : Subgroup G) i ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Chapter3.NormalIn (indexedWeakClosure V (T : Subgroup G) i) (L ⊔ (T : Subgroup G))) ∧
    (∀ H ∈ Chapter1.HOutside G (T : Set G) (M : Set G), 1 < generationParameter H) ∧
    (∀ H ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable H → H ≤ M) ∧
    (globalR V = 3 ∧ 1 < globalW V (T : Subgroup G)) ∧
    (∀ H ∈ Chapter13.Section08.Source.Hz L₁ (T : Subgroup G) G₁ M,
      (∀ K ∈ Chapter1.cComponentsIn H, ¬ K ≤ M) ∧
      (∀ p : ℕ, p.Prime → 3 < p → O2p H p = Chapter13.Section08.Source.QH H)) := by
  obtain ⟨hW, hn, hs, hrw⟩ := source_13_6_25 s he
  exact ⟨hW, hn, hs, hrw, source_13_6_26 hG hA38 s he h1338 L₁ G₁⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
