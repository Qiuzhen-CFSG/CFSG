module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedSolvability
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoRegular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaIrreducible
public import Theory.GroupAction.NormalizerFrattiniInterval

/-!
# Original beta core control in the A5 distance-two source

The strict DGS source identifies the full original beta core's Frattini
subgroup with its center section and proves that the interval above this
section is chief under the full original parabolic. This gives Frattini
irreducibility on the literal parabolic core. The A5 residual argument
then puts the whole core in the original factor.

For an A5/A5 pair, the source constructs the field-four markings and the
strict core intersection internally. No reduced catalogue, model recognition,
or irreducibility premise is assumed by the A5 branch theorem. The alpha
endpoint and the one-Borel join comparison remain separate obligations.

Source: DGS, Groups and Graphs (1985), (10.10)(d), pp.164--165;
Aschbacher--Smith F.1.12, pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

omit [Finite G] in
/-- The actual nonbinary beta chief interval is the intrinsic Frattini
quotient of the full original parabolic core. -/
theorem HypothesisF11.bTwo_beta_frattini_irreducible
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)]
    [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i))
    (hK : 2 < Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map (G₀ L S).subtype ≠
      (Z F α).map (G₀ L S).subtype) :
    IsNormalizerFrattiniIrreducible (pCore 2 (parabolic L S 1)) := by
  let P := parabolic L S 1
  let Q₁ := P.pCoreIn 2
  let Z₁ := (Z F β).map (G₀ L S).subtype
  have hPhi : (frattini Q₁).map Q₁.subtype = Z₁ :=
    (NoncommutingProfile.Reduction.original_bTwo_strict_core_orders
      h hc hne hb hβu ht htne K e hD).2.2.2.2.2.2.2.2.2.2.1
  have hPQ : P ≤ normalizer (Q₁ : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hirr := normalizerFrattiniIrreducible_subgroupOf_of_interval Q₁ P
    (pCoreIn_le 2 P) hPQ (by
      intro N hZN hNQ hPN
      rw [hPhi] at hZN
      rcases NoncommutingProfile.Reduction.original_bTwo_nonbinary_beta_interval
          h hc hne hb hβu ht htne K e hK hD N hNQ hZN hPN with hz | hq
      · exact Or.inl (hz.trans hPhi.symm)
      · exact Or.inr hq)
  have hQ : Q₁.subgroupOf P = pCore 2 P :=
    comap_map_eq_self_of_injective P.subtype_injective _
  rw [hQ] at hirr
  exact hirr

/-- The A5/A5 distance-two source itself supplies strictness and both
field markings, and therefore identifies the full original beta core. -/
theorem HypothesisF11.a5_bTwo_beta_parabolic_core_eq
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {u : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u) :
    twoCore (parabolic L S 1) = twoCore (L 1) := by
  have hval : 3 ≤ Nat.card ((graph F).neighborSet α) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) false
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet α)
    (by rw [←Nat.card_coe_set_eq]; omega) β
  obtain ⟨k,f,fin,ch,alg,c,hactor,hk,n,hn,hm,hpow,hext,hD,_⟩ :=
    DGS85.Assembly.BTwoSource.original_core_layers h hc hne hb hβu ht htne
      (h.a5_parabolic_not_solvable 0 (a 0).some)
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  let K : Bool → Type := fun _ => GaloisField 2 2
  let e (i : Bool) : (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i) :=
    by cases i
       · exact (a 0).some.trans e₄.symm
       · exact (a 1).some.trans e₄.symm
  exact h.a5_parabolic_core_eq_of_frattini_irreducible 1 (a 1).some
    (h.bTwo_beta_frattini_irreducible hc hne hb hβu ht htne K e (by
      change 2 < Nat.card (GaloisField 2 2)
      rw [hfour]
      decide) hD)

end CFSG.Quasithin.ChapterF.Source
