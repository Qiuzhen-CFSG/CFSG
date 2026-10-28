module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoShifted
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoActionSource

/-!
# Original markings for the b=2 shifted-pair argument

The constructed 10.3 pair is applied on the genuine reduced F1.11 graph.
Its noncommutation also survives the actual inclusion into the original
completion. The existing 10.6 quotient calculation now requires only the
first critical pair: the second pair and its noncommutation are proved.

The earlier 6.5 obstruction and 7.1 Sylow products remain source inputs.
The literal D identities and action construction still belong to the
Chapter 10 proof; these results do not assert 10.6 or 10.9/10.10 without
those remaining inputs.
Source: DGS, *Groups and Graphs* (1985), 10.3 and 10.6, pp.154--158.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
open DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- Literal source 10.3 on the reduced F1.11 graph. The conclusion also
records noncommutation after the actual reduced-to-original inclusion. -/
theorem original_bTwo_shifted_pair_of_noncentral
    (h : HypothesisF11 L S) (hb : b F = 2) {u : Vertex F}
    (hu : (graph F).Adj u β) (hc : IsCriticalPair F α u)
    (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hnc : ¬ Z F β ≤ centerIn (graphLocalGroup F β))
    (hs : Stellmacher.IsSylowSubgroupIn (Z F α ⊔ Q F u) (stabilizer F u))
    (hnot : ∀ t, (graph F).Adj t α →
      ¬ stabilizer F α ≤ normalizer ((Q F t ⊓ Q F α : Subgroup (G₀ L S)) : Set (G₀ L S))) :
    ∃ t, (graph F).Adj t α ∧ t ≠ β ∧
      Z F u ⊔ (stabilizer F α ⊓ stabilizer F t) = stabilizer F α ∧
      ¬ Z F t ≤ stabilizer F u ∧ IsCriticalPair F t β ∧
      IsCriticalPair F β t ∧ ⁅Z F β,Z F t⁆ ≠ ⊥ ∧
      ⁅(Z F β).map (G₀ L S).subtype,(Z F t).map (G₀ L S).subtype⁆ ≠ ⊥ := by
  have hadj : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base F false true⟩
  obtain ⟨t,ht,hneT,hgen,hesc,hct,hcr,hn⟩ := bTwo_shifted_pair_of_noncentral
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    hb hadj hu.symm hc hne hnc hs hnot
  refine ⟨t,ht,hneT,hgen,hesc,hct,hcr,hn,?_⟩
  rw [←Subgroup.map_commutator]
  exact fun he => hn ((map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective).mp he)

/-- Source application to the existing 10.6 quotient calculation. The
second critical-pair and noncommutation premises are proved by 10.3.
The literal D identities remain Chapter 10 obligations, and the actual
quotient actions and line indices remain explicit earlier-source inputs. -/
theorem original_bTwo_noncentral_exclusion_of_shifted_D
    (h : HypothesisF11 L S) (hb : b F = 2) {t u : Vertex F}
    (ht : (graph F).Adj t α) (hu : (graph F).Adj u β)
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hnc : ¬ Z F β ≤ centerIn (graphLocalGroup F β))
    (hgen : Z F u ⊔ (stabilizer F α ⊓ stabilizer F t) = stabilizer F α)
    (hnot : ¬ stabilizer F α ≤ normalizer ((Q F t ⊓ Q F α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    {k₀ k₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
    [Field k₁] [Finite k₁] [CharP k₁ 2]
    (c₀ : BTwoActionData F u β α t k₀)
    (c₁ : BTwoActionData F t α β u k₁)
    (hD₀ : D F β t = Z F α) (hD₁ : D F α u = Z F β)
    (hs₀ : Stellmacher.IsSylowSubgroupIn (Z F t ⊔ Q F β) (stabilizer F β) ∧
      Stellmacher.IsSylowSubgroupIn (Z F β ⊔ Q F t) (stabilizer F t))
    (hs₁ : Stellmacher.IsSylowSubgroupIn (Z F u ⊔ Q F α) (stabilizer F α) ∧
      Stellmacher.IsSylowSubgroupIn (Z F α ⊔ Q F u) (stabilizer F u))
    (hline₀ : ((Q F u).map (G₀ L S).subtype).relIndex
      ((Z F α).map (G₀ L S).subtype) = Nat.card k₀)
    (hline₁ : ((Q F t).map (G₀ L S).subtype).relIndex
      ((Z F β).map (G₀ L S).subtype) = Nat.card k₁) : False := by
  have hadj : (graph F).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base F false true⟩
  have htype : t.type = (β).type := by
    have h₀ := ht.1
    have h₁ := hadj.1
    cases ha : (α).type <;> cases ht' : t.type <;> cases hm : (β).type <;> simp_all
  have hCSt := bTwo_centralizer_sylow_of_noncentral (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hnc htype
  have hCSβ := bTwo_centralizer_sylow_of_noncentral (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hnc (t := β) rfl
  obtain ⟨_,_,hc₀,hne₀⟩ := bTwo_shifted_critical_pair (reduced_triple h)
    (reduced_kernel_sylow h) hb ht hadj hu.symm hc hs₁.2 hgen hCSt hCSβ hnot
  exact original_bTwo_noncentral_exclusion_of_D_identities h hb ht hu
    hc₀ hc hne₀ hne c₀ c₁ hD₀ hD₁ hs₀ hs₁ hline₀ hline₁

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
