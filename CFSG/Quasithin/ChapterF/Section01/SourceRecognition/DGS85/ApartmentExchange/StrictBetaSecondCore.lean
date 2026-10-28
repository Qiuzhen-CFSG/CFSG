module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictPathSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaIrreducible

/-!
# The strict beta radius-two core

The original nonbinary beta chief interval forces its neighboring-core
intersection to equal the literal beta center. The intersection is normalized
by the full original beta parabolic and lies in the opposite core, so the
alternative that it equals the beta core contradicts the adjacent-core
obstruction. The source kernel-Sylow theorem identifies this intersection
with the two-core of the full second ball kernel; the full kernel is retained.

Source: DGS, Groups and Graphs (1985), (10.10)(d), pp.164--165, and the
radius-two calculation used in (14.9), pp.215--216.
-/

public noncomputable section
open Subgroup
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile CommutingOneProfile
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The original strict inputs identify the whole beta second-kernel
two-core, without a chosen section or a supplied kernel decomposition. -/
theorem strict_source_beta_second_core
    (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
    (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) u⁆ ≠ ⊥)
    (hb : b (reducedFamily L S)=2)
    (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n)) :
    neighborCoreIntersection F β=Z F β ∧
      (ballKernel F β 2).pCoreIn 2=Z F β ∧
      ((ballKernel F β 2).pCoreIn 2).map ι=(Z F β).map ι := by
  have hab : (graph F).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hval : 3≤Nat.card ((graph F).neighborSet α) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) false
  obtain ⟨t,ht,htne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet α)
    (by rw [←Nat.card_coe_set_eq]; omega) β
  obtain ⟨k,f,fin,ch,alg,c,hactor,hk,m,hm,hright,hpow,hext,hD,_⟩ :=
    original_core_layers h hc hne hb hβu ht htne hns
  obtain ⟨k₀,f₀,fin₀,h₀,⟨e₀⟩⟩ := hlinear
  obtain ⟨k₁,f₁,fin₁,h₁,⟨e₁⟩⟩ := hright
  let _ := f₀
  let _ := fin₀
  let _ := f₁
  let _ := fin₁
  let _ : Fintype k₀ := Fintype.ofFinite k₀
  let _ : Fintype k₁ := Fintype.ofFinite k₁
  let _ : CharP k₀ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₀)
  let _ : CharP k₁ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₁)
  let K : Bool → Type := fun i => if i then k₁ else k₀
  let _ : ∀ i, Field (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, Finite (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, CharP (K i) 2 := fun i => by cases i <;> assumption
  let e : ∀ i, (family L i ⧸ pCore 2 (family L i)) ≃* PSL(2,K i) := by
    intro i
    cases i
    · exact e₀
    · exact e₁
  have hK : 2<Nat.card (K true) := by
    change 2<Nat.card k₁
    rw [h₁]
    have he : 2^2≤2^m := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  let I := neighborCoreIntersection F β
  have hIQ : I≤Q F β := source_neighborCoreIntersection_le_core
    (reduced_triple h) hab
  have hZI : Z F β≤I := by
    apply le_iInf
    intro z
    exact graph_Z_le_Q_of_short (reduced_triple h) (reduced_kernel_sylow h) (by
      change (graph F).dist β z < b F
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr z.property,hb]
      decide)
  have hI : I=Z F β := by
    have hQb : (Q F β).map ι=(parabolic L S 1).pCoreIn 2 := reduced_base_Q_map h true
    have hIQ₀ : I.map ι≤(parabolic L S 1).pCoreIn 2 := by
      rw [←hQb]
      exact map_mono hIQ
    rcases NoncommutingProfile.Reduction.original_bTwo_nonbinary_beta_interval
      h hc hne hb hβu ht htne K e hK hD (I.map ι) hIQ₀ (map_mono hZI)
      (NoncommutingProfile.Reduction.original_second_core_normalized h) with he | he
    · exact map_injective (G₀ L S).subtype_injective he
    · have hIQeq : I=Q F β := map_injective (G₀ L S).subtype_injective
        (he.trans (reduced_base_Q_map h true).symm)
      have hba : Q F β≤Q F α := hIQeq ▸ neighborCoreIntersection_le F hab
      exact False.elim (reduced_graph_core_obstruction h β α hab.symm (by
        rw [inf_eq_right.mpr hba]
        exact (stabilizer F β).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))
  have hsecond : (ballKernel F β 2).pCoreIn 2=Z F β :=
    (reduced_neighborCoreIntersection_eq_second_core h hab).symm.trans hI
  exact ⟨hI,hsecond,congrArg (Subgroup.map ι) hsecond⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
