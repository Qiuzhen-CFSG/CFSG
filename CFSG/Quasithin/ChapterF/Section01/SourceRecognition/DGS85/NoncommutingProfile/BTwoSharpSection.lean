module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoSmallCentralSection

/-!
# Sharp proper-section bounds and unequal fields

The p.165 section estimates squeeze every proper nonzero subgroup invariant
under the full original beta stabilizer between q_beta squared and q_alpha
squared. Comparison with the intrinsic center action proves q_alpha <= q_beta,
so a proper section forces equal fields and has both order and index q_beta
squared. Thus unequal fields give a chief interval in the actual beta core.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.10), printed p.165. The remaining equal-field contradiction is separate.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- Comparison of the two field parameters with the original quotient markings. -/
theorem original_bTwo_strict_field_le
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι) :
    Nat.card (K false) ≤ Nat.card (K true) := by
  obtain ⟨k,f,fin,ch,alg,c,hactor,_,_,_,hZ,_,_,_,_,_,_,_,hk,_⟩ :=
    original_bTwo_intrinsic_core_orders h hc hne hb hβu ht htne (e true)
  have hZa := (original_bTwo_strict_core_orders h hc hne hb hβu ht htne K e hD).2.2.2.1
  have hsq : Nat.card k^2=Nat.card (K false)^2 := hZ.symm.trans hZa
  have heq : Nat.card k=Nat.card (K false) := by nlinarith
  exact heq ▸ hk

/-- A proper nonzero invariant beta section forces equality of the fields,
and both its order and its index are the square of that common field order. -/
theorem original_bTwo_nonbinary_beta_proper_section_sharp
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (N : Subgroup G) (hNQ : N < (parabolic L S 1).pCoreIn 2)
    (hZN : (Z F β).map ι < N)
    (hPN : parabolic L S 1 ≤ normalizer (N : Set G)) :
    Nat.card (K false)=Nat.card (K true) ∧
      Nat.card (N ⧸ ((Z F β).map ι).subgroupOf N)=Nat.card (K true)^2 ∧
      Nat.card ((parabolic L S 1).pCoreIn 2 ⧸ N.subgroupOf ((parabolic L S 1).pCoreIn 2))=
        Nat.card (K true)^2 := by
  have hlower := original_bTwo_nonbinary_beta_section_lower h hc hne hb hβu ht htne K e hK hD N hNQ.le hZN hPN
  have hupper := original_bTwo_nonbinary_beta_section_upper h hc hne hb hβu ht htne K e hK hD N hNQ hZN.le hPN
  have hfield := original_bTwo_strict_field_le h hc hne hb hβu ht htne K e hD
  have hsquare : Nat.card (K true)^2≤Nat.card (K false)^2 := hlower.trans hupper
  have heq : Nat.card (K false)=Nat.card (K true) := by nlinarith only [hsquare,hfield]
  have hsection : Nat.card (N ⧸ ((Z F β).map ι).subgroupOf N)=Nat.card (K true)^2 :=
    le_antisymm (by rw [←heq]; exact hupper) hlower
  refine ⟨heq,hsection,?_⟩
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let Z₁ := (Z F β).map ι
  have hfact := relIndex_mul_relIndex Z₁ N Q₁ hZN.le hNQ.le
  have htotal := (original_bTwo_strict_beta_total_section h hc hne hb hβu ht htne K e hD).2
  change Nat.card (Q₁ ⧸ Z₁.subgroupOf Q₁)=Nat.card (K false)^2*Nat.card (K true)^2 at htotal
  have hsectioni : Z₁.relIndex N=Nat.card (K true)^2 := by
    exact hsection
  have hquot : Nat.card (K true)^2 * N.relIndex Q₁ = Nat.card (K true)^2*Nat.card (K true)^2 := by
    calc
      Nat.card (K true)^2 * N.relIndex Q₁ = Z₁.relIndex N * N.relIndex Q₁ := by
        rw [hsectioni]
      _ = Z₁.relIndex Q₁ := hfact
      _ = Nat.card (K true)^2*Nat.card (K true)^2 := by
        simpa only [relIndex,index_eq_card,heq] using htotal
  have hresult := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.card_pos : 0<Nat.card (K true))) hquot
  simpa only [relIndex,index_eq_card] using hresult

/-- The unequal-field case of p.165: the literal beta core has no proper
nonzero section invariant under the full original beta stabilizer. -/
theorem original_bTwo_unequal_beta_interval
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆≠⊥)
    (hb : b F=2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t≠β)
    (K : Bool → Type*) [∀ i, Field (K i)] [∀ i, Finite (K i)] [∀ i, CharP (K i) 2]
    (e : ∀ i, (family L i⧸pCore 2 (family L i))≃*PSL(2,K i))
    (hK : 2<Nat.card (K true))
    (hD : (parabolic L S 1).pCoreIn 2⊓(Q F t).map ι≠(Z F α).map ι)
    (hfields : Nat.card (K false)≠Nat.card (K true))
    (N : Subgroup G) (hNQ : N≤(parabolic L S 1).pCoreIn 2)
    (hZN : (Z F β).map ι≤N)
    (hPN : parabolic L S 1≤normalizer (N:Set G)) :
    N=(Z F β).map ι ∨ N=(parabolic L S 1).pCoreIn 2 := by
  by_cases he : N=(Z F β).map ι
  · exact Or.inl he
  by_cases heQ : N=(parabolic L S 1).pCoreIn 2
  · exact Or.inr heQ
  exact False.elim (hfields (original_bTwo_nonbinary_beta_proper_section_sharp h hc hne hb
    hβu ht htne K e hK hD N (lt_of_le_of_ne hNQ heQ)
    (lt_of_le_of_ne hZN (Ne.symm he)) hPN).1)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
