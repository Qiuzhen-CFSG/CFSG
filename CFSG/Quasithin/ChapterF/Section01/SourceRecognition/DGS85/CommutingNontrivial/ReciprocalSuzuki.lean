module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.IndexEstimates
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiElementBounds

/-!
# Suzuki field-square bounds on the original moving center

Every nonzero elementary subgroup of an actual Suzuki quotient contains an
involution. The individual involution bound (5.10)(b) gives a fixed-space
index at least q²; fixed-space antitonicity gives the same bound for the
whole subgroup. This includes Sz(2). The existing residual-fixed-space
argument supplies whole-action faithfulness on the original center.

Identity vector coordinates identify the fixed-space index with the literal
centralizer index in the source group. The actor may be any elementary
subgroup of the local group escaping its core. `ReciprocalIntersection`
uses this for Z_alpha intersect Q_alpha', and its reduced-source application
excludes the corresponding second subcase of the proof of 8.2.

Source: DGS, *Groups and Graphs* (1985), (5.10)(b), pp.110--112,
and (8.2)(**), pp.134--135. The remaining factor-module case of 8.2,
unitary comparisons, and 8.3--8.7 remain separate obligations.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem suzuki_elementary_fixed_bound {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] (m : ℕ)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) W) (hf : Function.Injective ρ)
    (A : Subgroup (SuzukiMatrixGroup m)) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    (2^(2*m+1))^2 ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have ha2 : orderOf a = 2 :=
    orderOf_eq_prime_iff.mpr
      ⟨elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha,ha1⟩
  have hlo := suzuki_element_fixed_index m ρ hf a ha2
  have hle : Nat.card (W ⧸ fixedSpace ρ (zpowers a)) ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
    let : Finite (W ⧸ fixedSpace ρ A) := Finite.of_surjective _ (fixedSpace ρ A).mkQ_surjective
    exact Nat.card_le_card_of_surjective _
      (Submodule.factor_surjective (fixedSpace_antitone ρ (zpowers_le.mpr ha)))
  simpa only [←pow_mul, Nat.mul_comm 2] using hlo.trans hle

/-- Every elementary actor escaping the core at the moving Suzuki vertex
moves at least the square of the defining field, including Sz(2). -/
theorem source_moving_suzuki_field_square_bound (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (m : ℕ) (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* SuzukiMatrixGroup m)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hAL : A ≤ d.localGroup w.val)
    (hAQ : ¬ A ≤ Q (family P) w.val) :
    (2^(2*m+1))^2 ≤ (centralizer (A : Set G)).relIndex (Z (family P) w.val) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let := source_center_nontrivial h w.val
  let F := family P
  let L := d.localGroup w.val
  let Z₀ := Z F w.val
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : Finite L := Finite.of_injective (inclusion (d.local_le w.val)) (inclusion_injective _)
  let : Finite Z₀ := Finite.of_injective (inclusion (Z_le_stabilizer F w.val)) (inclusion_injective _)
  obtain ⟨ρ,S,hact,_,_,_,_,hres,_⟩ := source_moving_center_module h d hc hab hd hb hcomm w hm e
  have hf := suzuki_quotient_action_faithful m e ρ hres
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hne : (A.subgroupOf L).map q ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [local_quotient_kernel F d w.val e] at hk
    exact hAQ (fun a ha => hk (show (⟨a,hAL ha⟩ : L) ∈ A.subgroupOf L from ha))
  have hbound := suzuki_elementary_fixed_bound m ρ hf _ hne
  have hZL : Z₀ ≤ L := pGroup_le_localGroup F d w.val _
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer F w.val)
  have hi := center_action_fixed_index L Z₀ A hZL
    ((d.local_le w.val).trans (stabilizer_normalizes_Z F w.val)) hAL q ρ hact
  rwa [hi] at hbound

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
