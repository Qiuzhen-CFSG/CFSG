module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.QuotientFaithfulness
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.MovingActor

/-!
# Unitary square bounds on the original moving center

The graph's elementary neighboring span makes its actual quotient actor
elementary before any representation-faithfulness argument. At unitary
field order at least four, the three-root minimum-degree bound therefore
applies to the original conjugation action with zero global fixed space.
This retains the special unitary scalar center and requires no faithfulness
of the full special unitary quotient. The projective case additionally
has a faithful action by simplicity. The bound uses the literal relative
index of the moving actor against the neighboring core.

Source: DGS, *Groups and Graphs* (1985), 8.2--8.7, pp.134--140,
and 5.12, pp.113--115. The field-two unitary cases remain separate; this
module does not remove them from the source catalogue. The reduced consumer
is `ReducedModuleEstimates`.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

private theorem action_nontrivial_of_fixed_eq_bot {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]
    (ρ : Representation (ZMod 2) D W) (hf : fixedSpace ρ ⊤ = ⊥) :
    ∃ g, ρ g ≠ 1 := by
  by_contra! ht
  have he : fixedSpace ρ ⊤ = ⊤ := by
    apply top_unique
    intro v _ g
    change ρ g v = v
    rw [ht]
    rfl
  exact top_ne_bot (he.symm.trans hf)

/-- The special unitary moving-neighbor estimate, retaining the same
quotient map and original source vectors. -/
theorem source_moving_special_unitary_square_bound
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* (J.specialSubgroup)) :
    letI := CommutingOneProfile.source_center_elementary h w.val
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup w.val)))
    let Aq := (A.subgroupOf (d.localGroup w.val)).map q
    ∃ (ρ : Representation (ZMod 2) (J.specialSubgroup) (Additive (Z F w.val)))
      (S : Sylow 2 (J.specialSubgroup)),
      (∀ (l : d.localGroup w.val) (z : Additive (Z F w.val)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) ∧
      Aq ≤ S ∧ Aq ≠ ⊥ ∧ IsElementaryAbelian 2 Aq ∧ IsQuadratic ρ Aq ∧
      GeneratedByFixedSpace ρ S ∧ fixedSpace ρ (pResidual 2 (J.specialSubgroup)) = ⊥ ∧
      Nat.card Aq = (Q F w.val).relIndex A ∧
      (Q F w.val).relIndex A ^ 2 ≤ Nat.card (Additive (Z F w.val) ⧸ fixedSpace ρ Aq) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let := source_center_nontrivial h w.val
  let : Finite (Z (family P) w.val) := Finite.of_injective
    (inclusion (Z_le_stabilizer (family P) w.val)) (inclusion_injective _)
  dsimp only
  obtain ⟨ρ, S, hact, hAS, hne, hq, hgen, hfix, hcard⟩ :=
    source_moving_center_module h d hc hab hd hb hcomm w hm e
  obtain ⟨_, hb3, _⟩ := source_critical_geometry h d hc hab hd hb hcomm
  let : IsElementaryAbelian 2 (V (family P) beta 1) :=
    CommutingThreeProfile.V_elementary (family P) h.generate
      (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) beta
  let A := V (family P) beta 1 ⊓ Q (family P) a'
  let L := d.localGroup w.val
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (A.subgroupOf L) :=
    IsElementaryAbelian.subgroupOf (source_moving_actor h d hc hab hd hb hcomm w hm).2.1
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hglobal : fixedSpace ρ ⊤ = ⊥ := bot_unique ((fixedSpace_antitone ρ le_top).trans hfix.le)
  have hnt := action_nontrivial_of_fixed_eq_bot ρ hglobal
  refine ⟨ρ, S, hact, hAS, hne, inferInstance, hq, hgen, hfix, hcard, ?_⟩
  simpa only [q, A, L, hcard] using su3_elementary_square_bound J hn hK hconj
    ρ hnt hglobal ((A.subgroupOf L).map q)

/-- The projective unitary moving-neighbor estimate, retaining the same
quotient map and original source vectors. -/
theorem source_moving_projective_unitary_square_bound
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    {K : Type*} [Field K] [Finite K] (J : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* (ProjectiveSpecialUnitaryMatrixGroup J)) :
    letI := CommutingOneProfile.source_center_elementary h w.val
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup w.val)))
    let Aq := (A.subgroupOf (d.localGroup w.val)).map q
    ∃ (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) (Additive (Z F w.val)))
      (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)),
      (∀ (l : d.localGroup w.val) (z : Additive (Z F w.val)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) ∧
      Aq ≤ S ∧ Aq ≠ ⊥ ∧ IsElementaryAbelian 2 Aq ∧ IsQuadratic ρ Aq ∧
      Function.Injective ρ ∧
      GeneratedByFixedSpace ρ S ∧ fixedSpace ρ (pResidual 2 (ProjectiveSpecialUnitaryMatrixGroup J)) = ⊥ ∧
      Nat.card Aq = (Q F w.val).relIndex A ∧
      (Q F w.val).relIndex A ^ 2 ≤ Nat.card (Additive (Z F w.val) ⧸ fixedSpace ρ Aq) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let := source_center_nontrivial h w.val
  let : Finite (Z (family P) w.val) := Finite.of_injective
    (inclusion (Z_le_stabilizer (family P) w.val)) (inclusion_injective _)
  dsimp only
  obtain ⟨ρ, S, hact, hAS, hne, hq, hgen, hfix, hcard⟩ :=
    source_moving_center_module h d hc hab hd hb hcomm w hm e
  obtain ⟨_, hb3, _⟩ := source_critical_geometry h d hc hab hd hb hcomm
  let : IsElementaryAbelian 2 (V (family P) beta 1) :=
    CommutingThreeProfile.V_elementary (family P) h.generate
      (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) beta
  let A := V (family P) beta 1 ⊓ Q (family P) a'
  let L := d.localGroup w.val
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (A.subgroupOf L) :=
    IsElementaryAbelian.subgroupOf (source_moving_actor h d hc hab hd hb hcomm w hm).2.1
  let : IsElementaryAbelian 2 ((A.subgroupOf L).map q) := IsElementaryAbelian.map q
  have hglobal : fixedSpace ρ ⊤ = ⊥ := bot_unique ((fixedSpace_antitone ρ le_top).trans hfix.le)
  have hnt := action_nontrivial_of_fixed_eq_bot ρ hglobal
  have hf := projective_unitary_action_faithful J hn hK hconj ρ hfix
  refine ⟨ρ, S, hact, hAS, hne, inferInstance, hq, hf, hgen, hfix, hcard, ?_⟩
  simpa only [q, A, L, hcard] using psu3_elementary_square_bound J hn hK hconj
    ρ hnt hglobal ((A.subgroupOf L).map q)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
