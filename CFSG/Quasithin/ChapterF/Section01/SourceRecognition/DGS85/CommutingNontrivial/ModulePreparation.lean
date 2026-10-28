module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReducedControl
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FixedGeneration
public import Theory.GroupTheory.PResidual.CenterlessSylow
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.RankOne.QuadraticRecognition.SourceTheorem

/-!
# The original critical center as a binary quotient module

Conjugation on the actual source center descends through the intrinsic
O₂ of its local actor. The representation keeps the original quotient map
and every representative's conjugation formula. The previously proved
triviality of the starting local center kills the O²-fixed subspace by
the centerless Sylow-centralizer theorem. The source Sylow-center span
supplies generation by the same Sylow fixed space, using the proved
normal-local generation theorem without replacing the original vectors.

The reduced F1.11 application constructs the action, its marked Sylow,
and both supplementary premises of corrected 5.12. A second literal
application gives the quadratic index bound and conditional natural
recognition, retaining actual rank-one model isomorphisms and equivariant
natural coordinates. Faithfulness, quadratic actor placement and the
strict comparison remain Chapter 8 obligations. This does not prove the
critical-distance bound or the equal-field conclusion.

Source: DGS, *Groups and Graphs* (1985), 8.1(b), 8.2--8.7, pp.133--140;
corrected 5.12, pp.113--114, with Sylow-fixed generation retained.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

private theorem residual_fixed_eq_bot_of_center_eq_bot
    {D : Type*} [Group D] (L Z : Subgroup G) [Finite L] [IsElementaryAbelian 2 Z]
    (hZL : Z ≤ L) (hz : center L = ⊥) (q : L →* D)
    (ρ : Representation (ZMod 2) D (Additive Z))
    (hact : ∀ (l : L) (z : Additive Z),
      ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) :
    fixedSpace ρ (pResidual 2 D) = ⊥ := by
  have hp : IsPGroup 2 (Z.subgroupOf L) := (IsElementaryAbelian.isPGroup 2 Z).comap_subtype
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  have hbot := sylow_inf_centralizer_pResidual_eq_bot_of_center_eq_bot T hz
  apply bot_unique
  intro z hzfix
  have hc : (⟨z.toMul, hZL z.toMul.property⟩ : L) ∈
      centralizer (pResidual 2 L : Set L) := by
    intro l hl
    apply Subtype.ext
    have hh := congrArg (fun w : Additive Z => (w.toMul : G))
      (hzfix ⟨q l, map_pResidual_le 2 q (mem_map_of_mem q hl)⟩)
    change ((ρ (q l) z).toMul : G) = z.toMul at hh
    rw [hact] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hm : (⟨z.toMul, hZL z.toMul.property⟩ : L) ∈ (T : Subgroup L) ⊓
      centralizer (pResidual 2 L : Set L) := ⟨hT z.toMul.property, hc⟩
  have he := congrArg L.subtype (mem_bot.mp (hbot ▸ hm))
  change z = 0
  exact Additive.toMul.injective (Subtype.ext he)

/-- Construct the original center action through the actual intrinsic two-core quotient.
This does not yet assert that the resulting action is faithful. -/
theorem source_exists_center_quotient_action
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    {D : Type*} [Group D] (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D) :
    letI := CommutingOneProfile.source_center_elementary h v
    ∃ ρ : Representation (ZMod 2) D (Additive (Z (family P) v)),
      ∀ (l : d.localGroup v) (z : Additive (Z (family P) v)),
        ((ρ (e (QuotientGroup.mk' (pCore 2 (d.localGroup v)) l)) z).toMul : G) =
          (l : G) * z.toMul * (l : G)⁻¹ := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h v
  have hn : stabilizer (family P) v ≤ normalizer (d.localGroup v : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (d.localGroup v).map (MulAut.conj g).toMonoidHom = _
    rw [← d.conjugate]
    exact congrArg d.localGroup hg
  have hcore : (d.localGroup v).pCoreIn 2 ≤ Q (family P) v :=
    pCoreIn_mono_of_normalizes (d.local_le v) hn
  have hnZ := (d.local_le v).trans (stabilizer_normalizes_Z (family P) v)
  let α := (Z (family P) v).normalizerMonoidHom.comp (inclusion hnZ)
  have hker : pCore 2 (d.localGroup v) ≤ α.ker := by
    intro l hl
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    have hc : (l : G) ∈ centralizer (Z (family P) v : Set G) :=
      (le_centralizer_iff.mp (Z_centralizes_Q (family P) v (source_Z_Q_U h v).1))
        (hcore (mem_map_of_mem (d.localGroup v).subtype hl))
    change (l : G) * (z : G) * (l : G)⁻¹ = z
    rw [← mem_centralizer_iff.mp hc z z.property, mul_assoc, mul_inv_cancel, mul_one]
  let β := QuotientGroup.lift (pCore 2 (d.localGroup v)) α hker
  let γ := β.comp e.symm.toMonoidHom
  let : MulDistribMulAction D (Z (family P) v) := MulDistribMulAction.compHom _ γ
  refine ⟨Representation.ofElementaryAbelianAction, ?_⟩
  intro l z
  change ((β (e.symm (e (QuotientGroup.mk' (pCore 2 (d.localGroup v)) l)))) z.toMul : G) = _
  rw [e.symm_apply_apply]
  rfl

/-- Both supplementary premises of corrected 5.12 hold for any centerless
local actor on its literal source center. This applies also at the moving
neighbor in 8.1 and retains the original quotient and Sylow image. -/
theorem source_center_module_prepared_of_center_eq_bot
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    (a : Vertex (family P)) (hz : center (d.localGroup a) = ⊥)
    {D : Type*} [Group D]
    (T : Sylow 2 (stabilizer (family P) a))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D) :
    letI := CommutingOneProfile.source_center_elementary h a
    let K := (d.localGroup a).subgroupOf (stabilizer (family P) a)
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup a)))
    let qK := q.comp (subgroupOfEquivOfLe (d.local_le a)).toMonoidHom
    ∀ (ρ : Representation (ZMod 2) D (Additive (Z (family P) a))),
      (∀ (l : d.localGroup a) (z : Additive (Z (family P) a)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      ∃ S : Sylow 2 D,
        (S : Subgroup D) = ((T : Subgroup (stabilizer (family P) a)).subgroupOf K).map qK ∧
        GeneratedByFixedSpace ρ S ∧ fixedSpace ρ (pResidual 2 D) = ⊥ := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h a
  let : Finite (d.localGroup a) := Finite.of_injective (inclusion (d.local_le a))
    (inclusion_injective _)
  let K := (d.localGroup a).subgroupOf (stabilizer (family P) a)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup a)))
  let eK := subgroupOfEquivOfLe (d.local_le a)
  let qK := q.comp eK.toMonoidHom
  dsimp only
  intro ρ hact
  have hn : stabilizer (family P) a ≤ normalizer (d.localGroup a : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (d.localGroup a).map (MulAut.conj g).toMonoidHom = _
    rw [← d.conjugate]
    exact congrArg d.localGroup hg
  let : K.Normal := (normal_subgroupOf_iff_le_normalizer (d.local_le a)).mpr hn
  have hTK : (T : Subgroup (stabilizer (family P) a)) ≤ K :=
    fun x hx => d.sylow_le a T (mem_map_of_mem _ hx)
  have hq : Function.Surjective qK :=
    (e.surjective.comp (QuotientGroup.mk'_surjective _)).comp eK.surjective
  let S := (T.subtype hTK).mapSurjective hq
  have hg : GeneratedByFixedSpace ρ
      (((T : Subgroup (stabilizer (family P) a)).subgroupOf K).map qK) :=
    CommutingOneProfile.source_center_representation_generated_normal h a T K hTK qK ρ
      (fun l z => hact (eK l) z)
  have hZL : Z (family P) a ≤ d.localGroup a :=
    ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
      ((pCoreIn_le_sylow _ T).trans (d.sylow_le a T))
  exact ⟨S, rfl, hg, residual_fixed_eq_bot_of_center_eq_bot (d.localGroup a) (Z (family P) a)
    hZL hz q ρ hact⟩

/-- Both supplementary module premises of corrected 5.12 hold on the literal
starting center, with its original local quotient and conjugation coordinates.
Faithfulness, the actor's quadraticity and the strict comparison remain separate. -/
theorem source_critical_center_module_prepared
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    {D : Type*} [Group D]
    (T : Sylow 2 (stabilizer (family P) a))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D) :
    letI := CommutingOneProfile.source_center_elementary h a
    let K := (d.localGroup a).subgroupOf (stabilizer (family P) a)
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup a)))
    let qK := q.comp (subgroupOfEquivOfLe (d.local_le a)).toMonoidHom
    ∀ (ρ : Representation (ZMod 2) D (Additive (Z (family P) a))),
      (∀ (l : d.localGroup a) (z : Additive (Z (family P) a)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      ∃ S : Sylow 2 D,
        (S : Subgroup D) = ((T : Subgroup (stabilizer (family P) a)).subgroupOf K).map qK ∧
        GeneratedByFixedSpace ρ S ∧ fixedSpace ρ (pResidual 2 D) = ⊥ := by
  obtain ⟨_, _, hZ, _⟩ := source_critical_geometry h d hc hab hd hb hcomm
  exact source_center_module_prepared_of_center_eq_bot h d a
    (local_center_eq_bot_of_neighbor_central h d hab hZ) T e

/-- The reduced critical center has an actual quotient action with both auxiliary
5.12 premises proved. No representation or fixed-space hypothesis is supplied. -/
theorem reduced_critical_center_module
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
    (d : RemainingLocalTheorems (Reduction.reducedFamily J S₀))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a, Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    {D : Type*} [Group D]
    (T : Sylow 2 (stabilizer (Reduction.reducedFamily J S₀) a))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D) :
    letI : IsElementaryAbelian 2 (Z (Reduction.reducedFamily J S₀) a) :=
      CommutingOneProfile.source_center_elementary (Reduction.reduced_triple h) a
    let K := (d.localGroup a).subgroupOf (stabilizer (Reduction.reducedFamily J S₀) a)
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup a)))
    let qK := q.comp (subgroupOfEquivOfLe (d.local_le a)).toMonoidHom
    ∃ (ρ : Representation (ZMod 2) D (Additive (Z (Reduction.reducedFamily J S₀) a)))
      (S : Sylow 2 D),
      (∀ (l : d.localGroup a) (z : Additive (Z (Reduction.reducedFamily J S₀) a)),
        ((ρ (q l) z).toMul : Reduction.G₀ J S₀) =
          (l : Reduction.G₀ J S₀) * z.toMul * (l : Reduction.G₀ J S₀)⁻¹) ∧
      (S : Subgroup D) = ((T : Subgroup (stabilizer (Reduction.reducedFamily J S₀) a)).subgroupOf K).map qK ∧
      GeneratedByFixedSpace ρ S ∧ fixedSpace ρ (pResidual 2 D) = ⊥ := by
  let : IsElementaryAbelian 2 (Z (Reduction.reducedFamily J S₀) a) :=
    CommutingOneProfile.source_center_elementary (Reduction.reduced_triple h) a
  dsimp only
  obtain ⟨ρ, hact⟩ := source_exists_center_quotient_action (Reduction.reduced_triple h)
    (reducedEarlierLocalTheorems h d) a e
  obtain ⟨S, hS, hg, hres⟩ := source_critical_center_module_prepared
    (Reduction.reduced_triple h) (reducedEarlierLocalTheorems h d) hc hab hd hb hcomm T e ρ hact
  exact ⟨ρ, S, hact, hS, hg, hres⟩

/-- Corrected 5.12 on the actual starting center of the commuting critical pair.
The source proof discharges generation and the O²-fixed-space premise;
reduced 6.2(d) is supplied by the original F1.11 hypothesis. The
literal quotient model, faithfulness, quadratic actor and actor placement remain
explicit; a strict numerical comparison produces equivariant natural coordinates. -/
theorem reduced_critical_center_bound_and_recognition
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
    (d : RemainingLocalTheorems (Reduction.reducedFamily J S₀))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)} (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀)) (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a, Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    {D : Type*} [Group D] [Finite D] (M : BinaryRankOneModel D)
    (T : Sylow 2 (stabilizer (Reduction.reducedFamily J S₀) a))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D)
    (A : Subgroup (d.localGroup a)) :
    letI : IsElementaryAbelian 2 (Z (Reduction.reducedFamily J S₀) a) :=
      CommutingOneProfile.source_center_elementary (Reduction.reduced_triple h) a
    let K := (d.localGroup a).subgroupOf (stabilizer (Reduction.reducedFamily J S₀) a)
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup a)))
    let qK := q.comp (subgroupOfEquivOfLe (d.local_le a)).toMonoidHom
    ∀ (ρ : Representation (ZMod 2) D (Additive (Z (Reduction.reducedFamily J S₀) a))),
      (∀ (l : d.localGroup a) (z : Additive (Z (Reduction.reducedFamily J S₀) a)),
        ((ρ (q l) z).toMul : Reduction.G₀ J S₀) = (l : Reduction.G₀ J S₀) * z.toMul * (l : Reduction.G₀ J S₀)⁻¹) →
      Function.Injective ρ →
      A.map q ≤ ((T : Subgroup (stabilizer (Reduction.reducedFamily J S₀) a)).subgroupOf K).map qK →
      IsQuadratic ρ (A.map q) →
      ∃ S : Sylow 2 D,
        (S : Subgroup D) = ((T : Subgroup (stabilizer (Reduction.reducedFamily J S₀) a)).subgroupOf K).map qK ∧
        Nat.card (A.map q) ≤ Nat.card (Additive (Z (Reduction.reducedFamily J S₀) a) ⧸ fixedSpace ρ (A.map q)) ∧
        (Nat.card (Additive (Z (Reduction.reducedFamily J S₀) a) ⧸ fixedSpace ρ (A.map q)) <
          Nat.card (A.map q) ^ 2 → NaturalRealization ρ S) := by
  let : ∀ i, Finite (Reduction.reducedFamily J S₀ i) :=
    finite_endpoints (Reduction.reduced_triple h)
  let : IsElementaryAbelian 2 (Z (Reduction.reducedFamily J S₀) a) :=
    CommutingOneProfile.source_center_elementary (Reduction.reduced_triple h) a
  let : Finite (Z (Reduction.reducedFamily J S₀) a) := Finite.of_injective
    (inclusion (Z_le_stabilizer (Reduction.reducedFamily J S₀) a)) (inclusion_injective _)
  dsimp only
  intro ρ hact hf hAS hquad
  obtain ⟨S, hS, hg, hres⟩ := source_critical_center_module_prepared
    (Reduction.reduced_triple h) (reducedEarlierLocalTheorems h d) hc hab hd hb hcomm T e ρ hact
  refine ⟨S, hS, ?_⟩
  exact binary_rank_one_bound_and_recognition M ρ hf S _ (hS.symm ▸ hAS) hquad hg hres

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
