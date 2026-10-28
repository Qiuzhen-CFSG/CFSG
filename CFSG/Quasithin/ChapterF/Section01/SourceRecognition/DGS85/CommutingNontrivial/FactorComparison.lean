module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FactorBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ReciprocalVanishingApplication

/-!
# Comparing the original factor indices in DGS 8.2

Under reverse containment, the proved moving-intersection theorem identifies
C_(Z_alpha)(V_alpha') with Z_alpha intersect Q_alpha'. The reverse
centralizer index is bounded by the original core index because Q_alpha
centralizes Z_alpha. Thus the ending-factor inequality makes the starting
linear center an offender. Corrected 5.12 recognizes its actual natural
action, and the proved natural-case graph argument excludes reverse containment.

The factor inequality is an intermediate input here; the final applications
in `LinearFactorEscape` discharge it for the supplied ending quotient models.
Source: DGS, Groups and Graphs (1985), 8.2, printed pp.134--135.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Under reverse containment, the center's centralizer of the ending span
is exactly its original ending-core intersection. -/
theorem source_reverse_center_centralizer (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta) :
    Z (family P) a ⊓ centralizer (V (family P) a' 1 : Set G) =
      Z (family P) a ⊓ Q (family P) a' := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h a
  let F := family P
  obtain ⟨_,_,_,_,w,hw,_⟩ := source_critical_geometry h d hc hab hd hb hcomm
  have hZP : Z F a ≤ stabilizer F a' := Z_le_stabilizer_of_dist_le_b F h.generate a a' hc.1.le
  have hp : IsPGroup 2 ↥(Z F a ⊓ centralizer (V F a' 1 : Set G) : Subgroup G) :=
    (IsElementaryAbelian.isPGroup 2 (Z F a)).to_le inf_le_left
  have hU : Z F a ⊓ centralizer (V F a' 1 : Set G) ≤ U F a' :=
    (inf_le_inf_right _ hZP).trans (source_span_centralizer_le_kernel h hw)
  exact le_antisymm (le_inf inf_le_left
    (pSubgroup_le_Q_of_le_U F a' _ hp hU (d.kernel_sylow a')))
    (le_inf inf_le_left (commutator_eq_bot_iff_le_centralizer.mp
      (source_reverse_intersection_centralizes h hB d hc hab hd hb hcomm models hreverse)))

private theorem sylow_generation_transport {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (S T : Sylow 2 D)
    (hgen : GeneratedByFixedSpace ρ S) : GeneratedByFixedSpace ρ T := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq D S T
  exact generatedByFixedSpace_of_equivariant_surjection ρ ρ
    (MulAut.conj g).toMonoidHom (ρ g)
    (fun v => ⟨ρ g⁻¹ v,ρ.self_inv_apply g v⟩)
    (by intro a v; simp only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,
      MulAut.conj_apply,map_mul,Module.End.mul_apply,ρ.inv_self_apply]) S hgen

/-- The ending-factor bound completes reciprocal escape when the starting
quotient is linear. Every center-action and corrected 5.12 premise is
constructed; the bound is discharged by the literal applications below. -/
theorem source_reciprocal_linear_escape_of_factor_bound (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ ≠ ⊥)
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n)
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,K))
    (hfactor : (Q (family P) a').relIndex (Z (family P) a) ≤
      (centralizer (Z (family P) a : Set G)).relIndex (V (family P) a' 1)) :
    ¬ V (family P) a' 1 ≤ Q (family P) beta := by
  intro hreverse
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h a
  let F := family P
  let L := d.localGroup a
  let Z₀ := Z F a
  let A := V F a' 1
  obtain ⟨_,hb3,hcentral,hquadratic,_⟩ := source_critical_geometry h d hc hab hd hb hcomm
  change 3 ≤ b F at hb3
  have hz := local_center_eq_bot_of_neighbor_central h d hab hcentral
  let := source_center_nontrivial h a
  let : IsElementaryAbelian 2 A := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by omega) a'
  have hAP : A ≤ stabilizer F a := hreverse.trans ((source_Z_Q_U h beta).2.trans
    ((ballKernel_one_le_edge F hab.symm).trans inf_le_right))
  have hAL : A ≤ L := pGroup_le_localGroup F d a A (IsElementaryAbelian.isPGroup 2 A) hAP
  have hZL : Z₀ ≤ L := pGroup_le_localGroup F d a Z₀ (IsElementaryAbelian.isPGroup 2 Z₀)
    (Z_le_stabilizer F a)
  let : Finite L := Finite.of_injective (inclusion (d.local_le a)) (inclusion_injective _)
  let : Finite Z₀ := Finite.of_injective (inclusion hZL) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion hAL) (inclusion_injective _)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let Aq := (A.subgroupOf L).map q
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let : IsElementaryAbelian 2 Aq := IsElementaryAbelian.map q
  obtain ⟨ρ,hact⟩ := source_exists_center_quotient_action h d a e
  obtain ⟨S₀,_,hgen,hres⟩ := source_center_module_prepared_of_center_eq_bot h d a hz default e ρ hact
  have hf := linear_quotient_action_faithful hn hK e ρ hres
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 Aq).exists_le_sylow
  have hg := sylow_generation_transport ρ S₀ S hgen
  let δ := centerSection L Z₀ hZL ((d.local_le a).trans (stabilizer_normalizes_Z F a)) q ρ hact
  have hq : IsQuadratic ρ Aq := by
    apply BinaryConjugationSection.isQuadratic_of_triple_commutator_le L Z₀ ⊥ A ρ q δ
    rw [commutator_comm A,commutator_comm A]
    exact (commutator_mono (commutator_mono (Z_neighbor_le_V F hab.symm) le_rfl) le_rfl).trans
      hquadratic.2.le
  have hi := center_action_fixed_index L Z₀ A hZL δ.normalized hAL q ρ hact
  have he := source_reverse_center_centralizer h hB d hc hab hd hb hcomm models hreverse
  have hcidx : (centralizer (A : Set G)).relIndex Z₀ = (Q F a').relIndex Z₀ := by
    rw [←inf_relIndex_left Z₀ (centralizer (A : Set G)),he,inf_relIndex_left]
  have hcard : Nat.card Aq = (Q F a).relIndex A :=
    BinaryConjugationSection.actor_image_card_eq_relIndex L (Q F a) A q (local_quotient_kernel F d a e) hAL
  have hupper : (centralizer (Z₀ : Set G)).relIndex A ≤ (Q F a).relIndex A :=
    relIndex_le_of_le_left (le_centralizer_iff.mp (Z_centralizes_Q F a (source_Z_Q_U h a).1))
      (((Q F a).subgroupOf A).index_ne_zero_of_finite)
  have hx : 1 < (Q F a').relIndex Z₀ := by
    have hnz : (Q F a').relIndex Z₀ ≠ 0 := ((Q F a').subgroupOf Z₀).index_ne_zero_of_finite
    have hno : (Q F a').relIndex Z₀ ≠ 1 := by
      intro heq
      exact hc.2 ((relIndex_eq_one.mp heq).trans (source_Z_Q_U h a').2)
    omega
  have hxy : (Q F a').relIndex Z₀ ≤ Nat.card Aq := by
    rw [hcard]
    exact hfactor.trans hupper
  have hstrict : Nat.card (Additive Z₀ ⧸ fixedSpace ρ Aq) < Nat.card Aq ^ 2 := by
    rw [hi,hcidx]
    nlinarith
  have hnat := (binary_rank_one_bound_and_recognition (.sl2 K n hn hK (MulEquiv.refl _))
    ρ hf S Aq hAS hq hg hres).2 hstrict
  exact source_reciprocal_escape_of_natural_center h hB d hc hab hd hb hcomm models hne
    (source_natural_center_of_recognition h d a hz e ρ S hact hnat) hreverse

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
