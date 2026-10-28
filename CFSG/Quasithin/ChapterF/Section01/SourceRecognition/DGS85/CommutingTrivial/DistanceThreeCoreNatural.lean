module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeCore
public import Theory.Representation.SL2.SharpSection
public import Theory.Representation.BinaryConjugationSection.NaturalExtension

/-!
# Naturality of the middle core quotient

The genuine full-stabilizer obstruction makes the action on the core quotient
nontrivial: a trivial action would normalize the adjacent core intersection.
The opposite span has full Sylow image and fixes a subgroup of index `q` in
the quotient of order `q^2`. For `q > 2`, the involution displacement bound
makes this fixed codimension sharp. A conjugate Sylow then identifies the
whole original action with the natural module.

The literal reduced-path application in `DistanceThreeCoreSection` supplies
the actor, commutator bound and indices. Source: DGS, *Groups and Graphs*
(1985), §9.10(1b), printed p.147, in the proof's nonbinary branch.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The source core-intersection obstruction forces the original quotient action
to be nontrivial. -/
theorem middle_core_section_nontrivial
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta x : Vertex (family P)} (hbx : (graph (family P)).Adj beta x)
    (hob : ¬ stabilizer (family P) beta ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) beta : Subgroup G) : Set G))
    {F W : Type*} [Field F] [AddCommGroup W] [Module (ZMod 2) W]
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (σ : Representation (ZMod 2) SL(2,F) W)
    (d : BinaryConjugationSection (graphLocalGroup (family P) beta) (Q (family P) beta)
      (Q (family P) a ⊓ Q (family P) x)
      (σ.comp (eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta)))))) :
    ∃ g, σ g ≠ 1 := by
  by_contra! ht
  let Γ := family P
  let H := graphLocalGroup Γ beta
  let N := Q Γ a ⊓ Q Γ x
  let D := Q Γ beta ⊓ Q Γ x
  have hN : N ≤ D := le_inf d.kernel_le inf_le_right
  have hHD : H ≤ normalizer (D : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    apply commutator_le.mpr
    intro l hl z hz
    exact hN ((d.action_mem_ker_iff ⟨l,hl⟩).mp (ht _) z hz.1)
  apply hob
  rw [inf_comm (Q Γ x),←graphLocalGroup_sup_edge h hB hS hbx]
  refine sup_le hHD ?_
  exact (le_inf (inf_le_left.trans (stabilizer_normalizes_Q Γ beta))
    (inf_le_right.trans (stabilizer_normalizes_Q Γ x))).trans inf_normalizer_le_normalizer_inf

/-- A full Sylow actor fixing the adjacent half recognizes the actual core
section as natural in the nonbinary branch of §9.10(1b). -/
theorem middle_core_section_natural
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a beta x : Vertex (family P)} (hbx : (graph (family P)).Adj beta x)
    (hob : ¬ stabilizer (family P) beta ≤ normalizer
      ((Q (family P) x ⊓ Q (family P) beta : Subgroup G) : Set G))
    {F W : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (eβ : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F))
    (σ : Representation (ZMod 2) SL(2,F) W)
    (d : BinaryConjugationSection (graphLocalGroup (family P) beta) (Q (family P) beta)
      (Q (family P) a ⊓ Q (family P) x)
      (σ.comp (eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) beta))))))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hcard : Nat.card W = Nat.card F ^ 2)
    (A : Subgroup G) (hp : IsPGroup 2 A) (hA : A ≤ graphLocalGroup (family P) beta)
    (hiA : (Q (family P) beta).relIndex A = Nat.card F)
    (hiD : (Q (family P) beta ⊓ Q (family P) x).relIndex (Q (family P) beta) = Nat.card F)
    (hc : ⁅A,Q (family P) beta ⊓ Q (family P) x⁆ ≤ Q (family P) a ⊓ Q (family P) x) :
    let : Algebra (ZMod 2) F := ZMod.algebra F 2
    ∃ E : W ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ g v, E (σ g v) = Matrix.mulVec g.val (E v) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let := finite_endpoints h
  let Γ := family P
  let : Finite (Q Γ beta) := Finite.of_injective
    (inclusion (Q_le_stabilizer Γ beta)) (inclusion_injective _)
  let H := graphLocalGroup Γ beta
  let q := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let D := Q Γ beta ⊓ Q Γ x
  let I := (A.subgroupOf H).map q
  have hnt := middle_core_section_nontrivial h hB hS hbx hob eβ σ d
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ eβ.injective,QuotientGroup.ker_mk']
  have hkmap : q.ker.map H.subtype = Q Γ beta := hk ▸ graphLocalGroup_core h beta
  obtain ⟨T,hT⟩ := (hp.comap_subtype.map q).exists_le_sylow
  have hIcard : Nat.card I = Nat.card F := by
    rw [←relIndex_ker,←relIndex_map_map_of_injective _ _ H.subtype_injective,
      hkmap,map_subgroupOf_eq_of_le hA,hiA]
  have hTI : I = T := eq_of_le_of_card_ge hT (by
    rw [hIcard]
    exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).toEquiv).ge)
  have hdim : Module.finrank (ZMod 2) W = 2*n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hF,←pow_mul] at hcard
    have he := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hcard
    omega
  have hfixed : d.imageSpace D ≤ fixedSpace σ I := by
    intro w hw l
    obtain ⟨lH,hl,he⟩ := l.property
    change σ (l : SL(2,F)) w = w
    rw [←he]
    exact d.fixed_on_imageSpace_of_commutator_le A D hc lH hl w hw
  have hdi := d.imageSpace_codimension_of_index D inf_le_left
    (le_inf d.kernel_le inf_le_right) n (hiD.trans hF)
  have hupper : fixedCodim σ I ≤ n := by
    have hl := Submodule.finrank_mono hfixed
    have he := fixedCodim_add_finrank σ I
    omega
  have hne : I ≠ ⊥ := by
    intro he
    have hc : Nat.card I = 1 := by rw [he]; simp
    rw [hIcard,hF] at hc
    exact (ne_of_gt (one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : n ≠ 0))) hc
  have hcodim : fixedCodim σ T = n := by
    rw [←hTI]
    exact le_antisymm hupper
      (Representation.SL2.two_subgroup_fixedCodim_lower σ hnt hn hF I (hp.comap_subtype.map q) hne)
  obtain ⟨g,_,hg⟩ := Matrix.SpecialLinearGroup.exists_residual_conjugate_sylow_image_sup_eq_top
    T (MonoidHom.id SL(2,F)) Function.surjective_id
  simp only [Subgroup.map_id] at hg
  let R : Sylow 2 SL(2,F) := g • T
  have hR : fixedCodim σ R = n := by
    change fixedCodim σ ((T : Subgroup SL(2,F)).map (MulAut.conj g).toMonoidHom) = n
    rw [fixedCodim_map_conj,hcodim]
  exact Representation.SL2.natural_of_order_and_sharp_fixed σ hnt hn hF T R hg hcodim hR hcard

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
