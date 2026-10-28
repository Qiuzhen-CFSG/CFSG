module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualRecognition
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# The field-square constraint in the natural residual alternative

The image of the moving neighboring center in the full residual section
is fixed by the constructed residual-join Sylow. In a natural SL₂ section
this image has order at most the defining field. Its original denominator
centralizes the whole residual join, hence the original opposite actor.
The unitary displacement estimate therefore gives q_lambda² ≤ q_alpha'.

The reduced-source application obtains the natural action from a strict
original centralizer-index comparison using corrected (5.12). Comparing
the literal quotient maps identifies that action with the prepared one;
no naturality or fixed-generation premise is added to the configuration.
The torus exclusion of this alternative remains a subsequent source step.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
proof of (8.3), p.136, the inequality preceding the torus argument.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- In the natural residual alternative, the neighboring seed has image
at most one natural fixed line. The original unitary actor supplies the
lower bound, on the very same residual denominator. -/
theorem source_natural_residual_seed_bound (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a,Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a',Z (family P) w.val⁆ ≠ ⊥)
    (hescape : ¬ Q (family P) w.val ≤ Q (family P) a')
    (R : Sylow 2 (d.localGroup w.val))
    (hR : (R : Subgroup (d.localGroup w.val)).map (d.localGroup w.val).subtype =
      (stabilizer (family P) w.val ⊓ stabilizer (family P) a').pCoreIn 2)
    {K W : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] :
    let F := family P
    let L := d.localGroup a'
    let E := (pResidual 2 L).map L.subtype
    let D := E ⊔ Q F w.val
    ∀ (eD : (D ⧸ pCore 2 D) ≃* SL(2,K))
      (σ : Representation (ZMod 2) SL(2,K) W)
      (_c : BinaryConjugationSection D (V F a' 1) (V F a' 1 ⊓ centralizer (E : Set G))
        (σ.comp (eD.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D)))))
      (S : Sylow 2 D) (T : Sylow 2 SL(2,K)),
      (S : Subgroup D).map D.subtype = quotientSylowOmegaPreimage (d.localGroup w.val) R →
      (S : Subgroup D).map (eD.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))) = T →
      IsQuadratic σ T → GeneratedByFixedSpace σ T → fixedSpace σ ⊤ = ⊥ →
      (W ≃ₗ[ZMod 2] (Fin 2 → K)) →
      (V F a' 1 ⊓ centralizer (E : Set G)).relIndex (Z F w.val) ≤ Nat.card K ∧
      ∀ m : ℕ, 2 ≤ m →
        (ClassicalGroup.IsPSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^m) ∨
          IsSU (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) 3 (2^m)) →
        (2^m)^2 ≤ Nat.card K := by
  intro F L E D eD σ c S T hS hT hq hgen hfix C
  let := finite_endpoints h
  let π := eD.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  let N := V F a' 1 ⊓ centralizer (E : Set G)
  let A := V F beta 1 ⊓ Q F a'
  let ZW := Z F w.val
  let : Finite ZW := Finite.of_injective (inclusion (Z_le_stabilizer F w.val)) (inclusion_injective _)
  have hmove : ⁅quotientSylowOmegaPreimage (d.localGroup w.val) R,ZW⁆ ≤ N :=
    (source_omega_displacement_residual_fixed h hB d hc hab hd hb hcomm models w hm hescape R hR).trans
      (inf_le_inf_right _ (Z_neighbor_le_V F w.property))
  have hfixed : c.imageSpace ZW ≤ fixedSpace σ T := by
    intro z hz t
    obtain ⟨s,hs,he⟩ := (show t.val ∈ (S : Subgroup D).map π from hT.symm ▸ t.property)
    change σ t.val z = z
    rw [←he]
    exact c.fixed_on_imageSpace_of_commutator_le _ ZW hmove s
      (hS ▸ mem_map_of_mem D.subtype hs) z hz
  have hcard := (Nat.card_le_card_of_injective (Submodule.inclusion hfixed)
    (Submodule.inclusion_injective hfixed)).trans_eq
      (sl2_natural_fixed_spaces σ T hq hgen hfix C).1
  rw [c.imageSpace_card_eq_relIndex ZW (Z_neighbor_le_V F w.property)] at hcard
  refine ⟨hcard,?_⟩
  intro m hm2 hu
  obtain ⟨_,hb3,_,_,_⟩ := source_critical_geometry h d hc hab hd hb hcomm
  let : IsElementaryAbelian 2 (V F beta 1) := CommutingThreeProfile.V_elementary F h.generate
    (fun v => (source_Z_Q_U h v).1) d.kernel_sylow (by change 2 < b (family P); omega) beta
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨_,hAL,_,hAQ,_⟩ := source_moving_actor h d hc hab hd hb hcomm w hm
  have hlower := source_moving_unitary_orbit_bound h hB d hc hab hd hb hcomm models w hm hm2 hu rfl A hAL hAQ
  have hAD : A ≤ D := inf_le_left.trans
    (source_critical_actor_le_residual_join h hB d hc hab hd hb hcomm w R hR)
  have hCN : ZW ⊓ N ≤ centralizer (A : Set G) := by
    apply le_centralizer_iff.mpr
    exact hAD.trans (sup_le
      (le_centralizer_iff.mp (inf_le_right.trans inf_le_right))
      ((le_centralizer_iff.mp (Z_centralizes_Q F w.val (source_Z_Q_U h w.val).1)).trans
        (centralizer_le inf_le_left)))
  have hind := relIndex_le_of_le_left hCN
    (((ZW ⊓ N).subgroupOf ZW).index_ne_zero_of_finite)
  rw [inf_relIndex_left] at hind
  exact hlower.trans (hind.trans hcard)

open Representation.NormalElementaryQuotient CommutingTrivial
variable {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- A strict original centralizer comparison in the linear ending branch
forces the source unitary field-square inequality. The action and natural
coordinates are constructed by the preceding corrected recognition theorem;
no natural-module hypothesis is imposed on the original configuration. -/
theorem reduced_strict_linear_residual_unitary_field_bound
    (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a,Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (w : (graph (Reduction.reducedFamily J S₀)).neighborSet a')
    (hm : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≠ ⊥)
    (R : Sylow 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val))
    (hR : (R : Subgroup (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)).map
      (graphLocalGroup (Reduction.reducedFamily J S₀) w.val).subtype =
        (stabilizer (Reduction.reducedFamily J S₀) w.val ⊓ stabilizer (Reduction.reducedFamily J S₀) a').pCoreIn 2)
    (hbad : ¬ ⁅quotientSylowOmegaPreimage (graphLocalGroup (Reduction.reducedFamily J S₀) w.val) R,
      Z (Reduction.reducedFamily J S₀) w.val⁆ ≤
        ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
          V (Reduction.reducedFamily J S₀) a' 1⁆)
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily J S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) a')) ≃* SL(2,K))
    (hstrict : (centralizer (V (Reduction.reducedFamily J S₀) beta 1 : Set (Reduction.G₀ J S₀))).relIndex
      (V (Reduction.reducedFamily J S₀) a' 1) <
      Nat.pow ((Q (Reduction.reducedFamily J S₀) a').relIndex (V (Reduction.reducedFamily J S₀) beta 1)) 2) :
    ∀ m : ℕ, 2 ≤ m →
      (ClassicalGroup.IsPSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^m) ∨
        IsSU (graphLocalGroup (Reduction.reducedFamily J S₀) w.val ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily J S₀) w.val)) 3 (2^m)) →
      (2^m)^2 ≤ 2^n := by
  let ht := Reduction.reduced_triple h
  let F := Reduction.reducedFamily J S₀
  let L := graphLocalGroup F a'
  let U := (V F a' 1).subgroupOf L
  let E := (pResidual 2 L).map L.subtype
  let D := E ⊔ Q F w.val
  let d := Reduction.reducedEarlierLocalTheorems h hob
  let : ∀ i, Finite (F i) := finite_endpoints ht
  let : U.Normal := neighborhoodIn_normal F a' L (sylowGenerated_le _)
  obtain ⟨hb2,_,hDL,eD,σ,S,T,heD,hact,hS,hT,hgen,hres,_,⟨c⟩⟩ :=
    reduced_counterexample_linear_residual_prepared h hob models hc hab hd hb hcomm w hm R hR hbad hn hK e
  let : IsElementaryAbelian 2 U := neighborhoodIn_elementary F ht.generate
    (fun v => (source_Z_Q_U ht v).1) (Reduction.reduced_kernel_sylow h) a' hb2 L
  let W := FixedQuotient U (pResidual 2 L)
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion hDL) (inclusion_injective _)
  let : Finite (V F a' 1) := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  let : Finite W := Finite.of_surjective (fun x : V F a' 1 => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  obtain ⟨_,hDL',eD',τ,T',heD',hact',_,_,_,_,_,_,_,hupper,hnat⟩ :=
    reduced_counterexample_linear_residual_recognition h hob models hc hab hd hb hcomm w hm R hR hbad hn hK e
  obtain ⟨hnatural,C,_⟩ := hnat (hupper.trans_lt hstrict)
  have heq : eD = eD' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D) x
    exact (heD g).trans (heD' g).symm
  have hσ : σ = τ := by
    ext x z
    obtain ⟨g,rfl⟩ := (eD.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 D))) x
    change σ (eD (QuotientGroup.mk' (pCore 2 D) g)) z = τ (eD (QuotientGroup.mk' (pCore 2 D) g)) z
    rw [hact,heq]
    exact (congrArg (fun f => f z) (hact' g)).symm
  have hq : IsQuadratic σ T := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,K) T' T
    rw [hσ,←hg]
    exact SL2SylowFixedRecognition.quadratic_conjugate τ hnatural.2.2 g
  have hfix : fixedSpace σ ⊤ = ⊥ :=
    bot_unique ((fixedSpace_antitone σ le_top).trans hres.le)
  have hescape := core_escape_of_intersection_obstruction F (hob w.val a' w.property.symm)
  have hbound := (source_natural_residual_seed_bound ht (Reduction.reduced_borel_core_sylow h)
    d hc hab hd hb hcomm models w hm hescape R hR eD σ c S T hS hT hq hgen hfix C).2
  intro m hm2 hu
  rw [←hK]
  exact hbound m hm2 hu

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
