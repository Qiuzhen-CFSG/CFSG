module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairFixedSpaces

/-!
# Descending the Chapter 11 pair section to a prescribed actor

The beta core acts trivially on the literal quotient V/(Z_alpha intersect
Z_gamma). Any surjective actor map with precisely that kernel therefore
carries its conjugation representation. The critical-center image acts
quadratically and generates the module from its fixed space. The two seed
images identify that entire fixed space and compute its quotient order as
the opposite-seed relative index. No alpha row or core-product identity is
assumed.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(a,b,d,g), printed pp.168--170, and corrected (5.12).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The literal pair quotient with its prescribed actor, quotient coordinates,
quadratic action and corrected fixed-generation hypothesis. -/
theorem source_pair_section_for_actor {K : Type*} [Group K]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (f : ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b : Subgroup G) →* K)
    (hf : Function.Surjective f)
    (hk : f.ker = (Q (family P) b).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b))
 :
    let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∃ hJ : (J.subgroupOf V).Normal, letI := hJ
      ∃ hE : IsElementaryAbelian 2 (V ⧸ J.subgroupOf V), letI := hE
        ∃ σ : Representation (ZMod 2) K (Additive (V ⧸ J.subgroupOf V)),
          ∃ s : BinaryConjugationSection H V J (σ.comp f),
            (∀ x : V, (s.coordinates x).toAdd = Additive.ofMul (QuotientGroup.mk' (J.subgroupOf V) x)) ∧
            fixedSpace σ ⊤ = ⊥ ∧
            IsQuadratic σ (((Z (family P) a).subgroupOf H).map f) ∧
            GeneratedByFixedSpace σ (((Z (family P) a).subgroupOf H).map f) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  let D := Q (family P) a ⊓ Q (family P) c
  obtain ⟨hJ,hE,hQ,σ₀,s₀,_⟩ := source_rankOne_pair_section h hB d hc hb hbc hac Ma Mb
  let := hJ
  let := hE
  have hinter : D ⊓ V = J := source_rankOne_pair_core_intersection h hB d hc hb hbc hac Mb
  have hab := source_critical_one_adjacent hc hb
  have hn := source_pair_core_normalizers h hab hbc
  have hHJ : H ≤ normalizer (J : Set G) := by
    rw [←hinter]
    exact (le_inf hn.2.1 hn.2.2.1).trans inf_normalizer_le_normalizer_inf
  have hdisp : ⁅Q (family P) b,V⁆ ≤ J := by
    rw [←hinter]
    exact le_inf (source_rankOne_pair_core_action h hB d hc hb hbc Ma Mb)
      (le_normalizer_iff_commutator_le_right.mp (le_sup_right.trans hn.2.2.1))
  obtain ⟨σ,s,hs⟩ := exists_descended_actor H V J s₀.section_le s₀.kernel_le
    hn.2.2.1 hHJ f hf (by
      intro y hy x hx
      have hyker : y ∈ f.ker := hy
      rw [hk] at hyker
      exact hdisp (commutator_mem_commutator hyker hx))
  have hfixed := source_rankOne_pair_fixed_spaces h hB d hc hb hbc Mb f hf hk σ s
  have hquad := isQuadratic_of_triple_commutator_le H V J (Z (family P) a) σ f s
    (show ⁅Z (family P) a,⁅Z (family P) a,V⁆⁆ ≤ J from by
      simpa only [commutator_comm] using
        (((commutator_mono (commutator_mono (pairSpan_le_core _ _ _) le_rfl) le_rfl).trans
          (source_adjacent_core_center_quadratic h hab).le).trans (bot_le : (⊥ : Subgroup G) ≤ J)))
  obtain ⟨g,hg,hga⟩ := source_rankOne_center_pair_moves h hB d hc hb hbc Mb
  let g₀ : H := ⟨g,mem_sup_left hg⟩
  have hgb : g • b = b := by
    apply (show H ≤ stabilizer (family P) b from ?_) g₀.property
    apply sup_le (sup_le ?_ ?_) (Q_le_stabilizer _ b)
    · exact (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U h a).2).trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)
    · exact (((source_Z_Q_U h c).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U h c).2).trans ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
  have hconj : Z (family P) c ⊓ Q (family P) b =
      (Z (family P) a ⊓ Q (family P) b).conjBy (g₀ : G) := by
    dsimp only [conjBy,g₀]
    rw [map_inf _ _ _ (MulAut.conj g).injective,←Z_translate,←Q_translate,hga,hgb]
  have hgen := pair_section_generated H V J (Z (family P) a ⊓ Q (family P) b)
    (Z (family P) c ⊓ Q (family P) b) (Z (family P) a) σ f s le_sup_left
    (sup_eq_left.mpr s.kernel_le).symm g₀ hconj
    ((commutator_eq_bot_iff_le_centralizer.mpr
      ((le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative (Z (family P) a))).trans
        (centralizer_le inf_le_left))).le.trans bot_le)
  exact ⟨hJ,hE,σ,s,hs,hfixed.1,hquad,hgen⟩
/-- The literal fixed-space quotient is exactly the opposite-seed index,
for every descended pair actor. -/
theorem source_pair_fixed_quotient_card
    {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (f : ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b : Subgroup G) →* K)
    (hf : Function.Surjective f)
    (hk : f.ker = (Q (family P) b).subgroupOf ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b))
    (σ : Representation (ZMod 2) K W)
    (s : BinaryConjugationSection ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b)
      (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b))
      (Z (family P) a ⊓ Z (family P) c) (σ.comp f)) :
    Nat.card (W ⧸ fixedSpace σ (((Z (family P) a).subgroupOf
        ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b)).map f)) =
      (Q (family P) a).relIndex (Z (family P) c ⊓ Q (family P) b) := by
  let E := Z (family P) a ⊓ Q (family P) b
  let F := Z (family P) c ⊓ Q (family P) b
  let J := Z (family P) a ⊓ Z (family P) c
  have hJQ : J ≤ Q (family P) b := s.kernel_le.trans (pairSpan_le_core _ _ _)
  have hinter : J = E ⊓ F := le_antisymm
    (le_inf (le_inf inf_le_left hJQ) (le_inf inf_le_right hJQ))
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
  have hcomp := s.isCompl_imageSpace E F rfl hinter
  have hfixed := source_rankOne_pair_fixed_spaces h hB d hc hb hbc Mb f hf hk σ s
  rw [hfixed.2.1,Nat.card_congr (Submodule.quotientEquivOfIsCompl _ _ hcomp).toEquiv,
    s.imageSpace_card_eq_relIndex F le_sup_right]
  have hi : Q (family P) a ⊓ F = J := by
    dsimp only [F]
    rw [←inf_assoc,(source_rankOne_mixed_center_intersections h hB d hc hb hbc Mb).2,
      inf_eq_left.mpr hJQ]
  change J.relIndex F = _
  rw [←hi,inf_relIndex_right]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
