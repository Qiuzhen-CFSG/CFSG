module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoreQuotient
public import Theory.Representation.ComplementaryConjugateFixed
public import Theory.Representation.BinaryConjugationSection.FixedMoving
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage

/-!
# Exact fixed spaces in the general Chapter 11 two-seed quotient

The two center images generate the actual quotient actor. Their seed images
are complementary and conjugate, and each center fixes its own seed.
The general complementary-conjugate argument identifies the entire fixed
spaces, not merely subspaces contained in them. Their intersection is zero.
Lifting coordinates gives the exact commutator preimages in the original
pair span, with denominator Z_alpha intersect Z_gamma. Each alpha core
therefore meets the pair span in its own seed. The original-source consumer
uses this equality to remove the intersection premise of the nonlinear
small-core exclusion.

No linear alpha marking, field bound, core-product identity, or fixed-space
premise is assumed. This strengthens the direct product in (11.3)(b) to
the full fixed-space decomposition needed by (5.11) in the proof of
(11.3)(h). That splitting, general
(11.3)(h)/(11.4), alpha selection and the complete profiles remain separate.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(a,b) and its proof, printed pp.168--171.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The actual two seed images are the full fixed spaces of their respective centers. -/
theorem source_rankOne_pair_fixed_spaces
    {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (π : ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b : Subgroup G) →* K)
    (hπ : Function.Surjective π)
    (hker : π.ker = (Q (family P) b).subgroupOf
      ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b))
    (σ : Representation (ZMod 2) K W)
    (s : BinaryConjugationSection ((Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b)
      (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b))
      (Z (family P) a ⊓ Z (family P) c) (σ.comp π)) :
    let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
    fixedSpace σ ⊤ = ⊥ ∧
      fixedSpace σ (((Z (family P) a).subgroupOf H).map π) =
        s.imageSpace (Z (family P) a ⊓ Q (family P) b) ∧
      fixedSpace σ (((Z (family P) c).subgroupOf H).map π) =
        s.imageSpace (Z (family P) c ⊓ Q (family P) b) := by
  let := finite_endpoints h
  let := source_center_elementary h a
  let := source_center_elementary h c
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  let E := Z (family P) a ⊓ Q (family P) b
  let F := Z (family P) c ⊓ Q (family P) b
  have hab := source_critical_one_adjacent hc hb
  have hZaH : Z (family P) a ≤ H := le_sup_left.trans le_sup_left
  have hZcH : Z (family P) c ≤ H := le_sup_right.trans le_sup_left
  have hgen : ((Z (family P) a).subgroupOf H).map π ⊔
      ((Z (family P) c).subgroupOf H).map π = ⊤ := by
    have ht : ((Z (family P) a).subgroupOf H ⊔ (Z (family P) c).subgroupOf H) ⊔
        (Q (family P) b).subgroupOf H = ⊤ := by
      rw [←subgroupOf_sup hZaH hZcH,←subgroupOf_sup (sup_le hZaH hZcH) le_sup_right]
      exact subgroupOf_self H
    have hm := congrArg (map π) ht
    have hk : π.ker.map π = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
    rw [Subgroup.map_sup,Subgroup.map_sup,←hker,hk,
      sup_bot_eq,map_top_of_surjective π hπ] at hm
    exact hm
  have hJV : J ≤ V := s.kernel_le
  have hJQ : J ≤ Q (family P) b := hJV.trans (pairSpan_le_core _ _ _)
  have hEF : J = E ⊓ F := le_antisymm
    (le_inf (le_inf inf_le_left hJQ) (le_inf inf_le_right hJQ))
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
  have hcompl := s.isCompl_imageSpace E F rfl hEF
  obtain ⟨g,hg,hga⟩ := source_rankOne_center_pair_moves h hB d hc hb hbc Mb
  let g₀ : H := ⟨g,mem_sup_left hg⟩
  have hHb : H ≤ stabilizer (family P) b := by
    apply sup_le (sup_le ?_ ?_) (Q_le_stabilizer _ b)
    · exact (((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U h a).2).trans ((ballKernel_one_le_edge _ hab).trans inf_le_right)
    · exact (((source_Z_Q_U h c).1.trans (map_subtype_le _)).trans
        (source_Z_Q_U h c).2).trans ((ballKernel_one_le_edge _ hbc.symm).trans inf_le_right)
  have hgb : g • b = b := hHb g₀.property
  have hconj : F = E.conjBy (g₀ : G) := by
    dsimp only [E,F,conjBy,g₀]
    rw [map_inf _ _ _ (MulAut.conj g).injective,←Z_translate,←Q_translate,hga,hgb]
  have hspace : s.imageSpace F = (s.imageSpace E).map (σ (π g₀)) := by
    rw [hconj,s.imageSpace_conjBy E (show E ≤ V from le_sup_left) g₀]
    rfl
  have hfix (z : Vertex (family P)) [IsElementaryAbelian 2 (Z (family P) z)] :
      s.imageSpace (Z (family P) z ⊓ Q (family P) b) ≤
        fixedSpace σ (((Z (family P) z).subgroupOf H).map π) := by
    have hz : ⁅Z (family P) z,Z (family P) z ⊓ Q (family P) b⁆ ≤ J :=
      (commutator_eq_bot_iff_le_centralizer.mpr
        ((le_centralizer_iff_isMulCommutative.mpr
          (inferInstance : IsMulCommutative (Z (family P) z))).trans
            (centralizer_le inf_le_left))).le.trans bot_le
    intro w hw t
    obtain ⟨u,hu,he⟩ := t.property
    change σ t.val w = w
    rw [←he]
    exact s.fixed_on_imageSpace_of_commutator_le _ _ hz u hu w hw
  exact complementary_conjugate_fixed_spaces σ _ _ _ _ (π g₀) hgen hcompl
    (hfix a) (hfix c) hspace

/-- Exact centralizer preimages in V/(Z_alpha intersect Z_gamma), including the whole center pair. -/
theorem source_rankOne_pair_fixed_preimages
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    let J := Z (family P) a ⊓ Z (family P) c
    ∀ x ∈ V,
      ((∀ t ∈ Z (family P) a, ⁅x,t⁆ ∈ J) ↔ x ∈ Z (family P) a ⊓ Q (family P) b) ∧
      ((∀ t ∈ Z (family P) c, ⁅x,t⁆ ∈ J) ↔ x ∈ Z (family P) c ⊓ Q (family P) b) ∧
      ((∀ t ∈ Z (family P) a ⊔ Z (family P) c, ⁅x,t⁆ ∈ J) ↔ x ∈ J) := by
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  obtain ⟨hJ,hE,hQ,σ,s,_,_,_,_⟩ := source_rankOne_pair_section h hB d hc hb hbc hac Ma Mb
  let := hJ
  let := hE
  let := hQ
  let π := QuotientGroup.mk' ((Q (family P) b).subgroupOf H)
  have hf := source_rankOne_pair_fixed_spaces h hB d hc hb hbc Mb π
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) σ s
  have hJQ : J ≤ Q (family P) b := s.kernel_le.trans (pairSpan_le_core _ _ _)
  have hfixed (z : Vertex (family P)) (hzH : Z (family P) z ≤ H)
      (hzV : Z (family P) z ⊓ Q (family P) b ≤ V)
      (hJz : J ≤ Z (family P) z)
      (hz : fixedSpace σ (((Z (family P) z).subgroupOf H).map π) =
        s.imageSpace (Z (family P) z ⊓ Q (family P) b))
      (x : V) :
      (∀ t ∈ Z (family P) z, ⁅(x : G),t⁆ ∈ J) ↔
        (x : G) ∈ Z (family P) z ⊓ Q (family P) b := by
    have he : (s.coordinates x).toAdd ∈
        fixedSpace σ (((Z (family P) z).subgroupOf H).map π) ↔
        ∀ t ∈ Z (family P) z, ⁅(x : G),t⁆ ∈ J := by
      constructor
      · intro hw t ht
        exact (s.fixed_coordinate_iff_commutator_mem ⟨t,hzH ht⟩ x).mp
          (hw ⟨π ⟨t,hzH ht⟩,⟨t,hzH ht⟩,ht,rfl⟩)
      · intro hx t
        obtain ⟨u,hu,he⟩ := t.property
        change σ t.val (s.coordinates x).toAdd = _
        rw [←he]
        exact (s.fixed_coordinate_iff_commutator_mem u x).mpr (hx u hu)
    rw [←he,hz,s.coordinates_mem_imageSpace_iff _ hzV,
      sup_eq_left.mpr (le_inf hJz hJQ)]
  dsimp only
  intro x hx
  let xV : V := ⟨x,hx⟩
  have ha := hfixed a (le_sup_left.trans le_sup_left) le_sup_left inf_le_left hf.2.1 xV
  have hc' := hfixed c (le_sup_right.trans le_sup_left) le_sup_right inf_le_right hf.2.2 xV
  refine ⟨ha,hc',?_⟩
  constructor
  · intro hall
    exact ⟨((ha.mp (fun t ht => hall t (mem_sup_left ht))).1),
      ((hc'.mp (fun t ht => hall t (mem_sup_right ht))).1)⟩
  · intro hxJ t ht
    have hcentral := (source_pair_core_normalizers h (source_critical_one_adjacent hc hb) hbc).1
    have hxD : x ∈ Q (family P) a ⊓ Q (family P) c :=
      ⟨((source_Z_Q_U h a).1.trans (map_subtype_le _)) hxJ.1,
        ((source_Z_Q_U h c).1.trans (map_subtype_le _)) hxJ.2⟩
    have he : x*t=t*x := mem_centralizer_iff.mp (hcentral ht) x hxD
    rw [commutatorElement_def,he,mul_inv_cancel_right,mul_inv_cancel]
    exact J.one_mem

/-- Each alpha core meets the literal pair span in its own seed, before row selection. -/
theorem source_rankOne_pair_core_seed_intersections
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
    Q (family P) a ⊓ V = Z (family P) a ⊓ Q (family P) b ∧
      Q (family P) c ⊓ V = Z (family P) c ⊓ Q (family P) b := by
  have hf := source_rankOne_pair_fixed_preimages h hB d hc hb hbc hac Ma Mb
  let V := pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)
  let J := Z (family P) a ⊓ Z (family P) c
  have hi (z : Vertex (family P)) (hzV : Z (family P) z ⊓ Q (family P) b ≤ V)
      (hfix : ∀ x ∈ V, (∀ t ∈ Z (family P) z, ⁅x,t⁆ ∈ J) ↔
        x ∈ Z (family P) z ⊓ Q (family P) b) :
      Q (family P) z ⊓ V = Z (family P) z ⊓ Q (family P) b := by
    apply le_antisymm ?_ (le_inf
      (inf_le_left.trans ((source_Z_Q_U h z).1.trans (map_subtype_le _))) hzV)
    intro x hx
    apply (hfix x hx.2).mp
    intro t ht
    have he : x*t=t*x := (mem_centralizer_iff.mp (source_core_centralizes_center h z hx.1) t ht).symm
    rw [commutatorElement_def,he,mul_inv_cancel_right,mul_inv_cancel]
    exact J.one_mem
  exact ⟨hi a le_sup_left (fun x hx => (hf x hx).1),
    hi c le_sup_right (fun x hx => (hf x hx).2.1)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
