module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.SeedCarrier
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.SourceGeometry
public import Theory.Representation.PSL3Two.SmallInvariantSubgroups

/-!
# Original source geometry for the natural MS sections

The original seed span places the moving four-group in [Z(O₂(K)),K] using
only two-perfection and the earlier source configuration. A subgroup of order
at most four invariant under the full natural or doubled-natural action is
trivial, so the original plane stabilizer is proper. Its Sylow image and a
factor three make it a parabolic. The moving line excludes the point
parabolic; relative normality and the two-group supplement put the line
parabolic residual inside the actual image of Lᵥ.

Thus both actual module models give C_U(Lᵥ)=C_U(K), without asserting that
the seed carrier equals U. This is the precise geometry consumed by the
nonshort alternatives of C.1.34 in 13.6.22. Model realization and the literal
checked-center identity are supplied separately by the MS family producer.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.22,
printed pp.932–933; C.1.34, printed pp.136–137.
-/

public section
open Subgroup Representation
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open BinaryRankTwo
variable {G A : Type*} [_root_.Group G] [Finite G] [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
  {L K V T U : Subgroup G} {v : G}
  {ρ : Representation (ZMod 2) BinaryLinearThree.Group A}

omit [Finite A] in
private theorem source_parabolic_proper
    (d : SourceLineData L K V T v)
    (m : ConjugationQuotientModel K (BinaryRankTwo.sourceU K) ρ)
    (hsmall : ∀ H : Subgroup (Multiplicative A), Nat.card H ≤ 4 →
      (∀ g : BinaryLinearThree.Group, ∀ x : H,
        Multiplicative.ofAdd (ρ g x.val.toAdd) ∈ H) → H = ⊥) :
    ((sourceP L K T v).subgroupOf K).map m.actor ≠ ⊤ := by
  intro htop
  let H := (⁅V, Lv L v⁆.subgroupOf (BinaryRankTwo.sourceU K)).map m.quotient
  have hc : Nat.card H ≤ 4 := by
    have he : Nat.card (⁅V, Lv L v⁆.subgroupOf (BinaryRankTwo.sourceU K)) = 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe d.line_le).toEquiv, d.line_card]
    exact (Nat.le_of_dvd Nat.card_pos ((⁅V, Lv L v⁆.subgroupOf (BinaryRankTwo.sourceU K)).card_map_dvd m.quotient)).trans he.le
  have hn : sourceP L K T v ≤ normalizer ((⁅V, Lv L v⁆ : Subgroup G) : Set G) :=
    (sup_le_sup_left inf_le_left _).trans d.line_invariant
  have hbot : H = ⊥ := hsmall H hc (fun g x =>
    line_image_invariant m hn ⟨g, htop.symm ▸ mem_top g⟩ x)
  have hline := line_eq_bot_of_image_fixed m d.lv_le d.line_le d.line_moved (fun a x => by
    have hx : m.quotient ⟨x, d.line_le x.property⟩ ∈ H :=
      mem_map_of_mem m.quotient x.property
    have hz : m.quotient ⟨x, d.line_le x.property⟩ = 1 := by
      have hb : m.quotient ⟨x, d.line_le x.property⟩ ∈ (⊥ : Subgroup (Multiplicative A)) := hbot ▸ hx
      exact hb
    change ρ _ (Multiplicative.toAdd _) = Multiplicative.toAdd _
    rw [hz]
    exact map_zero _)
  have hh := (eq_bot_iff_card _).mp hline
  rw [d.line_card] at hh
  omega

private theorem source_residual_marking
    (d : SourceLineData L K V T v)
    (m : ConjugationQuotientModel K (BinaryRankTwo.sourceU K) ρ)
    (hf : Function.Surjective m.actor) (hk : m.actor.ker = pCore 2 K)
    (hfull : ∀ H : Subgroup (Multiplicative A), Nat.card H ≤ 4 →
      (∀ g : BinaryLinearThree.Group, ∀ x : H,
        Multiplicative.ofAdd (ρ g x.val.toAdd) ∈ H) → H = ⊥)
    (hsmall : ∀ H : Subgroup (Multiplicative A), Nat.card H ≤ 4 →
      (∀ g : pointParabolicSL, ∀ x : H,
        Multiplicative.ofAdd (ρ g (Multiplicative.toAdd (x : Multiplicative A))) ∈ H) →
      ∀ g : pointParabolicSL, ∀ x : H,
        ρ g (Multiplicative.toAdd (x : Multiplicative A)) =
          Multiplicative.toAdd (x : Multiplicative A)) :
    ∃ g : BinaryLinearThree.Group,
      residual lineParabolicSL ≤ ((Lv L v).subgroupOf K).map (conjugate m g).actor := by
  obtain ⟨S, hS⟩ := SourceActors.exists_source_sylow d.normalizes_K d.sylow d.sylow_eq
  have hPK : sourceP L K T v ≤ K := sup_le d.lv_le inf_le_right
  have hDP : Lv L v ≤ sourceP L K T v := le_sup_left
  have hSP : ((S.mapSurjective hf : Sylow 2 BinaryLinearThree.Group) : Subgroup _) ≤
      ((sourceP L K T v).subgroupOf K).map m.actor := by
    rw [SourceActors.sylow_image m.actor hf S hS,
      sourceP, SourceActors.parabolic_image m.actor d.lv_le]
    exact le_sup_right
  have h3 := SourceActors.three_dvd_image m.actor d.lv_le
    (by rw [hk]; exact pCore_isPGroup) d.three_dvd
  have ht : ¬ IsPGroup 2 (((sourceP L K T v).subgroupOf K).map m.actor) := by
    intro ht
    have hd := h3.trans (Subgroup.card_dvd_of_le
      (map_mono (f := m.actor) (comap_mono hDP)))
    obtain ⟨n, hn⟩ := ht.exists_card_eq
    change 3 ∣ Nat.card (((sourceP L K T v).subgroupOf K).map m.actor) at hd
    rw [hn] at hd
    have hh := (by decide : Nat.Prime 3).dvd_of_dvd_pow hd
    norm_num at hh
  have hnorm : ((Lv L v).subgroupOf (sourceP L K T v)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le (Lv L v).le_normalizer
      (inf_le_left.trans d.normalizes_Lv))
  have hquot : let := hnorm; IsPGroup 2
      (sourceP L K T v ⧸ (Lv L v).subgroupOf (sourceP L K T v)) := by
    let := hnorm
    have hT : IsPGroup 2 T := by
      have he := d.sylow_eq
      have ht := d.sylow.isPGroup'.map (K ⊔ T).subtype
      rw [he, map_subgroupOf_eq_of_le (show T ≤ K ⊔ T from le_sup_right)] at ht
      exact ht
    apply isPGroup_quotient_of_sup_eq_top _ ((T ⊓ K).subgroupOf (sourceP L K T v))
      ((hT.to_le inf_le_left).comap_subtype)
    rw [← subgroupOf_sup hDP (show T ⊓ K ≤ sourceP L K T v from le_sup_right)]
    exact subgroupOf_self _
  obtain ⟨g, _, hg⟩ := exists_residual_marked_model m hPK hDP d.line_le
    d.line_moved d.line_card ((sup_le_sup_left inf_le_left _).trans d.line_invariant)
    (S.mapSurjective hf) hSP (source_parabolic_proper d m hfull) ht hsmall hnorm hquot
  exact ⟨g, hg⟩

/-- The natural center-commutator model supplies the original fixed-space comparison. -/
theorem natural_model_source_centralizer_eq
    (d : SourceLineData L K V T v)
    (m : ConjugationQuotientModel K (BinaryRankTwo.sourceU K) BinaryLinearThree.W)
    (hf : Function.Surjective m.actor) (hk : m.actor.ker = pCore 2 K) :
    BinaryRankTwo.sourceU K ⊓ centralizer (Lv L v : Set G) =
      BinaryRankTwo.sourceU K ⊓ centralizer (K : Set G) := by
  obtain ⟨g, hg⟩ := source_residual_marking d m hf hk
    BinaryLinearThree.natural_small_invariant_eq_bot point_invariant_small_fixed
  exact natural_centralizer_eq (conjugate m g) d.lv_le hg

/-- The doubled model uses one actor and needs no seed-carrier equality. -/
theorem doubled_model_source_centralizer_eq
    (d : SourceLineData L K V T v)
    (m : ConjugationQuotientModel K (BinaryRankTwo.sourceU K)
      (BinaryLinearThree.W.prod BinaryLinearThree.W))
    (hf : Function.Surjective m.actor) (hk : m.actor.ker = pCore 2 K) :
    BinaryRankTwo.sourceU K ⊓ centralizer (Lv L v : Set G) =
      BinaryRankTwo.sourceU K ⊓ centralizer (K : Set G) := by
  obtain ⟨g, hg⟩ := source_residual_marking d m hf hk
    BinaryLinearThree.doubled_small_invariant_eq_bot point_invariant_small_doubled_fixed
  exact doubled_centralizer_eq (conjugate m g) d.lv_le hg
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch

open Subgroup Representation Stellmacher
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open BinaryRankTwo A5Module ComponentSelection
open MSSourceModels.SeedCarrier
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {K L M V V₁ V₂ : Subgroup G}

/-- The nonshort source cases use the actual center commutator; only
 two-perfection is needed to place the original moving line in that carrier. -/
theorem center_sourceLineData_of_localConfiguration
    (d : FlagSource T L V V₁ V₂) (c : LocalConfiguration M d.flag)
    (hp : IsPPerfect 2 K)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Nonempty (SourceLineData L K V (Tv (T : Subgroup G) (markedV d.flag.module))
      (markedV d.flag.module)) := by
  let s := d.flag.module
  let T₀ := Tv (T : Subgroup G) (markedV s)
  have hSylow : CFSG.Quasithin.Chapter1.IsSylowIn 2 T₀ (Gv (markedV s)) :=
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  have hzmem := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp d.flag.z_central
  have hzT : markedZ s ∈ T₀ := ⟨hzmem.1, markedZ_mem_Gv s⟩
  have hzOmega : markedZ s ∈ omegaOneCenterAmbient T₀ :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hzT, hzmem.2.1, fun t ht => hzmem.2.2 t ht.1⟩
  let e : EarlierData K L (T : Subgroup G) (markedZ s) (markedV s) :=
    ⟨hK, hSylow, hn, hLK, hzOmega, hchar⟩
  have hline : ⁅V, Lv L (markedV s)⁆ ≤ BinaryRankTwo.sourceU K :=
    marked_line_le_sourceU s e hp
  have hL : T₀ ≤ normalizer (Lv L (markedV s) : Set G) :=
    AlternatingBranches.CoveredSix.Mv_normalizes_Lv hTL
  have hlineN : Lv L (markedV s) ⊔ T₀ ≤ normalizer
      ((⁅V, Lv L (markedV s)⁆ : Subgroup G) : Set G) := by
    refine sup_le (normalizer_commutator_ge_right _ _) ?_
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (d.T_normalizes ht.1),
      mem_normalizer_iff_map_conj_eq.mp (hL ht)]
  obtain ⟨S, hS⟩ := hSylow.restrict (show T₀ ≤ K ⊔ T₀ from le_sup_right)
    (sup_le hK.1.1 inf_le_right)
  have hS' : (S : Subgroup (K ⊔ T₀ : Subgroup G)) = T₀.subgroupOf (K ⊔ T₀) := by
    apply map_injective (K ⊔ T₀).subtype_injective
    rw [hS, map_subgroupOf_eq_of_le (show T₀ ≤ K ⊔ T₀ from le_sup_right)]
  refine ⟨{
    lv_le := hLK
    normalizes_K := hn
    normalizes_Lv := hL
    line_le := hline
    line_card := AlternatingBranches.CoveredSix.source_commutator_card s
    line_moved := AlternatingBranches.ExceptionalActors.moved_self_commutator s
    line_invariant := hlineN
    sylow := S
    sylow_eq := hS'
    three_dvd := ?_ }⟩
  rw [← c.residual_card]
  exact (pCore 2 (Lv L (markedV s))).card_quotient_dvd_card
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
