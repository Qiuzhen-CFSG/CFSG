module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource

/-!
# Source parabolic reduction to degree four

Starting with the prescribed K/O₂(K) ≃ PSLₙ(2), 3 ≤ n ≤ 5, the genuine
ordinary or covered natural action of §13.2 determines the source residuals
of Notation 13.2.1. The earlier component conclusions are relative to H;
all starred subgroups use the literal H/O₂(H) quotient.

In the ordinary case, the constructed single-node flag excludes degree three
by the full automorphism-group clause of 13.8.21(3). In degree five its
nonadjacent-node enlargement has solvable S₃ × S₃ quotient; 13.8.13 and
the theta identity of 13.7.3(9) give the contradiction. In degree four an
inner supplement produces an actual local component in Hz with PSL₃(2)
quotient, so the same degree-three argument excludes it. The remaining
outer action is the middle-node S₈ extension, compatible with the supplied
component marking.

In the covered case the actual E₉ quotient excludes degree three. Individual
invariance of the two constructed nodes forces T* ≤ K*. Their residual
normalizer recovers H∩M = L₁T in the original group. In degree five the
source normalizer restriction selects the strictly larger parabolic with
S₃ × PSL₃(2) quotient, contradicting uniform 13.8.21(1). Degree four retains
the ordered end nodes and their original residual markings.

The main theorem takes only the earlier natural-action data, literal residual
identities and the used clauses of 13.8.13 and 13.8.21. It does not assume
strict critical denominators: its proof applies to both cases of 13.8.8,
including the transvection case (1). Thus no case is discarded and no extra
case-(2) hypothesis is imposed. The representation-theoretic conclusions
13.8.22–24 are not needed for this stronger, uniform parabolic implication.
The orthogonal exclusion, the natural-module conclusion and H = G₁ remain
separate downstream arguments.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed pp.959–960 (PDF pp.976–977), using Notation 13.2.1,
13.2.2(3),(9), 13.7.3(9), 13.8.13 and 13.8.21(1),(3).
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics
open Chapter1
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

/-- The actual ordinary source flag contradicts the complete degree-three
automorphism-group conclusion of 13.8.21(3). -/
theorem exclude_three_ordinary (H K L T V V₁ : Subgroup G)
    (d : OrdinarySource.NaturalSetup L T V V₁)
    (hKH : K ≤ H) (hLK : one L T V₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (e : (K ⧸ pCore 2 K) ≃* PSL 3)
    (hAut : Nonempty (Source.Hstar H ≃* MulAut Matrix.PSL3Two.PSL)) : False := by
  obtain ⟨b, i, hP, _, hn, _⟩ := OrdinarySource.source_deleted_basis_flag
    H K L (one L T V₁) T V V₁ d hKH hLK hK hKn hT rfl
    (by decide : 2 ≤ 2) (by decide : 2 ≤ 4) e
  exact exclude_three_source_deletedFlag H K T hKH (isSylowIn_iff.mp hT).2.1
    hK hKn (isSylowIn_iff.mp hT).1 hKT e hAut b i _ hP hn

/-- The adjacent-node component is constructed inside K and its overgroup
belongs to Hz. Applying the degree-three exclusion to that actual overgroup
rules out T* ≤ K*, without inferring T ≤ K from its starred image. -/
theorem exclude_four_inner_ordinary (H K L T V V₁ G₁ M : Subgroup G)
    (d : OrdinarySource.NaturalSetup L T V V₁)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hLK : one L T V₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (htheta : one L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (e : (K ⧸ pCore 2 K) ≃* PSL 4)
    (hs : Source.starImage H T ≤ Source.starImage H K)
    (hAut : ∀ (Y D : Subgroup G), Y ∈ Source.Hz (one L T V₁) T G₁ M → D ≤ Y →
      (D.subgroupOf Y).IsCComponent → Nonempty ((D ⧸ pCore 2 D) ≃* PSL 3) →
      Nonempty (Source.Hstar Y ≃* MulAut Matrix.PSL3Two.PSL)) : False := by
  obtain ⟨b, i, _, _, _, D, _, _, _, _, _, K₁, _, hK₁K, hLK₁, hn, _, hc, hY, _, eK, _⟩ :=
    OrdinarySource.exists_four_source_local_component H K L (one L T V₁) T V V₁ G₁ M d
      hH hKH hLK hK hKn hT hKT rfl htheta e hs
  have hYH : K₁ ⊔ T ≤ H := sup_le (hK₁K.trans hKH) (isSylowIn_iff.mp hT).2.1
  have hnormal : (K₁.subgroupOf (K₁ ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le K₁.le_normalizer hn)
  exact exclude_three_ordinary (K₁ ⊔ T) K₁ L T V V₁ d le_sup_left hLK₁ hc hnormal
    (hT.restrict le_sup_right hYH) rfl eK
    (hAut (K₁ ⊔ T) K₁ hY le_sup_left hc ⟨eK⟩)

/-- The ordinary alternative retains the actual node, its two-residual,
the component Sylow flag and the compatible action on eight letters. -/
def MiddleNodeMarking (H K L₁ T : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (e : (K ⧸ pCore 2 K) ≃* PSL 4) : Prop :=
  ∃ (b : Basis 3) (i : Fin 3),
    i.val + 1 = 2 ∧
    OrdinarySource.sourceNode H K L₁ T =
      ambientFlagStabilizer (starLinearEquiv H K hKH hK e) (deletedFlag (by decide) b i) ∧
    ((Source.starImage H T ⊓ Source.starImage H K).subgroupOf (Source.starImage H K)).map
      (linearModel (starLinearEquiv H K hKH hK e)).toMonoidHom = cutStabilizer b Set.univ ∧
    Source.starImage H T ≤ normalizer (OrdinarySource.sourceNode H K L₁ T : Set _) ∧
    (pResidual 2 (OrdinarySource.sourceNode H K L₁ T)).map
      (OrdinarySource.sourceNode H K L₁ T).subtype = Source.starImage H L₁ ∧
    Source.starImage H T ⊓ Source.starImage H K < Source.starImage H T ∧
    ∃ E : Source.Hstar H ≃* Equiv.Perm (Fin 8),
      (∀ k : K, E (QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩) =
        (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
          (e (QuotientGroup.mk' (pCore 2 K) k)) : Equiv.Perm (Fin 8))) ∧
      (Source.starImage H K).map E.toMonoidHom = alternatingGroup (Fin 8) ∧
      (OrdinarySource.sourceNode H K L₁ T).map E.toMonoidHom =
        (flagStabilizer (starLinearEquiv H K hKH hK e) (deletedFlag (by decide) b i)).map
          ((alternatingGroup (Fin 8)).subtype.comp
            ((starLinearEquiv H K hKH hK e).trans
              Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).toMonoidHom)

/-- The ordinary A₆ case reduces to the marked outer degree-four action.
Both lower-rank contradictions discharge their own source flag inputs. -/
theorem ordinary_source_reduction (H K L T V V₁ G₁ M : Subgroup G)
    (d : OrdinarySource.NaturalSetup L T V V₁)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hLK : one L T V₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (htheta : one L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, one L T V₁ ⊔ T ≤ J → J ≤ G₁ → Group.IsSolvable J → J ≤ M)
    (hAut : ∀ (Y D : Subgroup G), Y ∈ Source.Hz (one L T V₁) T G₁ M → D ≤ Y →
      (D.subgroupOf Y).IsCComponent → Nonempty ((D ⧸ pCore 2 D) ≃* PSL 3) →
      Nonempty (Source.Hstar Y ≃* MulAut Matrix.PSL3Two.PSL))
    {n : ℕ} (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5) (e : (K ⧸ pCore 2 K) ≃* PSL n) :
    ∃ hn : n = 4, MiddleNodeMarking H K (one L T V₁) T hKH hK (hn ▸ e) := by
  have hTH := (isSylowIn_iff.mp hT).2.1
  have ht := (isSylowIn_iff.mp hT).1
  have hcases : n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact (exclude_three_ordinary H K L T V V₁ d hKH hLK hK hKn hT hKT e
      (hAut H K hH hKH hK ⟨e⟩)).elim
  · have hs : ¬ Source.starImage H T ≤ Source.starImage H K := by
      intro hs
      exact exclude_four_inner_ordinary H K L T V V₁ G₁ M d hH hKH hLK hK hKn hT hKT
        htheta e hs hAut
    obtain ⟨b, i, hP, hS, hn, hR⟩ := OrdinarySource.source_deleted_basis_flag
      H K L (one L T V₁) T V V₁ d hKH hLK hK hKn hT rfl (by decide) (by decide) e
    obtain ⟨hi, hlt, E, hE, hKimage, hPimage⟩ := source_middleNode_marking
      H K T hKH hTH hK hKn ht hKT e b i _ hP hn hs
    exact ⟨rfl, b, i, hi, hP, hS, hn, hR, hlt, E, hE, hKimage, hPimage⟩
  · obtain ⟨b, i, hP, _, hn, _⟩ := OrdinarySource.source_deleted_basis_flag
      H K L (one L T V₁) T V V₁ d hKH hLK hK hKn hT rfl (by decide) (by decide) e
    have hs : Source.starImage H T ≤ Source.starImage H K := by
      rcases source_deletedFlag_alternative H K T hKH hTH hK hKn ht hKT
        (by decide) (by decide) e b i _ hP hn with hs | hn
      · exact hs
      · omega
    obtain ⟨c, j, hbase, hresidual, _⟩ := OrdinarySource.five_source_markings
      H K L (one L T V₁) T V V₁ d hKH hLK hK hKn hT hKT rfl e hs
    exact (exclude_five_single_node (one L T V₁) T G₁ M H hH
      (OrdinarySource.wholeLinearModel H K T hKH hTH hK hKT hs e)
      c j hbase hresidual htheta h13).elim

/-- The covered alternative retains the ordered endpoint residuals in one
basis under the extension of the original component marking. -/
def EndNodeMarking (H K M L T V₁ : Subgroup G) (hKH : K ≤ H) (hTH : T ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hKT : K ⊔ T = H)
    (e : (K ⧸ pCore 2 K) ≃* PSL 4) : Prop :=
  ∃ (hs : Source.starImage H T ≤ Source.starImage H K)
    (b : Basis 3) (beta delta : Fin 3),
    ((beta = 0 ∧ delta = 2) ∨ (beta = 2 ∧ delta = 0)) ∧
    let eH := CoverSource.wholeLinearModel H K T hKH hTH hK hKT hs e
    (Source.starImage H (one L T V₁ ⊔ T)).map eH.toMonoidHom = fourParabolic b {beta, delta} ∧
    (Source.starImage H (zero L)).map eH.toMonoidHom = fourNodeResidual b beta ∧
    (Source.starImage H (plus L T V₁)).map eH.toMonoidHom = fourNodeResidual b delta ∧
    (Source.starImage H T).map eH.toMonoidHom = cutStabilizer b Set.univ ∧
    H ⊓ M = one L T V₁ ⊔ T ∧
    normalizer (Source.starImage H (zero L) : Set (Source.Hstar H)) ≤
      normalizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)) ∧
    plus L T V₁ ≤ one L T V₁ ∧ Source.QH H ≤ T ∧
    Module.finrank (ZMod 2) (cutSpace b 1) = 2

/-- The triple-cover case has degree four with the two ordered end nodes.
The rank-two quotient and the strict degree-five overgroup are constructed
by the source-placement and Levi results, not assumed here. -/
theorem covered_source_reduction (H K G₁ M L T V V₁ V₃ : Subgroup G)
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hTH : T ≤ H) (hLK : one L T V₁ ≤ K)
    (hLM : one L T V₁ ≤ M) (hTM : T ≤ M)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (hT : IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hrel : ((one L T V₁).subgroupOf (H ⊓ M)).Normal)
    (hNM : normalizer (zero L : Set G) ≤ M)
    (h21 : ∀ (Y D : Subgroup G), Y ∈ Source.Hz (one L T V₁) T G₁ M → D ≤ Y →
      (D.subgroupOf Y).IsCComponent → one L T V₁ ≤ D)
    {n : ℕ} (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5) (e : (K ⧸ pCore 2 K) ≃* PSL n) :
    ∃ hn : n = 4, EndNodeMarking H K M L T V₁ hKH hTH hK hKT (hn ▸ e) := by
  obtain ⟨S, hS⟩ := hT
  have hS' : (S : Subgroup H) = T.subgroupOf H := by
    rw [← hS, Subgroup.subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  have hn := CoverSource.dimension_at_least_four H K L T V V₁ V₃ d hKH hLK hK
    hcover hfactor hn₀ e
  have hn4 : n = 4 := by
    by_contra hn4
    have : n = 5 := by omega
    subst n
    exact CoverSource.exclude_five_source H K G₁ M L T V V₁ V₃ d hH hKH hLK hLM hTM
      hK hKn hKT hcover hfactor S hS' hrel hNM e h21
  subst n
  obtain ⟨hs, b, beta, delta, _, _, hbase, hzero, hplus, hflag, hinter, hn, hp, hc, hend, hd⟩ :=
    CoverSource.four_source_markings H K M L T V V₁ V₃ d hKH hTH hLK hLM hTM hK hKn hKT
      hcover hfactor S hS' hrel hNM e
  exact ⟨rfl, hs, b, beta, delta, hend, hbase, hzero, hplus, hflag, hinter, hn, hp, hc, hd⟩

/-- Parabolic reduction from the genuine earlier local action and chapter
conclusions. No choice of either critical-denominator case is required. -/
theorem source_parabolic_reduction (H K L L₁ T V V₁ V₃ G₁ M : Subgroup G)
    (hdef : L₁ = one L T V₁)
    (hlocal : Nonempty (OrdinarySource.NaturalSetup L T V V₁) ∨
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
        Nonempty (LocalAction.NaturalSetup L T V V₁ V₃)))
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hM : L ⊔ T ≤ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hT : IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (hrel : (L₁.subgroupOf (H ⊓ M)).Normal)
    (hfactor : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      one L T V₁ = plus L T V₁ ⊔ zero L)
    (hNM : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) → normalizer (zero L : Set G) ≤ M)
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ → Group.IsSolvable J → J ≤ M)
    (h21 : ∀ (Y D : Subgroup G), Y ∈ Source.Hz L₁ T G₁ M → D ≤ Y →
      (D.subgroupOf Y).IsCComponent → L₁ ≤ D)
    (hAut : ∀ (Y D : Subgroup G), Y ∈ Source.Hz L₁ T G₁ M → D ≤ Y →
      (D.subgroupOf Y).IsCComponent → Nonempty ((D ⧸ pCore 2 D) ≃* PSL 3) →
      Nonempty (Source.Hstar Y ≃* MulAut Matrix.PSL3Two.PSL))
    {n : ℕ} (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5) (e : (K ⧸ pCore 2 K) ≃* PSL n) :
    ∃ hn : n = 4,
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
        Nonempty (Source.Hstar H ≃* PSL 4) ∧
        Source.starImage H T ⊓ Source.starImage H K = Source.starImage H T ∧
        EndNodeMarking H K M L T V₁ hKH (isSylowIn_iff.mp hT).2.1 hK hKT (hn ▸ e)) ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        MiddleNodeMarking H K L₁ T hKH hK (hn ▸ e)) := by
  subst L₁
  have hLK := h21 H K hH hKH hK
  rcases hlocal with hd | ⟨hc, hd⟩
  · obtain ⟨d⟩ := hd
    obtain ⟨hn, hmark⟩ := ordinary_source_reduction H K L T V V₁ G₁ M d hH hKH hLK hK
      hKn hT hKT htheta h13 hAut hn₀ hn₁ e
    exact ⟨hn, Or.inr ⟨⟨d.model⟩, hmark⟩⟩
  · obtain ⟨d⟩ := hd
    obtain ⟨hn, hmark⟩ := covered_source_reduction H K G₁ M L T V V₁ V₃ d hH hKH
      (isSylowIn_iff.mp hT).2.1 hLK ((one_le L T V₁).trans (inf_le_left.trans hM))
      (le_sup_right.trans hM) hK hKn hT hKT hc (hfactor hc) hrel (hNM hc) h21 hn₀ hn₁ e
    have hmark_copy := hmark
    obtain ⟨hs, _⟩ := hmark_copy
    exact ⟨hn, Or.inl ⟨hc,
      ⟨wholeStarLinearEquiv H K T hKH (isSylowIn_iff.mp hT).2.1 hK hKT hs (hn ▸ e)⟩,
      inf_eq_left.mpr hs, hmark⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
