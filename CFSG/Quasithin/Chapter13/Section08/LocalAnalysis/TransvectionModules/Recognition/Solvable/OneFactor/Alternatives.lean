module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.OneFactor.SimpleNatural
public import Theory.GroupTheory.NormalSymmetricThreeMarked


/-!
# Exhaustive one-factor alternatives for the solvable transvection closure

For the ordinary A₆ flag, T-invariance passes to an actual Sylow subgroup
of H/O₂(H). The normal-S₃ theorem and |L₁|₃ = 3 give L₁* = O²(K*)
or pointwise commutation. The equality lifts through the normalizing
two-kernel to O²(K) = L₁. Its marked natural action generates V₃/V₁;
the natural one-factor module has dimension two, identifying the moved space.

For the actual hexacode triple cover, the marked elementary-nine quotient
and the ambient three-rank bound force O²(K*) ≤ L₁*. The existing covered
lifting and invariant-line calculation then gives O²(K) = L₀ or L₁,+;
the latter's proved flag action again gives the literal moved-space equality.
No residual placement or moved-space conclusion is assumed.

The final entry point uses the actual normal closure, source Hz family,
and compatible natural models. The earlier universal identity 13.2.2(3)
remains explicit and is applied to the actual covered flag. The Solvable
parent owns its earlier-source inputs and the subsequent contradiction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.5, printed pp.947–948 (PDF pp.964–965), and
Notation 13.2.1 and 13.2.2(3), printed p.877.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor
variable {G : Type*} [Group G] [Finite G]

private theorem star_sylow_normalizes (H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (Y : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    ∃ S : Sylow 2 (Source.Hstar H), (S : Subgroup (Source.Hstar H)) = Source.starImage H T ∧
      (S : Subgroup (Source.Hstar H)) ≤ normalizer (Source.starImage H Y : Set (Source.Hstar H)) := by
  let S := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have he : (S : Subgroup (Source.Hstar H)) = Source.starImage H T := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
    rfl
  refine ⟨S, he, ?_⟩
  rw [he]
  exact ((map_mono ((comap_mono hn).trans (Y.le_normalizer_comap H.subtype))).trans
    ((Y.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H))))

private theorem star_one_perfect (H L T V₁ : Subgroup G) (hLH : one L T V₁ ≤ H) :
    IsPPerfect 2 (Source.starImage H (one L T V₁)) :=
  (isPPerfect_embedded_pResidual 2 _).of_surjective
    (starMap H (one L T V₁) hLH) (starMap_surjective H (one L T V₁) hLH)

/-- In the simple case the marked subgroup has three-part three, and its
star image equals the residual of K* or commutes pointwise with K*. -/
theorem simple_star_alternatives {T : Sylow 2 G} {H L V V₁ V₂ V₃ : Subgroup G}
    (d : TransvectionParabolic.EarlierCore.ComponentSetup T L V V₁ V₂ V₃)
    (hLH : one L T V₁ ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (K : Subgroup (Source.Hstar H)) [K.Normal] (e : K ≃* Equiv.Perm (Fin 3)) :
    3 ^ (Nat.card (one L T V₁)).factorization 3 = 3 ∧
      (Source.starImage H (one L T V₁) = (pResidual 2 K).map K.subtype ∨
        ∀ l ∈ Source.starImage H (one L T V₁), ∀ k ∈ K, Commute l k) := by
  refine ⟨simple_natural_threePart d.extend, ?_⟩
  obtain ⟨S, _, hn⟩ := star_sylow_normalizes H T hTH (one L T V₁)
    (T_normalizes_one L T V₁ d.line_stable)
  obtain ⟨n, hncard⟩ := (simple_natural_order_data d.extend).2
  have hd : Nat.card (Source.starImage H (one L T V₁)) ∣ 3 * 2 ^ n :=
    (card_dvd_of_surjective (starMap H (one L T V₁) hLH)
      (starMap_surjective H (one L T V₁) hLH)).trans hncard
  rcases Theory.GroupTheory.NormalSymmetricThreeMarked.eq_residual_or_centralizes_of_card_dvd
    K e S (Source.starImage H (one L T V₁)) (star_one_perfect H L T V₁ hLH) hn
    ⟨n, hd⟩ with he | hcomm
  · exact Or.inl he
  · exact Or.inr (fun l hl k hk => (hcomm hl k hk).symm)

/-- The covered marked subgroup contains O²(K*) by its genuine three-rank.
No placement premise or ambient normality of L₁ is assumed. -/
theorem covered_residual_image_le {T : Sylow 2 G} {H L V V₁ V₃ : Subgroup G}
    (d : NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hLH : one L T V₁ ≤ H) (hrank : primeRank 3 H ≤ 2)
    (K : Subgroup (Source.Hstar H)) [K.Normal] (e : K ≃* Equiv.Perm (Fin 3)) :
    (pResidual 2 K).map K.subtype ≤ Source.starImage H (one L T V₁) := by
  apply Theory.GroupTheory.NormalSymmetricThreeMarked.residual_le_of_rank K e
    (Source.starImage H (one L T V₁)) (star_one_perfect H L T V₁ hLH)
  · exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 H)
      pCore_isPGroup).trans hrank
  · exact covered_star_threeRank_ge_two (G := G) (H := H) (L := L) (V := V)
      (V₁ := V₁) (V₃ := V₃) (T : Subgroup G) d hfactor hLH

variable {H L V V₁ V₂ V₃ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Equality of star residuals lifts to the actual preimage residual.
The natural marked flag, not a moved-space premise, then gives Ũ_K = Ṽ₃. -/
theorem simple_alternatives (T : Sylow 2 G)
    (d : TransvectionParabolic.EarlierCore.ComponentSetup T L V V₁ V₂ V₃)
    (hLH : one L T V₁ ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (K : Subgroup (Source.Hstar H)) [K.Normal]
    (factors : ChapterB.SolvableFFFactors (ρ.comp K.subtype))
    (hJ : offenderSubgroup (ρ.comp K.subtype) = ⊤) (hc : factors.count = 1) :
    (∀ l ∈ Source.starImage H (one L T V₁), ∀ k ∈ K, Commute l k) ∨
      (preimageResidual H K = one L T V₁ ∧
        subspaceCommutator ρ ⊤ K = seedSpace H V₃ V₁) := by
  let n := naturalTwo_of_count_one K factors hJ hc
  let e := n.groupEquiv.trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
  rcases (simple_star_alternatives d hLH hTH K e).2 with he | hcomm
  · right
    have hres := preimageResidual_eq_of_image_of_sourceSylow H T hTH K (one L T V₁) hLH
      (isPPerfect_embedded_pResidual 2 _) (T_normalizes_one L T V₁ d.line_stable) he
    refine ⟨hres, ?_⟩
    apply movedSpace_eq_seedSpace_of_residual ρ hρ
      (d.extend.line_le_plane.trans d.extend.plane_le_seed)
      d.extend.flag_orders.1 d.extend.flag_orders.2.2 K factors hJ hc _ hres
    change V₃ ≤ ⁅V₃, TransvectionParabolic.EarlierCore.residual
      ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G))⁆ ⊔ V₁
    rw [d.extend.line_residual_eq]
    exact d.extend.seed_eq_commutator_sup_line.le
  · exact Or.inl hcomm

/-- The covered branch is exhaustive: residual placement is now proved.
The actual triple-cover witness is retained in the L₀ case. -/
theorem covered_alternatives (T : Sylow 2 G)
    (d : NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hLH : one L T V₁ ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hrank : primeRank 3 H ≤ 2) (h₁ : Nat.card V₁ = 2) (h₃ : Nat.card V₃ = 8)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (K : Subgroup (Source.Hstar H)) [K.Normal]
    (factors : ChapterB.SolvableFFFactors (ρ.comp K.subtype))
    (hJ : offenderSubgroup (ρ.comp K.subtype) = ⊤) (hc : factors.count = 1) :
    (preimageResidual H K = zero L ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) ∨
    (preimageResidual H K = plus L T V₁ ∧
      subspaceCommutator ρ ⊤ K = seedSpace H V₃ V₁) := by
  let n := naturalTwo_of_count_one K factors hJ hc
  let e := n.groupEquiv.trans (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
  exact covered_alternatives_of_residual_image_le T d hfactor hLH hTH h₁ h₃ ρ hρ K factors hJ hc
    (covered_residual_image_le d hfactor hLH hrank K e)

/-- The one-factor source branch, with the actual transvection normal closure.
The only earlier universal group identity retained is 13.2.2(3), applied to
the actual covered natural flag. All residual placements, lifts, and moved
spaces are derived. The standing counterexample hypotheses are used only
through the displayed marked models, Hz membership and odd-rank bound. -/
theorem source_one_factor_alternatives (T : Sylow 2 G) (G₁ M : Subgroup G)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hmodels : Nonempty (TransvectionParabolic.EarlierCore.ComponentSetup T L V V₁ V₂ V₃) ∨
      Nonempty (NaturalSetup L (T : Subgroup G) V V₁ V₃))
    (earlier1322 : ∀ (W₁ W₃ : Subgroup G), NaturalSetup L (T : Subgroup G) V W₁ W₃ →
      one L T W₁ = plus L T W₁ ⊔ zero L)
    (hrank : primeRank 3 H ≤ 2) (h₁ : Nat.card V₁ = 2) (h₃ : Nat.card V₃ = 8)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (t : Source.Hstar H)
    (_ht : IsTransvection ρ t)
    (factors : ChapterB.SolvableFFFactors (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype) = ⊤)
    (hc : factors.count = 1) :
    let K := normalClosure ({t} : Set (Source.Hstar H))
    (∀ l ∈ Source.starImage H (one L T V₁), ∀ k ∈ K, Commute l k) ∨
      (preimageResidual H K = zero L ∧
        Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) ∨
      ((preimageResidual H K = one L T V₁ ∨ preimageResidual H K = plus L T V₁) ∧
        subspaceCommutator ρ ⊤ K = seedSpace H V₃ V₁) := by
  have hLH : one L T V₁ ≤ H := le_sup_left.trans hH.1.2
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  let K := normalClosure ({t} : Set (Source.Hstar H))
  rcases hmodels with hs | hs
  · obtain ⟨d⟩ := hs
    rcases simple_alternatives T d hLH hTH ρ hρ K factors hJ hc with hcomm | ⟨hres, hmove⟩
    · exact Or.inl hcomm
    · exact Or.inr (Or.inr ⟨Or.inl hres, hmove⟩)
  · obtain ⟨d⟩ := hs
    rcases covered_alternatives T d (earlier1322 V₁ V₃ d) hLH hTH hrank h₁ h₃
      ρ hρ K factors hJ hc with hzero | ⟨hres, hmove⟩
    · exact Or.inr (Or.inl hzero)
    · exact Or.inr (Or.inr ⟨Or.inr hres, hmove⟩)
end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.OneFactor

end
