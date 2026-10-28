module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.MixedLocal.PairAction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.MixedLocal.Fixed

/-!
# Realized inputs to the mixed factor construction

This interface records the precise preceding facts consumed in the mixed
construction, together with the realized conjugation action and direct-product
fixed spaces. It does not redefine the source family or assert its realization.
The parent must construct these witnesses from 15.4.12 and 15.4.14.

The subgroup definitions retain `T_I=N_T(Y₂)`, `G_i=Y_i T_I`, their join `I`,
and `E₀=C_E(Y₁)∩C_E(Y₂)`. Conjugation transports the actual commutator-intersection
lines; the elementary Thompson subgroup lies in the Baumann subgroup; and `YT`
normalizes the first generated local group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the first three paragraphs of 15.4.18, printed p.1162.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.MixedLocal
open Subgroup
variable {G : Type*} [Group G]

noncomputable abbrev omega (T : Sylow 2 G) : Subgroup G := ChapterB.thompsonAlpha (T : Subgroup G)
noncomputable abbrev baum (T : Sylow 2 G) : Subgroup G := ChapterB.baumann (T : Subgroup G)
abbrev fixed (E Y : Subgroup G) : Subgroup G := E ⊓ centralizer (Y : Set G)
abbrev movedLine (E Y : Subgroup G) : Subgroup G := ⁅E, Y⁆ ⊓ E
abbrev stabilizer (T : Sylow 2 G) (L : Bool → Subgroup G) : Subgroup G :=
  (T : Subgroup G) ⊓ normalizer (L false : Set G)
abbrev firstGroup (T : Sylow 2 G) (Y : Subgroup G) (L : Bool → Subgroup G) : Subgroup G :=
  Y ⊔ stabilizer T L
abbrev secondGroup (T : Sylow 2 G) (L : Bool → Subgroup G) : Subgroup G :=
  L false ⊔ stabilizer T L
abbrev generated (T : Sylow 2 G) (Y : Subgroup G) (L : Bool → Subgroup G) : Subgroup G :=
  firstGroup T Y L ⊔ secondGroup T L
noncomputable abbrev commonFixed (T : Sylow 2 G) (Y : Subgroup G) (L : Bool → Subgroup G) : Subgroup G :=
  fixed (omega T) Y ⊓ fixed (omega T) (L false)

/-- Raw preceding witnesses and the realized factor action used in the first
three paragraphs of 15.4.18. The parent supplies these from 15.4.12 and 15.4.14.
There is no assumption here about `G_i/O₂(G_i)`, the mixed Sylow subgroup,
its index, the order of `E`, the common fixed subgroup, or the intersection. -/
structure RealizedFactors [Finite G] (T : Sylow 2 G) (Y X M₁ M₂ : Subgroup G)
    (L : Bool → Subgroup G) where
  maximal₁ : IsMaximalTwoLocal M₁
  maximal₂ : IsMaximalTwoLocal M₂
  different : M₁ ≠ M₂
  sylow_le₁ : (T : Subgroup G) ≤ M₁
  sylow_le₂ : (T : Subgroup G) ≤ M₂
  normalizer₁ : M₁ = normalizer (Y : Set G)
  normalizer₂ : M₂ = normalizer (X : Set G)
  unique₁ : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₁
  unique₂ : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₂
  product : L false ⊔ L true = X
  pairAction : FactorPairAction M₂ L
  swapper : G
  swapper_mem : swapper ∈ (T : Subgroup G)
  swapper_moves : swapper ∉ normalizer (L false : Set G)
  baumann_invariant : baum T ≤ normalizer (L false : Set G)
  thompson_commutator₁ : ⁅Y, ChapterB.thompsonJ (T : Subgroup G) 0⁆ = Y
  thompson_commutator₂ : ⁅L false, ChapterB.thompsonJ (T : Subgroup G) 0⁆ = L false
  factor_core_index₁ : (pCore 2 Y).index = 3
  factor_core_index₂ : (pCore 2 (L false)).index = 3
  earlierSylow₁ : Sylow 2 (Y ⊔ baum T : Subgroup G)
  earlierSylow₁_image : (earlierSylow₁ : Subgroup (Y ⊔ baum T : Subgroup G)).map
    (Y ⊔ baum T : Subgroup G).subtype = baum T
  earlierSylowX : Sylow 2 (X ⊔ baum T : Subgroup G)
  earlierSylowX_image : (earlierSylowX : Subgroup (X ⊔ baum T : Subgroup G)).map
    (X ⊔ baum T : Subgroup G).subtype = baum T
  single_split₁ : fixed (omega T) Y ⊔ movedLine (omega T) Y = omega T
  single_disjoint₁ : Disjoint (fixed (omega T) Y) (movedLine (omega T) Y)
  single_card₁ : Nat.card (movedLine (omega T) Y) = 2
  single_split₂ : fixed (omega T) (L false) ⊔ movedLine (omega T) (L false) = omega T
  single_disjoint₂ : Disjoint (fixed (omega T) (L false)) (movedLine (omega T) (L false))
  single_card₂ : Nat.card (movedLine (omega T) (L false)) = 2
  double_split : fixed (omega T) X ⊔
    (movedLine (omega T) (L false) ⊔ movedLine (omega T) (L true)) = omega T
  double_disjoint : Disjoint (fixed (omega T) X)
    (movedLine (omega T) (L false) ⊔ movedLine (omega T) (L true))
  lines_disjoint : Disjoint (movedLine (omega T) (L false)) (movedLine (omega T) (L true))
  central_fixed_card : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
    centralizer (X : Set G) : Subgroup G) = 2

/-- Conjugation transports the actual commutator-intersection line. -/
theorem map_movedLine {E Y Y' : Subgroup G} {t : G}
    (hE : t ∈ normalizer (E : Set G))
    (hY : Y.map (MulAut.conj t).toMonoidHom = Y') :
    (movedLine E Y).map (MulAut.conj t).toMonoidHom = movedLine E Y' := by
  have he : E.map (MulAut.conj t).toMonoidHom = E := mem_normalizer_iff_map_conj_eq.mp hE
  change (⁅E, Y⁆ ⊓ E).map (MulAut.conj t).toMonoidHom = _
  rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, map_commutator, he, hY]

theorem normalizes_movedLine {E Y U : Subgroup G}
    (hE : U ≤ normalizer (E : Set G)) (hY : U ≤ normalizer (Y : Set G)) :
    U ≤ normalizer (movedLine E Y : Set G) := by
  intro u hu
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact map_movedLine (hE hu) (mem_normalizer_iff_map_conj_eq.mp (hY hu))

/-- The elementary Thompson subgroup lies in the Baumann subgroup because
its omega center is central in it. -/
theorem thompson_le_baumann [Finite G] (T : Subgroup G) : ChapterB.thompsonJ T 0 ≤ ChapterB.baumann T := by
  rw [ChapterB.thompsonJ_zero]
  refine le_inf (sSup_le fun _ hA => hA.1) ?_
  intro j hj e he
  exact (((Stellmacher.mem_omegaOneCenterAmbient_iff _ e).mp he).2.2 j hj).symm

/-- The first generated local group is normalized by `YT`. Only the factor
stabilizer is required to be normal in `T`. -/
theorem firstGroup_normalized {T : Sylow 2 G} {Y M : Subgroup G} {L : Bool → Subgroup G}
    (a : FactorPairAction M L) (hTM : (T : Subgroup G) ≤ M)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    Y ⊔ (T : Subgroup G) ≤ normalizer (firstGroup T Y L : Set G) := by
  apply sup_le (le_sup_left.trans (firstGroup T Y L).le_normalizer)
  exact (le_inf hTY ((a.restrict hTM).normalizes_stabilizer)).trans
    (normalizer_inf_normalizer_le_normalizer_sup Y (stabilizer T L))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.MixedLocal
