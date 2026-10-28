module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.LongRoot.Onan
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.Residual
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.SolvableResidual

/-!
# Intrinsic normalizers for the long-root construction

Put `D = C_L(X)` and form `[N_L(D),D]`. In the source root cases the model
calculation identifies D with the root group, or its full inverse image in
the nontrivial cover, and identifies this commutator with Z. These
identifications remain separate obligations: the definition alone is not a
root-subgroup theorem.

The intrinsic construction is preserved by every element normalizing L and
X. Tight embedding therefore makes the stabilizer of T_C normalize its
relative root normalizer. The source transport constructs a mover in the
actual acting group. Finally T_C ≤ X forces a nontrivial component center,
without assuming a covered model or ambient normality of L.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
Lemma 16.5.13, printed pp.1201--1202.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.Construction
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- N_L(Z), embedded in G; no ambient normality of L is intended. -/
def relativeNormalizer (L Z : Subgroup G) : Subgroup G :=
  L ⊓ normalizer (Z : Set G)

/-- The intrinsic candidate which the root-model calculations must identify
with the genuine root subgroup (including the commutator lift in 2.G₂(4)). -/
def residualRoot (L X : Subgroup G) : Subgroup G :=
  ⁅relativeNormalizer L (L ⊓ centralizer (X : Set G)),
    L ⊓ centralizer (X : Set G)⁆

/-- Relative normalizers commute with actual ambient isomorphisms. -/
theorem relativeNormalizer_map (L Z : Subgroup G) (e : G ≃* G) :
    (relativeNormalizer L Z).map e.toMonoidHom =
      relativeNormalizer (L.map e.toMonoidHom) (Z.map e.toMonoidHom) := by
  unfold relativeNormalizer
  rw [map_inf _ _ _ e.injective, map_equiv_normalizer_eq]

/-- The candidate is functorial, so its normalizer control needs no assumed
root configuration. -/
theorem residualRoot_map (L X : Subgroup G) (e : G ≃* G) :
    (residualRoot L X).map e.toMonoidHom =
      residualRoot (L.map e.toMonoidHom) (X.map e.toMonoidHom) := by
  unfold residualRoot
  rw [map_commutator, relativeNormalizer_map, map_inf _ _ _ e.injective,
    map_centralizer_equiv]
  rfl

/-- The candidate lies in C_L(X). -/
theorem residualRoot_le (L X : Subgroup G) :
    residualRoot L X ≤ L ⊓ centralizer (X : Set G) :=
  le_normalizer_iff_commutator_le_right.mp inf_le_right

/-- Simultaneous normalizers of L and X preserve the intrinsic root. -/
theorem normalizes_residualRoot {L X : Subgroup G} {a : G}
    (haL : a ∈ normalizer (L : Set G)) (haX : a ∈ normalizer (X : Set G)) :
    a ∈ normalizer (residualRoot L X : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (residualRoot L X).map (MulAut.conj a).toMonoidHom = _
  rw [residualRoot_map, MulEquiv.toMonoidHom_eq_coe, mem_normalizer_iff_map_conj_eq.mp haL,
    mem_normalizer_iff_map_conj_eq.mp haX]

/-- They also preserve the actual relative root normalizer. -/
theorem normalizes_rootNormalizer {L X : Subgroup G} {a : G}
    (haL : a ∈ normalizer (L : Set G)) (haX : a ∈ normalizer (X : Set G)) :
    a ∈ normalizer (relativeNormalizer L (residualRoot L X) : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (relativeNormalizer L (residualRoot L X)).map (MulAut.conj a).toMonoidHom = _
  rw [relativeNormalizer_map, MulEquiv.toMonoidHom_eq_coe, mem_normalizer_iff_map_conj_eq.mp haL,
    mem_normalizer_iff_map_conj_eq.mp (normalizes_residualRoot haL haX)]

/-- Each of the three source descriptions of X implies that P normalizes X.
The solvable residual is P∞; the final branch is O³(C_P(Z)), not O₃. -/
theorem relativeNormalizer_normalizes_residual {L Z X : Subgroup G}
    (hX : X = (solvableResidual (relativeNormalizer L Z)).map
        (relativeNormalizer L Z).subtype ∨
      X = relativeNormalizer L Z ⊓ centralizer (Z : Set G) ∨
      X = (pResidual 3 (relativeNormalizer L Z ⊓ centralizer (Z : Set G) : Subgroup G)).map
        (relativeNormalizer L Z ⊓ centralizer (Z : Set G) : Subgroup G).subtype) :
    relativeNormalizer L Z ≤ normalizer (X : Set G) := by
  let P := relativeNormalizer L Z
  have hn : P ≤ normalizer (P ⊓ centralizer (Z : Set G) : Set G) :=
    (le_inf P.le_normalizer
      (inf_le_right.trans (normalizer_le_normalizer_centralizer Z))).trans
        inf_normalizer_le_normalizer_inf
  rcases hX with rfl | rfl | rfl
  · exact P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (solvableResidual P))
  · exact hn
  · exact hn.trans (normalizer_le_normalizer_characteristic_image
      (P ⊓ centralizer (Z : Set G)) (pResidual 3 _))

/-- Once the centralizer product is known, its elementary structure follows
from the elementary root and commuting factors. Their intersection need not be trivial. -/
theorem space_elementary {T : Sylow 2 G} {L X Z : Subgroup G}
    [IsElementaryAbelian 2 Z] [IsElementaryAbelian 2 (commutingSylow T L)]
    (hZL : Z ≤ L) (hV : space T X = Z ⊔ commutingSylow T L) :
    IsElementaryAbelian 2 (space T X) := by
  rw [hV]
  exact IsElementaryAbelian.sup_of_le_centralizer
    (inf_le_right.trans (centralizer_le hZL))

/-- The same product places P in the actual simultaneous normalizer. -/
theorem relativeNormalizer_le_actingGroup {T : Sylow 2 G} {L X Z : Subgroup G}
    (hV : space T X = Z ⊔ commutingSylow T L)
    (hPX : relativeNormalizer L Z ≤ normalizer (X : Set G)) :
    relativeNormalizer L Z ≤ actingGroup (space T X) X := by
  refine le_inf ?_ hPX
  rw [hV]
  apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
  refine le_inf inf_le_right ?_
  apply le_trans _ (centralizer_le_normalizer _)
  exact inf_le_left.trans (le_centralizer_iff.mp (show commutingSylow T L ≤
    centralizer (L : Set G) from inf_le_right))

variable [Finite G] {T : Sylow 2 G} {z g : G} {L X R : Subgroup G}

private theorem commuting_nontrivial (h : StandardSetup T z L) :
    commutingSylow T L ≠ ⊥ := by
  have hz : z ∈ commutingSylow T L := ⟨h.mem_sylow,
    mem_centralizer_iff.mpr fun x hx =>
      mem_centralizer_singleton_iff.mp (h.component.1 hx)⟩
  intro he
  have hz1 : z = 1 := by simpa only [he, mem_bot] using hz
  have ho := h.involution
  simp [hz1] at ho

/-- Source tight embedding controls the full stabilizer of T_C. -/
theorem commuting_stabilizer_le (h : StandardSetup T z L) :
    normalizer (commutingSylow T L : Set G) ≤ normalizer (L : Set G) := by
  rw [← h.normalizers_eq]
  exact h.tight.normalizer_le (T.isPGroup'.to_le inf_le_left)
    (commuting_nontrivial h) inf_le_right

/-- This is the source stabilizer-normality control for the actual P,
derived from its intrinsic construction and tight embedding. -/
theorem stabilizer_normalizes_parabolic (h : StandardSetup T z L) :
    actingGroup (space T X) X ⊓ normalizer (commutingSylow T L : Set G) ≤
      normalizer (relativeNormalizer L (residualRoot L X) : Set G) := by
  intro a ha
  exact normalizes_rootNormalizer (commuting_stabilizer_le h ha.2) ha.1.2

/-- The selected Δ-conjugator moves T_C, already from tight embedding. -/
theorem conjugator_moves_commutingSylow (h : IntersectionSetup T z L g R) :
    g ∉ normalizer (commutingSylow T L : Set G) := by
  intro hg
  have hgL := commuting_stabilizer_le h.toStandardSetup hg
  have hgK : g ∈ normalizer (centralizer (L : Set G) : Set G) :=
    h.normalizers_eq ▸ hgL
  exact h.mem_delta.2.1 (mem_normalizer_iff_map_conj_eq.mp hgK)

/-- The centralizer product lies in the source transported Sylow. Its root
factor lies in X ≤ Lᵍ; its commuting factor centralizes the nontrivial R. -/
theorem space_le_transported_sylow (h : IntersectionSetup T z L g R)
    {Z : Subgroup G} {u : G} (hu : u ∈ R) (hu2 : orderOf u = 2)
    (hZX : Z ≤ X) (hXL' : X ≤ L.conjBy g)
    (hRC : R ≤ centralizer (commutingSylow T L : Set G))
    (hV : space T X = Z ⊔ commutingSylow T L)
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g) :
    space T X ≤ (T : Subgroup G).conjBy g := by
  have hR : R ≠ ⊥ := by
    intro he
    have hu1 : u = 1 := by simpa only [he, mem_bot] using hu
    simp [hu1] at hu2
  have hLN : L.conjBy g ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G) := by
    change L.map (MulAut.conj g).toMonoidHom ≤
      normalizer ((centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom : Set G)
    rw [← map_equiv_normalizer_eq]
    exact map_mono (h.normalizers_eq ▸ L.le_normalizer)
  apply le_trans (le_inf (show space T X ≤ (T : Subgroup G) from inf_le_left) ?_)
    htransport
  rw [hV]
  exact sup_le (hZX.trans (hXL'.trans hLN))
    ((le_centralizer_iff.mp hRC).trans
      ((centralizer_le_normalizer _).trans (h.normalizer_le hR le_rfl)))

/-- The mover for the existing O'Nan consumer is constructed from the genuine
source transport, common-residual containment and 16.5.6(3). -/
theorem source_mover (h : IntersectionSetup T z L g R)
    {Z : Subgroup G} {u : G} (hu : u ∈ R) (hu2 : orderOf u = 2)
    (hZX : Z ≤ X) (hXL' : X ≤ L.conjBy g)
    (hRC : R ≤ centralizer (commutingSylow T L : Set G))
    (hV : space T X = Z ⊔ commutingSylow T L)
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hgX : g ∈ normalizer (X : Set G)) :
    g ∈ actingGroup (space T X) X ∧
      g ∉ normalizer (commutingSylow T L : Set G) :=
  ⟨mem_actingGroup_of_transport hgX
    (space_le_transported_sylow h hu hu2 hZX hXL' hRC hV htransport),
    conjugator_moves_commutingSylow h⟩

/-- The covered branch is forced, not assumed: T_C ≤ X ≤ L gives Z(L) ≠ 1. -/
theorem center_ne_bot_of_commuting_le_residual (h : StandardSetup T z L)
    (hXL : X ≤ L) (hCX : commutingSylow T L ≤ X) : center L ≠ ⊥ := by
  intro hc
  apply commuting_nontrivial h
  apply bot_unique
  intro c hcC
  have hcL := hXL (hCX hcC)
  have hm : (⟨c, hcL⟩ : L) ∈ center L := mem_center_iff.mpr fun l =>
    Subtype.ext (mem_centralizer_iff.mp hcC.2 l l.property)
  have he : (⟨c, hcL⟩ : L) = 1 := by simpa only [hc, mem_bot] using hm
  exact congrArg Subtype.val he

/-- The possible diagram action has centerless component. Thus the covered
branch cannot be the index-two exception. -/
theorem cover_reduction (h : StandardSetup T z L) (hXL : X ≤ L)
    (hdiagram : (T : Subgroup G) ≤ normalizer (X : Set G) ∨
      center L = ⊥) (hCX : commutingSylow T L ≤ X) :
    (T : Subgroup G) ≤ normalizer (X : Set G) := by
  rcases hdiagram with hn | hc
  · exact hn
  · exact (center_ne_bot_of_commuting_le_residual h hXL hCX hc).elim

/-- In the double-cover branch, the nontrivial T_C fills the center of order two. -/
theorem commuting_eq_center_of_card_two (h : StandardSetup T z L)
    (hXL : X ≤ L) (hCX : commutingSylow T L ≤ X)
    (hcenter : Nat.card (center L) = 2) :
    commutingSylow T L = (center L).map L.subtype := by
  have hle : commutingSylow T L ≤ (center L).map L.subtype := by
    intro c hc
    refine ⟨⟨c, hXL (hCX hc)⟩, mem_center_iff.mpr ?_, rfl⟩
    intro l
    exact Subtype.ext (mem_centralizer_iff.mp hc.2 l l.property)
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective L.subtype_injective, hcenter]
  have hc := (one_lt_card_iff_ne_bot _).mpr (commuting_nontrivial h)
  omega

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot.Construction
