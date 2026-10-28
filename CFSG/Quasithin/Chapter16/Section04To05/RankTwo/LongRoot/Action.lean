module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Conjugation
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Counting
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Reductions
public import Theory.Representation.ElementaryAbelianAction
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The action on the centralizer of the common residual

The acting group is `N_G(V) ∩ N_G(X)`, for the actual subgroup `V = C_T(X)`.
Transport puts the source conjugator in this group. Restricting the normalizer
homomorphism gives the faithful image and its quotient by the relative
centralizer. Tight embedding gives the TI condition on `V ∩ K = T_C`.

An invariant intersection proves `V ≤ X` in the irreducible case. A conjugate
of `T_C` contained in `X` already forces `T_C ≤ X`; this also handles the
two-member swapped alternative, once the source cover table excludes the
diagram-automorphism index-two case. The larger two-power alternative is
excluded using divisibility by `|T : N_T(X)|`, without a Sylow claim about
`N_T(X)` in the acting group.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
Lemma 16.5.13, printed pp.1201--1202. Model-dependent inputs remain explicit.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- The source `V`, before identifying it with the root-group product. -/
def space (T X : Subgroup G) : Subgroup G := T ⊓ centralizer (X : Set G)

/-- The actual simultaneous normalizer in the source. -/
def actingGroup (V X : Subgroup G) : Subgroup G :=
  normalizer (V : Set G) ⊓ normalizer (X : Set G)

/-- Restriction of the canonical normalizer action to the simultaneous normalizer. -/
def action (V X : Subgroup G) : actingGroup V X →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion inf_le_left)

/-- The kernel is the relative centralizer, rather than an assumed faithful quotient. -/
theorem action_kernel (V X : Subgroup G) :
    (action V X).ker = (centralizer (V : Set G)).subgroupOf (actingGroup V X) := by
  ext a
  change V.normalizerMonoidHom (inclusion inf_le_left a) = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

/-- The source quotient is identified with the actual automorphism image. -/
noncomputable def actionQuotient (V X : Subgroup G) :
    (actingGroup V X ⧸ (action V X).ker) ≃* (action V X).range :=
  QuotientGroup.quotientKerEquivRange (action V X)

/-- The elementary abelian subgroup carries its canonical binary representation. -/
noncomputable def representation (V X : Subgroup G) [IsElementaryAbelian 2 V] :
    Representation (ZMod 2) (action V X).range (Additive V) :=
  Representation.ofElementaryAbelianAction (p := 2)

theorem representation_faithful (V X : Subgroup G) [IsElementaryAbelian 2 V] :
    Function.Injective (representation V X) := by
  intro a b he
  apply Subtype.ext
  apply MulEquiv.ext
  intro v
  exact congrArg (fun f : Module.End (ZMod 2) (Additive V) => f (Additive.ofMul v)) he

variable [Finite G]

/-- The source transport, with no root-group assumptions needed. -/
theorem mem_actingGroup_of_transport {T X : Subgroup G} {g : G}
    (hgX : g ∈ normalizer (X : Set G)) (htransport : space T X ≤ T.conjBy g) :
    g ∈ actingGroup (space T X) X :=
  ⟨normalizes_centralizer_intersection hgX htransport, hgX⟩

/-- `N_T(X)` lies in the simultaneous normalizer. -/
theorem sylowNormalizer_le_actingGroup (T X : Subgroup G) :
    T ⊓ normalizer (X : Set G) ≤ actingGroup (space T X) X := by
  intro g hg
  apply mem_actingGroup_of_transport hg.2
  have he : T.conjBy g = T := mem_normalizer_iff_map_conj_eq.mp (T.le_normalizer hg.1)
  rw [he]
  exact inf_le_left

omit [Finite G] in
/-- The TI subgroup is exactly `T_C`, using the genuine containment `X ≤ L`. -/
theorem space_intersection_centralizer {T L X : Subgroup G} (hXL : X ≤ L) :
    space T X ⊓ centralizer (L : Set G) = T ⊓ centralizer (L : Set G) := by
  apply le_antisymm
  · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  · exact le_inf (le_inf inf_le_left (inf_le_right.trans (centralizer_le hXL))) inf_le_right

/-- Tight embedding supplies TI for distinct translates under the actual acting group. -/
theorem ti_commutingSylow {T : Sylow 2 G} {L X : Subgroup G}
    (hK : Theory.GroupTheory.IsTightlyEmbedded (centralizer (L : Set G)))
    (hXL : X ≤ L) {a b : G}
    (ha : a ∈ actingGroup (space T X) X) (hb : b ∈ actingGroup (space T X) X)
    (hne : (commutingSylow T L).conjBy a ≠ (commutingSylow T L).conjBy b) :
    Disjoint ((commutingSylow T L).conjBy a) ((commutingSylow T L).conjBy b) := by
  have he : space T X ⊓ centralizer (L : Set G) = commutingSylow T L :=
    space_intersection_centralizer hXL
  rw [← he] at hne ⊢
  exact ti_conjugates_of_tightlyEmbedded_intersection hK
    (T.isPGroup'.to_le (inf_le_left.trans inf_le_left)) inf_le_left ha hb hne

omit [Finite G] in
/-- The whole Sylow fixes `T_C`, whether or not it fixes the root parabolic. -/
theorem sylow_normalizes_commutingSylow {T : Sylow 2 G} {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (T : Subgroup G) ≤ normalizer (commutingSylow T L : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change ((T : Subgroup G) ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj g).injective, MulEquiv.toMonoidHom_eq_coe,
    mem_normalizer_iff_map_conj_eq.mp (T.le_normalizer hg)]
  have hn : g ∈ normalizer (centralizer (L : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer L (hTL hg)
  rw [mem_normalizer_iff_map_conj_eq.mp hn]
  rfl

omit [Finite G] in
/-- A moved conjugate contained in the common residual forces the original
subgroup into that residual, since the conjugator preserves it. -/
theorem le_residual_of_conjugate_le {V X C : Subgroup G} {g : G}
    (hg : g ∈ actingGroup V X) (hC : C.conjBy g ≤ X) : C ≤ X := by
  intro c hc
  exact (mem_normalizer_iff.mp hg.2 c).mpr (hC (mem_map_of_mem _ hc))

omit [Finite G] in
/-- The invariant intersection with `X` is nonzero because it contains the root group. -/
theorem space_le_residual_of_irreducible {V X Z : Subgroup G}
    (hZ : Z ≠ ⊥) (hZV : Z ≤ V) (hZX : Z ≤ X)
    (hirr : ∀ W : Subgroup G, W ≤ V → actingGroup V X ≤ normalizer (W : Set G) →
      W = ⊥ ∨ W = V) : V ≤ X := by
  have hn : actingGroup V X ≤ normalizer ((V ⊓ X : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_inf _ _ _ (MulAut.conj g).injective,
      mem_normalizer_iff_map_conj_eq.mp hg.1, mem_normalizer_iff_map_conj_eq.mp hg.2]
  rcases hirr (V ⊓ X) inf_le_left hn with hz | hv
  · exact (hZ (eq_bot_iff.mpr (hz ▸ le_inf hZV hZX))).elim
  · exact hv ▸ inf_le_right

/-- The power-of-two orbit in alternative (iii) is too large for the source
index bound. `P` will be `N_T(X)` and `N` the actual stabilizer. -/
theorem no_large_two_power_index (T : Sylow 2 G) {P M N : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hPT : P ≤ (T : Subgroup G)) (hPM : P ≤ M) (hPN : P ≤ N)
    (hbound : P.relIndex T ≤ 2) (hindex : N.relIndex M = 2 ^ n) : False := by
  have hd := two_power_relIndex_dvd_sylow_relIndex T n hPT hPM hPN hindex
  have hpos : 0 < P.relIndex (T : Subgroup G) := Nat.pos_of_ne_zero (by
    exact Subgroup.index_ne_zero_of_finite)
  have hle := Nat.le_of_dvd hpos hd
  have hfour : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hfour
  omega

/-- Once `T_C ≤ X` rules out the diagram case, a two-member orbit is impossible.
This supplies the additional argument required for O'Nan's swapped alternative. -/
theorem no_swapped_index {T : Sylow 2 G} {L X C : Subgroup G} {g : G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hC : C = commutingSylow T L)
    (hg : g ∈ actingGroup (space T X) X) (hswap : C.conjBy g ≤ X)
    (hcover : C ≤ X → (T : Subgroup G) ≤ normalizer (X : Set G))
    (hindex : (normalizer (C : Set G)).relIndex (actingGroup (space T X) X) = 2) : False := by
  have hTX := hcover (le_residual_of_conjugate_le hg hswap)
  have hTM : (T : Subgroup G) ≤ actingGroup (space T X) X :=
    (le_inf le_rfl hTX).trans (sylowNormalizer_le_actingGroup T X)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) := by
    rw [hC]
    exact sylow_normalizes_commutingSylow hTL
  have hd := two_power_relIndex_dvd_sylow_relIndex T 1 le_rfl hTM hTC
    (by simpa only [pow_one] using hindex)
  norm_num at hd

end CFSG.Quasithin.Chapter16.Intersections.RankTwo.LongRoot
