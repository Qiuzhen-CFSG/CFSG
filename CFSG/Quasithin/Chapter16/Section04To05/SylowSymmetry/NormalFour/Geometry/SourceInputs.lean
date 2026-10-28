module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.NormalFour.Geometry.NormalSubgroup

/-!
# Source inputs for the TI product and omega calculation

The relative normalizer identity makes an element of `C − S` move the tightly
embedded conjugate `K′`. Its two-subgroup `R` therefore has trivial intersection
with its moved conjugate. The actual Sylow containment also shows that `R`
normalizes `C`.

Multiplication coordinates put `A` in `SL`. Since `C` centralizes `L` and
normalizes `S`, this gives `[A,C] ≤ S`. Delta-zero puts all involutions of `R`
in `A`, yielding the precise commutator containment used by the omega argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 16.4.10, printed p.1193, using 16.4.2(1), (3), (5).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.NormalFour
open Subgroup
variable {G : Type*} [Group G] [Finite G] {C L A S : Subgroup G}

omit [Finite G] in
/-- The commuting coordinate of the inner subgroup lies in `S`, so its
commutators with `C` lie in `S`. This retains the actual ambient coordinates. -/
theorem commutator_inner_le (d : SaturatedProjection C L A S) : ⁅A, C⁆ ≤ S := by
  apply commutator_le.mpr
  intro a ha c hc
  have hf := d.configuration.factors_in_centralizer ha
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right S L
    (d.configuration.proper.le.trans
      (d.configuration.centralizes.trans (centralizer_le_normalizer _)))] at hf
  obtain ⟨s, hs, l, hl, rfl⟩ := hf
  have hcl : Commute l c := mem_centralizer_iff.mp (d.configuration.centralizes hc) l hl
  rw [commutatorElement_mul_left_eq_conj_mul, hcl.commutator_eq]
  simp only [mul_one, mul_inv_cancel, one_mul]
  exact (le_normalizer_iff_commutator_le_left.mp
    ((normal_subgroupOf_iff_le_normalizer d.configuration.proper.le).mp d.normal_inside))
      (commutator_mem_commutator hs hc)

variable {T : Sylow 2 G} {z g : G} {R : Subgroup G}

/-- The actual ambient subgroup `R` normalizes the commuting Sylow factor. -/
theorem normalizes_commuting (h : IntersectionSetup T z L g R) :
    R ≤ normalizer (commutingSylow T L : Set G) :=
  h.le_sylow.trans ((le_inf (T : Subgroup G).le_normalizer
    (h.normalizers_eq ▸ h.sylow_normalizes)).trans inf_normalizer_le_normalizer_inf)

/-- Tight embedding makes the chosen conjugates disjoint, since the earlier
normalizer identity puts the mover outside the normalizer of the actual `K′`. -/
theorem disjoint_conjugate (h : IntersectionSetup T z L g R)
    (hn : commutingSylow T L ⊓ normalizer ((centralizer (L : Set G)).conjBy g : Set G) =
      commutingSylow T L ⊓ centralizer (R : Set G))
    {t : G} (ht : t ∈ commutingSylow T L)
    (hout : t ∉ commutingSylow T L ⊓ centralizer (R : Set G)) :
    Disjoint R (R.conjBy t) := by
  have htN : t ∉ normalizer ((centralizer (L : Set G)).conjBy g : Set G) := by
    intro hh
    exact hout (hn ▸ (show t ∈ commutingSylow T L ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) from ⟨ht, hh⟩))
  have hodd := (tight_map h.tight (MulAut.conj g)).2 t htN
  let D := R ⊓ R.conjBy t
  have hDle : D ≤ (centralizer (L : Set G)).conjBy g ⊓
      ((centralizer (L : Set G)).conjBy g).conjBy t :=
    inf_le_inf (h.sylow.le.trans inf_le_left) (map_mono (h.sylow.le.trans inf_le_left))
  obtain ⟨n, hncard⟩ := (h.sylow.isPGroup.to_le (show D ≤ R from inf_le_left)).exists_card_eq
  have hcop : (Nat.card D).Coprime (Nat.card
      ((centralizer (L : Set G)).conjBy g ⊓ ((centralizer (L : Set G)).conjBy g).conjBy t : Subgroup G)) := by
    rw [hncard]
    exact hodd.coprime_two_left.pow_left n
  have hh := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rw [inf_eq_left.mpr hDle] at hh
  exact disjoint_iff.mpr hh

/-- The Delta-zero condition puts all involutions in the inner coordinate
subgroup, giving the commutator containment needed in the omega calculation. -/
theorem commutator_omega_le (h : IntersectionSetup T z L g R)
    (hd : (centralizer (L : Set G)).conjBy g ∈ deltaZero L)
    (d : SaturatedProjection (commutingSylow T L) L (innerPart L R)
      (commutingSylow T L ⊓ centralizer (R : Set G)))
    {t : G} (ht : t ∈ commutingSylow T L) :
    ⁅omegaOneAmbient R, zpowers t⁆ ≤ commutingSylow T L ⊓ centralizer (R : Set G) :=
  (commutator_mono (le_inf (omegaOneAmbient_le R) (h.omega_le_of_mem_deltaZero hd))
    (zpowers_le.mpr ht)).trans (commutator_inner_le d)

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.NormalFour
