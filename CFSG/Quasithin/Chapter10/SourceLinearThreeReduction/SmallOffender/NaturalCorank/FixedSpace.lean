module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.ActionKernel
public import CFSG.Quasithin.Chapter10.SourceA5OffenderFixedGeometry

/-!
# Fixed-space geometry for the natural small offender

A point of the conjugate moved factor, outside its component-fixed part,
has centralizer normalizing that factor. Thus the commutator of the
normalizing offender with its fixed space lies in the intersection of the
two moved factors. Once the outside-M intersection theorem is supplied,
this gives the common fixed-space equality. The size bound constructs an
actual suitable involution at corank at most one, including corank zero.

The outside-M intersection remains an explicit earlier-source premise in
this module. No A₅ identification, center-free assumption, or global TI
claim is used. Source: Aschbacher--Smith 10.2.10(1) and the middle of the
proof of 10.2.12, printed pp.753--754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}
  (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)

include c m

/-- The normalizing part of the offender fixes the fixed space of every
nonfixed point in the conjugate moved factor. -/
theorem normalizer_fixed_space
    (hinter : ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥)
    {b : G} (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom)
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) ≤ centralizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
        normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let X := W ⊓ centralizer ({b} : Set G)
  let B := P ⊓ D.maximalLocal ⊓ normalizer (W : Set G)
  have hXN : X ≤ normalizer (P : Set G) := inf_le_right.trans
    ((source_nonnormal_conjugate_point_centralizer_normalizes D c.nonnormal ht htn
      (m.crossed t ht htn) c.pointCentralizers hb hbn).trans inf_le_right)
  have hcomm : ⁅B,X⁆ ≤ W ⊓ P := le_inf
    ((commutator_mono le_rfl (show X ≤ W from inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp (show B ≤ normalizer (W : Set G) from inf_le_right)))
    ((commutator_mono (show B ≤ P from inf_le_left.trans inf_le_left) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hXN))
  have he : ⁅B,X⁆ = ⊥ := eq_bot_iff.mpr (hcomm.trans_eq hinter)
  exact le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp he)

/-- The literal common fixed space of the normalizing part equals C_W(b). -/
theorem normalizer_fixed_space_eq
    (hinter : ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥)
    {b : G}
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅D.fullModule,L⁆ ⊓ centralizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
        normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) : Subgroup G) : Set G) =
      ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hb))
  · exact le_inf inf_le_left (normalizer_fixed_space c m hinter hb.1.1 hbn)

/-- The actual normalizing involution at corank at most one, together with
the resulting fixed-space identity on the original subgroups. -/
theorem exists_normalizing_involution_fixed_space
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hinter : ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥) :
    ∃ b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
        normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G),
      orderOf b = 2 ∧
      b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) ∧
      ⁅D.fullModule,L⁆ ⊓ centralizer
        (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
          normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) : Subgroup G) : Set G) =
        ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) := by
  obtain ⟨b,hb,hbM,hbN,hbn⟩ :=
    corank_one_exists_noncentral_normalizing_element D c.nonnormal hsmall
  have hbne : b ≠ 1 := fun he => hbn (he ▸ one_mem _)
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 ((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  exact ⟨b,⟨⟨hb,hbM⟩,hbN⟩,
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hb) hbne,
    hbn,normalizer_fixed_space_eq c m hinter ⟨⟨hb,hbM⟩,hbN⟩ hbn⟩

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
