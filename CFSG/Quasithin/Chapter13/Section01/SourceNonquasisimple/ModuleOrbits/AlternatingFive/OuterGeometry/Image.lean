module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive.OuterGeometry.Kernel
public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.FiveLines
public import Mathlib.GroupTheory.PGroup

/-!
# The actual outer S₅ image on the A₅ central cover

The determinant-label image of the original two-group has order two. Thus
SL₂(4) together with that image has order 120. Its five-line image contains
A₅, so the scalar kernel of order three has trivial intersection with it.
The resulting faithful action is S₅, retaining the literal LT-action kernel
and the original component image.

Source: Aschbacher--Smith, proof of 13.1.12, printed p.872, using the
semilinear natural normalizer from 6.2.5. No orbit conclusion is an input.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.SL2FourNatural SemilinearNormalizer

local instance : Finite Gamma := Nat.finite_of_card_ne_zero (by rw [gamma_card]; decide)

private theorem symmetricFive_card : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]

private theorem alternatingFive_card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := (alternatingGroup (Fin 5)).card_mul_index
  rw [alternatingGroup.index_eq_two, symmetricFive_card] at h
  omega

private theorem special_card : Nat.card special.range = 60 := by
  have hi : Function.Injective special := by
    intro x y h
    apply action_faithful
    simpa only [natural_special] using congrArg natural h
  rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
    BenderSuzuki.External.huppert614_card_specialLinearGroup,
    Nat.card_eq_fintype_card,card_field]
  norm_num

private theorem two_group_label_card (P : Subgroup (Equiv.Perm Fˣ))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥) : Nat.card P = 2 := by
  have hc : Nat.card (Equiv.Perm Fˣ) = 6 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,card_labels]
    decide
  have hd : Nat.card P ∣ 6 := hc ▸ card_subgroup_dvd_card P
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    have hd4 : 4 ∣ 6 := (show 4 ∣ Nat.card P from by
      rw [hn]
      exact pow_dvd_pow 2 hh).trans hd
    norm_num at hd4
  have hgt := (one_lt_card_iff_ne_bot P).mpr hne
  have hle : Nat.card P ≤ 2 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) hnle
  omega

private theorem special_two_group_card (P : Subgroup Gamma) (hp : IsPGroup 2 P)
    (hne : ¬ P ≤ special.range) : Nat.card (special.range ⊔ P : Subgroup Gamma) = 120 := by
  let H := special.range ⊔ P
  let k := labels.comp H.subtype
  have hk : k.ker = special.range.subgroupOf H := by
    rw [← labels_ker]
    rfl
  have hr : k.range = P.map labels := by
    rw [MonoidHom.range_comp, H.range_subtype]
    change (special.range ⊔ P).map labels = _
    rw [Subgroup.map_sup, ← labels_ker, map_ker_self, bot_sup_eq]
  have hne' : P.map labels ≠ ⊥ := by
    rw [ne_eq,Subgroup.map_eq_bot_iff,labels_ker]
    exact hne
  have hkr : Nat.card k.ker = 60 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe (show special.range ≤ H from le_sup_left)).toEquiv]
    exact special_card
  have hrr : Nat.card k.range = 2 := by
    rw [hr]
    exact two_group_label_card (P.map labels) (hp.map labels) hne'
  have h := k.ker.card_mul_index
  rw [index_ker,hkr,hrr] at h
  exact h.symm

private theorem fiveLines_kernel_card : Nat.card fiveLines.ker = 3 := by
  have hs : Function.Surjective fiveLines := by
    intro p
    obtain ⟨g,hg⟩ := specialFieldFiveLines_surjective p
    exact ⟨g,hg⟩
  have h := fiveLines.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hs,Nat.card_congr (Subgroup.topEquiv).toEquiv,
    symmetricFive_card,gamma_card] at h
  omega

private theorem special_two_group_fiveLines_bijective
    (P : Subgroup Gamma) (hp : IsPGroup 2 P) (hne : ¬ P ≤ special.range) :
    Function.Bijective (fiveLines.comp (special.range ⊔ P : Subgroup Gamma).subtype) := by
  let H := special.range ⊔ P
  let f := fiveLines.comp H.subtype
  have hH : Nat.card H = 120 := special_two_group_card P hp hne
  have hle : alternatingGroup (Fin 5) ≤ f.range := by
    rw [← specialFiveLines_range]
    rintro _ ⟨l,rfl⟩
    exact ⟨⟨special l, (show special.range ≤ H from le_sup_left) ⟨l,rfl⟩⟩,rfl⟩
  have hcard : 60 ≤ Nat.card f.range := alternatingFive_card ▸ card_le_of_le hle
  have hkerle : f.ker.map H.subtype ≤ fiveLines.ker := by
    rintro _ ⟨g,hg,rfl⟩
    exact hg
  have hd : Nat.card f.ker ∣ 3 := by
    rw [← fiveLines_kernel_card, ← card_map_of_injective (K := f.ker) H.subtype_injective]
    exact card_dvd_of_le hkerle
  have he := f.ker.card_mul_index
  rw [index_ker,hH] at he
  have hk : Nat.card f.ker = 1 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with hh | hh
    · exact hh
    · rw [hh] at he
      omega
  refine ⟨(MonoidHom.ker_eq_bot_iff f).mp (eq_bot_of_card_eq _ hk), ?_⟩
  apply f.surjective_of_card_ker_le_div
  rw [hk,hH,symmetricFive_card]

namespace Marking
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {L : Subgroup G} (d : Marking T L W)

/-- The five-line action of the original natural quotient, before recognition. -/
@[expose] def outerQuotient (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) :
    (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 5) :=
  fiveLines.comp (d.semilinearHom hmoved)

theorem outerQuotient_image_faithful
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) (ho : d.HasOuterNaturalAction) :
    Function.Bijective (fiveLines.comp (d.semilinearHom hmoved).range.subtype) := by
  rw [d.semilinearHom_range hmoved]
  apply special_two_group_fiveLines_bijective
  · exact (T.isPGroup'.comap_subtype).map _
  · exact d.semilinearHom_two_image_not_le hmoved ho

theorem outerQuotient_surjective
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) (ho : d.HasOuterNaturalAction) :
    Function.Surjective (d.outerQuotient hmoved) := by
  intro p
  obtain ⟨g,hg⟩ := (d.outerQuotient_image_faithful hmoved ho).2 p
  obtain ⟨a,ha⟩ := g.property
  exact ⟨a,by change fiveLines (d.semilinearHom hmoved a) = p; rw [ha]; exact hg⟩

theorem outerQuotient_kernel
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) (ho : d.HasOuterNaturalAction) :
    (d.outerQuotient hmoved).ker =
      (centralizer (normalizerMoved L : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
  rw [← d.semilinearHom_kernel hmoved]
  ext a
  simp only [MonoidHom.mem_ker]
  constructor
  · intro ha
    have he : (⟨d.semilinearHom hmoved a, ⟨a,rfl⟩⟩ : (d.semilinearHom hmoved).range) = 1 := by
      apply (d.outerQuotient_image_faithful hmoved ho).1
      exact ha.trans (map_one _).symm
    exact congrArg Subtype.val he
  · intro ha
    change fiveLines (d.semilinearHom hmoved a) = 1
    rw [ha,map_one]

theorem outerQuotient_component
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L) :
    (L.subgroupOf (L ⊔ (T : Subgroup G))).map (d.outerQuotient hmoved) =
      alternatingGroup (Fin 5) := by
  change (L.subgroupOf (L ⊔ (T : Subgroup G))).map
    (fiveLines.comp (d.semilinearHom hmoved)) = _
  rw [← Subgroup.map_map,d.semilinearHom_component_image,MonoidHom.map_range]
  exact specialFiveLines_range

/-- The output marking identifies the actual LT-action and its actual L-image. -/
def outerMarking (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L)
    (ho : d.HasOuterNaturalAction) : OuterMarking T L where
  quotient := d.outerQuotient hmoved
  onto := d.outerQuotient_surjective hmoved ho
  kernel := d.outerQuotient_kernel hmoved ho
  component := d.outerQuotient_component hmoved

/-- Equivariance ties the S₅ map to the same five lines in the original
natural quotient, with its actual semilinear action retained. -/
theorem outerQuotient_lines
    (hmoved : ⁅normalizerMoved L,L⁆ = normalizerMoved L)
    (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (i : Fin 5) :
    ∃ c : F, c ≠ 0 ∧ d.naturalActor a (lineVector i) =
      c • lineVector (d.outerQuotient hmoved a i) := by
  obtain ⟨c,hc,he⟩ := fiveLines_equivariant (d.semilinearHom hmoved a) i
  refine ⟨c,hc,?_⟩
  rw [d.semilinearHom_natural] at he
  exact he

end Marking

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.AlternatingFive
