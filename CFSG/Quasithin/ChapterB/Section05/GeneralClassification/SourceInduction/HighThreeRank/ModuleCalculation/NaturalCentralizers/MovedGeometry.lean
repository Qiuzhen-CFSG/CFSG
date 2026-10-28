module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.Applicability
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.NonsplitFour
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The odd-core moved space in B.5.7

Averaging over an odd normal subgroup splits its actual moved space from its
fixed space and preserves faithfulness on the moved space. Applied to the
original three-core, a two-dimensional moved space therefore gives an embedding
in GL₂(2), order three, and an actual equivalence with the cyclic group C₃.

If the component moved space is fixed by the three-core, the two original moved
spaces are disjoint, their sum is the moved space of the product, and the
three-core moved space is fixed by the component. The selected moving offender
cannot fix that second space. These statements do not split off C_V(G), and
they do not assume either target ambient centralizer equality.

The commutant computation must supply the crossed-fixation premise; the
permutation offender bounds must supply the plane dimension. Both remain
explicit here. No universal earlier-source implication is used in these lemmas.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.7,
printed p.106, final paragraph.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V)

/-- The whole original group acts on the moved space of its normal subgroup. -/
def normalMoved (X : Subgroup G) [X.Normal] : Subrepresentation ρ where
  toSubmodule := moved ρ X
  apply_mem_toSubmodule g v hv := by
    have hs : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (moved ρ X) := by
      apply subspaceCommutator_invariant_normalizer
      · exact le_subspaceStabilizer ρ ⊤ (by intros; trivial)
      · rw [normalizer_eq_top]
    exact (hs (mem_top g) v).2 hv

/-- Odd-order averaging gives the actual fixed/moved decomposition. -/
theorem odd_moved_complement (X : Subgroup G) [Finite X] (ho : Odd (Nat.card X)) :
    IsCompl (moved ρ X) (fixedSpace ρ X) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let N := Representation.norm (ρ.comp X.subtype)
  have hc : (Fintype.card X : ZMod 2) = 1 :=
    (show Odd (Fintype.card X) by simpa only [Nat.card_eq_fintype_card] using ho).natCast_zmod_two
  have hfixed (v : V) (hv : v ∈ fixedSpace ρ X) : N v = v := by
    simp only [N, Representation.norm, LinearMap.sum_apply, MonoidHom.comp_apply, Subgroup.subtype_apply,
      show ∀ x : X, ρ x v = v from hv, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2), hc, one_smul]
  have hkill : moved ρ X ≤ LinearMap.ker N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, v, _, rfl⟩
    change N (ρ x v - v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (Representation.norm_self_apply (ρ.comp X.subtype) ⟨x, hx⟩ v)
  refine ⟨Submodule.disjoint_def.mpr (fun v hv hf => ?_), ?_⟩
  · exact (hfixed v hf).symm.trans (hkill hv)
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    have hsum : N v - v ∈ moved ρ X := by
      have hh : (∑ x : X, (ρ x v - v)) ∈ moved ρ X := by
        apply Submodule.sum_mem
        intro x _
        exact Submodule.subset_span ⟨x, x.property, v, Submodule.mem_top, rfl⟩
      simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul (ZMod 2), hc, one_smul, N, Representation.norm,
        LinearMap.sum_apply, MonoidHom.comp_apply, Subgroup.subtype_apply] using hh
    refine Submodule.mem_sup.mpr ⟨v - N v, ?_, N v, ?_, sub_add_cancel _ _⟩
    · simpa only [neg_sub] using (moved ρ X).neg_mem hsum
    · exact fun x => Representation.self_norm_apply (ρ.comp X.subtype) x v

/-- Restriction to the odd subgroup's moved space retains its faithful action. -/
theorem odd_moved_faithful (hf : Function.Injective ρ)
    (X : Subgroup G) [X.Normal] [Finite X] (ho : Odd (Nat.card X)) :
    Function.Injective ((normalMoved ρ X).toRepresentation.comp X.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  apply Subtype.ext
  apply hf
  ext v
  have hs := (odd_moved_complement ρ X ho).sup_eq_top
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp (hs.symm ▸ Submodule.mem_top (x := v))
  have hwfix := congrArg Subtype.val (LinearMap.congr_fun (MonoidHom.mem_ker.mp hx)
    (⟨w, hw⟩ : (normalMoved ρ X).toSubmodule))
  change ρ x w = w at hwfix
  change ρ x (w + c) = ρ (1 : G) (w + c)
  rw [map_add, hwfix, show ρ x c = c from hc x, map_one]
  rfl

/-- Commuting actions which kill the first moved space kill the reverse mixed differences. -/
theorem reverse_moved_fixed {L X : Subgroup G}
    (hcomm : L ≤ centralizer (X : Set G))
    (hfix : moved ρ L ≤ fixedSpace ρ X) :
    moved ρ X ≤ fixedSpace ρ L := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, v, _, rfl⟩ l
  have he : ρ x (ρ l v - v) = ρ l v - v :=
    hfix (Submodule.subset_span ⟨l, l.property, v, Submodule.mem_top, rfl⟩) ⟨x, hx⟩
  have hc : ρ x (ρ l v) = ρ l (ρ x v) := by
    simpa only [← Module.End.mul_apply, ← map_mul] using
      congrArg (fun g => ρ g v) (hcomm l.property x hx)
  rw [map_sub, hc] at he
  change ρ l (ρ x v - v) = ρ x v - v
  rw [map_sub]
  exact sub_eq_sub_iff_add_eq_add.mpr
    ((sub_eq_sub_iff_add_eq_add.mp he).trans (add_comm _ _))

/-- The component and odd-core moved spaces are disjoint without splitting any fixed line. -/
theorem moved_disjoint_of_odd {L X : Subgroup G} [Finite X]
    (ho : Odd (Nat.card X)) (hfix : moved ρ L ≤ fixedSpace ρ X) :
    Disjoint (moved ρ L) (moved ρ X) :=
  (odd_moved_complement ρ X ho).disjoint.symm.mono_left hfix

/-- Moving both normal subgroups gives the sum of their actual moved spaces. -/
theorem moved_sup (L X : Subgroup G) [L.Normal] [X.Normal] :
    moved ρ (L ⊔ X) = moved ρ L ⊔ moved ρ X := by
  let S : Subrepresentation ρ := normalMoved ρ L ⊔ normalMoved ρ X
  have hker (Y : Subgroup G) (hY : moved ρ Y ≤ S.toSubmodule) :
      Y ≤ S.quotientRepresentation.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective q
    change S.toSubmodule.mkQ (ρ y v) = S.toSubmodule.mkQ v
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (hY (Submodule.subset_span ⟨y, hy, v, Submodule.mem_top, rfl⟩))
  have hLX : L ⊔ X ≤ S.quotientRepresentation.ker :=
    sup_le (hker L le_sup_left) (hker X le_sup_right)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    have he := LinearMap.congr_fun (MonoidHom.mem_ker.mp (hLX hg)) (S.toSubmodule.mkQ v)
    change S.toSubmodule.mkQ (ρ g v) = S.toSubmodule.mkQ v at he
    exact (Submodule.Quotient.mk_eq_zero _).mp (show S.toSubmodule.mkQ (ρ g v - v) = 0 by
      rw [map_sub, he, sub_self])
  · apply sup_le
    · apply Submodule.span_mono
      rintro _ ⟨g, hg, v, hv, rfl⟩
      exact ⟨g, (le_sup_left : L ≤ L ⊔ X) hg, v, hv, rfl⟩
    · apply Submodule.span_mono
      rintro _ ⟨g, hg, v, hv, rfl⟩
      exact ⟨g, (le_sup_right : X ≤ L ⊔ X) hg, v, hv, rfl⟩

/-- Fixing the odd normal subgroup's moved space forces centralization of that subgroup. -/
theorem centralizes_of_fixes_odd_moved (hf : Function.Injective ρ)
    (X : Subgroup G) [X.Normal] [Finite X] (ho : Odd (Nat.card X))
    (A : Subgroup G) (hfix : moved ρ X ≤ fixedSpace ρ A) :
    A ≤ centralizer (X : Set G) := by
  intro a ha x hx
  apply hf
  ext v
  have hs := (odd_moved_complement ρ X ho).sup_eq_top
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp (hs.symm ▸ Submodule.mem_top (x := v))
  have haw : ρ a w = w := hfix hw ⟨a, ha⟩
  have hxw : ρ x w ∈ moved ρ X := (normalMoved ρ X).apply_mem_toSubmodule x hw
  have haxw : ρ a (ρ x w) = ρ x w := hfix hxw ⟨a, ha⟩
  have hxc : ρ x c = c := hc ⟨x, hx⟩
  have hac : ρ a c ∈ fixedSpace ρ X :=
    (fixedSpace_stable_of_normal ρ X (mem_top a) c).2 hc
  have hxac : ρ x (ρ a c) = ρ a c := hac ⟨x, hx⟩
  simp only [map_mul, Module.End.mul_apply, map_add, haw, haxw, hxc, hxac]

variable [Finite G] {K : GroupClass.{u}}

/-- Oddness of the original three-core. -/
theorem threeCore_odd : Odd (Nat.card (pCore 3 G)) := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
  rw [hn]
  exact (by decide : Odd 3).pow

/-- The source hypothesis makes the original three-core faithful on its moved space. -/
theorem threeCore_moved_faithful (hyp : FFHypothesis K ρ) :
    Function.Injective ((normalMoved ρ (pCore 3 G)).toRepresentation.comp
      (pCore 3 G).subtype) :=
  odd_moved_faithful ρ hyp.faithful _ threeCore_odd

/-- The selected moving offender really moves the original cubic moved space. -/
theorem threeCore_moved_not_fixed (hyp : FFHypothesis K ρ) {A : Subgroup G}
    (hm : ¬ A ≤ centralizer (pCore 3 G : Set G)) :
    ¬ moved ρ (pCore 3 G) ≤ fixedSpace ρ A := by
  intro hfix
  exact hm (centralizes_of_fixes_odd_moved ρ hyp.faithful _ threeCore_odd A hfix)

/-- The source component commutes with the original three-core. -/
theorem component_centralizes_threeCore {L : Subgroup G} (hL : IsComponent G L) :
    L ≤ centralizer (pCore 3 G : Set G) := by
  rcases hL.normal_dichotomy (pCore 3 G) with hle | hc
  · let := hL.2
    let := IsQuasisimple.simple (G := L)
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    let := (pCore_isPGroup (p := 3) (G := G)).isNilpotent
    let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective hle)
    exact (Group.IsPerfect.not_isSolvable L inferInstance).elim
  · exact commutator_eq_bot_iff_le_centralizer.mp hc

/-- The source's two moved summands, with their actual inclusions and crossed fixation. -/
theorem threeCore_moved_decomposition {L : Subgroup G} (hL : IsComponent G L)
    (d : NoncentralContext K G L)
    (hfix : moved ρ L ≤ fixedSpace ρ (pCore 3 G)) :
    moved ρ (L ⊔ pCore 3 G) = moved ρ L ⊔ moved ρ (pCore 3 G) ∧
      Disjoint (moved ρ L) (moved ρ (pCore 3 G)) ∧
      moved ρ (pCore 3 G) ≤ fixedSpace ρ L := by
  let : L.Normal := d.normal
  exact ⟨moved_sup ρ L _, moved_disjoint_of_odd ρ threeCore_odd hfix,
    reverse_moved_fixed ρ (component_centralizes_threeCore hL) hfix⟩

/-- A two-dimensional moved space identifies the actual noncentral three-core. -/
theorem threeCore_card_of_plane (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (d : NoncentralContext K G L)
    (hd : Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) = 2) :
    Nat.card (pCore 3 G) = 3 := by
  let := hyp.finite_module
  have hdiv := Representation.card_dvd_card_GL_of_injective
    ((normalMoved ρ (pCore 3 G)).toRepresentation.comp (pCore 3 G).subtype)
    (threeCore_moved_faithful ρ hyp)
  change Nat.card (pCore 3 G) ∣ Nat.card
    (Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 2) (moved ρ (pCore 3 G)))) (ZMod 2)) at hdiv
  rw [hd, Matrix.card_GL_field] at hdiv
  norm_num [Fin.prod_univ_succ] at hdiv
  have hone : Nat.card (pCore 3 G) ≠ 1 := by
    intro h
    have hb : pCore 3 G = ⊥ := Subgroup.card_eq_one.mp h
    exact d.noncentral (hb ▸ bot_le)
  have ho := threeCore_odd (G := G)
  have hc := Nat.coprime_two_right.mpr ho
  have hdiv3 := hc.dvd_of_dvd_mul_left (show Nat.card (pCore 3 G) ∣ 2 * 3 from hdiv)
  exact ((Nat.dvd_prime Nat.prime_three).mp hdiv3).resolve_left hone

/-- The cubic model is obtained from the faithful original action, not an abstract tag. -/
noncomputable def threeCoreEquiv_of_plane (hyp : FFHypothesis K ρ) {L : Subgroup G}
    (d : NoncentralContext K G L)
    (hd : Module.finrank (ZMod 2) (moved ρ (pCore 3 G)) = 2) :
    pCore 3 G ≃* Multiplicative (ZMod 3) := by
  let : IsCyclic (pCore 3 G) := threeCore_cyclic d
  apply mulEquivOfCyclicCardEq
  rw [threeCore_card_of_plane ρ hyp d hd]
  exact (Nat.card_zmod 3).symm
end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
