module
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.IsPerfect

/-!
# Nontrivial images above a simple quotient

Suppose every supplement of a normal subgroup K also supplements Q. If H/K
is simple and perfect, every nontrivial quotient image killing Q maps onto
that same H/K and is perfect. The new kernel is the actual image of K.
If K/Q is odd and nilpotent, so is that kernel.

The proof maps normal subgroups and commutators through the two actual
quotient maps; no perfection of H is assumed. This is the group transport
used after Niles's minimal-parabolic Frattini reduction, Lemma 2.2, in the
proof of Lemmas 2.8–2.9, “Pushing-up in finite groups”, printed pp. 32–33.
-/

public section
noncomputable section
open Subgroup
namespace Theory.GroupTheory.SimpleQuotientActionImage
variable {H J : Type*} [Group H] [Group J]

/-- A nontrivial image killing Q inherits perfection and the original simple
quotient, with its odd nilpotent kernel identified literally. -/
theorem structure_of_supplement_reduction
    (Q K : Subgroup H) [Q.Normal] [K.Normal]
    [IsSimpleGroup (H ⧸ K)] [Group.IsPerfect (H ⧸ K)]
    (hred : ∀ L : Subgroup H, L ⊔ K = ⊤ → L ⊔ Q = ⊤)
    (hnil : Group.IsNilpotent (K.map (QuotientGroup.mk' Q)))
    (hodd : ¬2 ∣ Nat.card (K.map (QuotientGroup.mk' Q)))
    (a : H →* J) (ha : Function.Surjective a)
    (hQ : Q ≤ a.ker) (hnt : a.ker ≠ ⊤) :
    a.ker ≤ K ∧ Group.IsPerfect J ∧
      ∃ q : J →* (H ⧸ K), Function.Surjective q ∧
        (∀ h, q (a h) = QuotientGroup.mk' K h) ∧
        q.ker = K.map a ∧ Group.IsNilpotent q.ker ∧ Odd (Nat.card q.ker) := by
  let π := QuotientGroup.mk' K
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective K
  have hk : a.ker ≤ K := by
    have hn : (a.ker.map π).Normal := (inferInstance : a.ker.Normal).map π hπ
    rcases hn.eq_bot_or_eq_top with hb | ht
    · simpa only [π, QuotientGroup.ker_mk'] using (map_eq_bot_iff a.ker).mp hb
    · have hh := congrArg (Subgroup.comap π) ht
      have ht' : a.ker ⊔ K = ⊤ := by
        simpa only [comap_map_eq,comap_top,π,QuotientGroup.ker_mk'] using hh
      exact (hnt (by simpa only [sup_of_le_left hQ] using hred a.ker ht')).elim
  have hp : Group.IsPerfect J := by
    have hdK : _root_.commutator H ⊔ K = ⊤ := by
      have hdmap : (_root_.commutator H).map π = ⊤ := by
        rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hπ]
        exact Group.IsPerfect.commutator_eq_top
      have hh := congrArg (Subgroup.comap π) hdmap
      simpa only [comap_map_eq,comap_top,π,QuotientGroup.ker_mk'] using hh
    have hdQ := hred (_root_.commutator H) hdK
    have hh := congrArg (Subgroup.map a) hdQ
    have hQa : Q.map a=⊥ := (map_eq_bot_iff Q).mpr hQ
    rw [Subgroup.map_sup,hQa,sup_bot_eq,map_top_of_surjective a ha,
      map_commutator_eq,MonoidHom.range_eq_top.mpr ha] at hh
    exact ⟨hh⟩
  let q := a.liftOfSurjective ha ⟨π,by simpa only [π,QuotientGroup.ker_mk'] using hk⟩
  have he (h : H) : q (a h) = π h := a.liftOfRightInverse_comp_apply _ _ _ h
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨h,rfl⟩ := hπ x
    exact ⟨a h,he h⟩
  have hqk : q.ker=K.map a := by
    ext x
    obtain ⟨h,rfl⟩ := ha x
    constructor
    · intro hh
      have hh' : π h=1 := (he h).symm.trans hh
      exact mem_map_of_mem a ((QuotientGroup.eq_one_iff h).mp hh')
    · rintro ⟨z,hz,hz'⟩
      change q (a h)=1
      rw [←hz',he]
      exact (QuotientGroup.eq_one_iff z).mpr hz
  let b := QuotientGroup.lift Q a hQ
  have heba : b.comp (QuotientGroup.mk' Q)=a := by ext h; rfl
  have hmap : (K.map (QuotientGroup.mk' Q)).map b=K.map a := by
    rw [Subgroup.map_map,heba]
  let _ := hnil
  have hnil' : Group.IsNilpotent (K.map a) := by
    rw [←hmap]
    exact Group.nilpotent_of_surjective (b.subgroupMap _) (b.subgroupMap_surjective _)
  have hdiv : Nat.card (K.map a) ∣ Nat.card (K.map (QuotientGroup.mk' Q)) := by
    rw [←hmap]
    exact Subgroup.card_dvd_of_surjective (b.subgroupMap _) (b.subgroupMap_surjective _)
  refine ⟨hk,hp,q,hq,he,hqk,hqk ▸ hnil',?_⟩
  rw [hqk]
  exact Nat.not_even_iff_odd.mp (fun heven=>hodd ((even_iff_two_dvd.mp heven).trans hdiv))
/-- A Frattini image modulo Q remains Frattini in every surjective image
whose kernel contains Q. -/
theorem map_le_frattini_of_quotient_image_le
    (Q K : Subgroup H) [Q.Normal]
    (hK : K.map (QuotientGroup.mk' Q) ≤ frattini (H ⧸ Q))
    (a : H →* J) (ha : Function.Surjective a) (hQ : Q ≤ a.ker) :
    K.map a ≤ frattini J := by
  let b := QuotientGroup.lift Q a hQ
  have hb : Function.Surjective b := QuotientGroup.lift_surjective_of_surjective Q a ha hQ
  have he : b.comp (QuotientGroup.mk' Q) = a := by ext h; rfl
  rw [←he, ←Subgroup.map_map]
  exact (Subgroup.map_mono hK).trans
    (map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective hb))

end Theory.GroupTheory.SimpleQuotientActionImage
