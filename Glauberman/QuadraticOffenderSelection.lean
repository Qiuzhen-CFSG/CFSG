module

public import Glauberman.Theorem3_1
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Quadratic offenders outside a normal subgroup

Let `S` be a finite p-group, `Q ≤ S`, and let the abelian subgroup `V ≤ S`
be normalized by `S` and centralize `Q`. If the all-abelian Thompson subgroup
of `S` is not contained in `Q`, choose a maximum-order abelian subgroup
outside `Q` with largest intersection with `V`. Thompson replacement makes
its action on `V` quadratic. Maximal abelian order also gives the offender
bound, measured against its image modulo `Q`.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 2.9, printed p.33,
the construction of `A` and assertions (2), (4), and (5). Central fixed
attachments in `V` are retained throughout.
-/

public section
open Subgroup
namespace Glauberman

variable {G : Type*} [Group G] [Finite G]

/-- A maximum-order abelian subgroup contains every subgroup of `S` which
centralizes it. -/
theorem le_maximum_abelian_of_centralizes {S A B : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups S) (hBS : B ≤ S)
    (hBA : B ≤ centralizer (A : Set G)) : B ≤ A := by
  rw [← thompsonAbelianSubgroups_centralizer_eq hA]
  exact le_inf hBA hBS

/-- The fixed subgroup on an abelian normal layer is its literal intersection
with a maximum-order abelian subgroup. -/
theorem centralizer_intersection_maximum_abelian {S A V : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups S) (hVS : V ≤ S) :
    V ⊓ centralizer (A : Set G) = A ⊓ V := by
  apply le_antisymm
  · exact le_inf (le_maximum_abelian_of_centralizes hA
      (inf_le_left.trans hVS) inf_le_right) inf_le_left
  · exact le_inf inf_le_right
      (inf_le_left.trans ((le_centralizer_iff_isMulCommutative).mpr hA.2.1))

/-- Maximal abelian order bounds the fixed-space index by the order of the
actor's image modulo `Q`, as in Niles 2.9(4). -/
theorem maximum_abelian_offender_bound {S Q V A : Subgroup G}
    (hA : A ∈ thompsonAbelianSubgroups S) (hVS : V ≤ S)
    (hVQ : V ≤ Q) (hVc : IsMulCommutative V)
    (hcentral : V ≤ centralizer (Q : Set G)) :
    (V ⊓ centralizer (A : Set G)).relIndex V ≤ Q.relIndex A := by
  let B := A ⊓ Q
  have hBV : V ≤ centralizer (B : Set G) :=
    hcentral.trans (centralizer_le inf_le_right)
  have hBc : IsMulCommutative B := by
    let _ := hA.2.1
    exact IsMulCommutative.of_setLike_mul_comm fun _ hx _ hy =>
      setLike_mul_comm hx.1 hy.1
  have hjoin : IsMulCommutative (B ⊔ V : Subgroup G) := by
    let _ := hBc
    let _ := hVc
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · exact le_centralizer_iff.mpr (sup_le B.le_centralizer hBV)
    · exact le_centralizer_iff.mpr
        (sup_le (le_centralizer_iff.mp hBV) V.le_centralizer)
  have hbound : Nat.card ↥(B ⊔ V) ≤ Nat.card A :=
    hA.2.2 _ (sup_le (inf_le_left.trans hA.1) hVS) hjoin
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes B V
    (hBV.trans (Subgroup.centralizer_le_normalizer _))
  have hinter : B ⊓ V = A ⊓ V := by
    ext x
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hVQ h.2⟩,h.2⟩⟩
  rw [hinter] at hprod
  have hVcard := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ V) V
    bot_le inf_le_right
  have hAcard := relIndex_mul_relIndex (⊥ : Subgroup G) B A
    bot_le inf_le_left
  simp only [relIndex_bot_left] at hVcard hAcard
  rw [centralizer_intersection_maximum_abelian hA hVS,
    ← inf_relIndex_left A Q]
  have hp1 : 0 < Nat.card B := Nat.card_pos
  have hp2 : 0 < Nat.card ↥(A ⊓ V) := Nat.card_pos
  have hh := Nat.mul_le_mul_left (Nat.card ↥(A ⊓ V)) hbound
  rw [← hprod, ← hVcard, ← hAcard] at hh
  have hh' : (Nat.card B * Nat.card ↥(A ⊓ V)) * (A ⊓ V).relIndex V ≤
      (Nat.card B * Nat.card ↥(A ⊓ V)) * B.relIndex A := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hh
  exact Nat.le_of_mul_le_mul_left hh' (Nat.mul_pos hp1 hp2)

/-- The source selection and quadraticity argument in Niles 2.9. -/
theorem exists_quadratic_maximum_abelian_outside
    {p : ℕ} [Fact p.Prime] (S Q V : Subgroup G)
    (hSp : IsPGroup p S) (hVS : V ≤ S) (hVc : IsMulCommutative V)
    (hSV : S ≤ normalizer (V : Set G))
    (hVQ : V ≤ centralizer (Q : Set G))
    (hJ : ¬ thompsonSubgroup S ≤ Q) :
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups S ∧ ¬ A ≤ Q ∧
      (∀ B : Subgroup G, B ∈ thompsonAbelianSubgroups S → ¬ B ≤ Q →
        Nat.card ↥(B ⊓ V) ≤ Nat.card ↥(A ⊓ V)) ∧
      ⁅⁅V, A⁆, A⁆ = ⊥ := by
  classical
  let t : Set (Subgroup G) := {A | A ∈ thompsonAbelianSubgroups S ∧ ¬ A ≤ Q}
  have ht : t.Nonempty := by
    by_contra hn
    apply hJ
    apply sSup_le
    intro A hA
    by_contra hAQ
    exact hn ⟨A, hA, hAQ⟩
  obtain ⟨A, hA, hmax⟩ := Set.exists_max_image t
    (fun B : Subgroup G => Nat.card ↥(B ⊓ V)) (Set.toFinite t) ht
  refine ⟨A, hA.1, hA.2, fun B hB hBQ => hmax B ⟨hB, hBQ⟩, ?_⟩
  by_contra hnonquad
  obtain ⟨B, hB, hlt, hquad⟩ :=
    theorem3_1b hSp hA.1 hVS hVc (hA.1.1.trans hSV) hnonquad
  have hBQ : ¬ B ≤ Q := by
    intro hBQ
    have hVB : V ≤ B := le_maximum_abelian_of_centralizes hB hVS
      (hVQ.trans (centralizer_le hBQ))
    have hzero : ⁅⁅V, A⁆, A⁆ ≤ ⊥ :=
      (commutator_mono (commutator_mono hVB le_rfl) le_rfl).trans_eq hquad
    exact hnonquad (le_bot_iff.mp hzero)
  have hcard := hmax B ⟨hB, hBQ⟩
  exact hlt.ne (eq_of_le_of_card_ge hlt.le hcard)

end Glauberman
