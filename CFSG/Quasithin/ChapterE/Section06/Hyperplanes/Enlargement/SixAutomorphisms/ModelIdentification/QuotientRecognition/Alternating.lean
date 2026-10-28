module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Action
public import Theory.Alternating.Aut
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# The alternating branch of quotient recognition

Orders exclude degrees at most six. For degree seven, every automorphism
comes from S₇, whose involution centralizers have orders 240 or 48. The
faithfully embedded A₆ cannot lie in one of them. The remaining degree
eight is transported by the actual exceptional A₈ ≃ PSL₄(2) equivalence.

Source: Aschbacher–Smith, Theorem C, printed p.33, and E.6.23, p.254;
GLS, Volume 3, Theorem 5.2.1 for alternating automorphisms.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
variable {G : Type*} [Group G] [Finite G] {M V U A L X Y : Subgroup G} {g : G}

private theorem seven_involution_centralizer_card (s : Equiv.Perm (Fin 7))
    (hs : orderOf s = 2) :
    Nat.card (centralizer ({s} : Set (Equiv.Perm (Fin 7)))) < 360 := by
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order (hs ▸ Nat.prime_two)
  rw [hs] at hk
  have hb := s.sum_cycleType_le
  rw [hk] at hb
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hb
  have hkb : k ≤ 2 := by omega
  rw [Equiv.Perm.nat_card_centralizer, hk]
  interval_cases k <;> norm_num

theorem not_quotient_seven [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    (e : (Y ⧸ center Y) ≃* alternatingGroup (Fin 7)) : False := by
  obtain ⟨a, ha, hfix⟩ := quotient_involution d hY
  obtain ⟨s, hs⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by decide) (by decide)).surjective (MulAut.congr e a)
  have hs2 : orderOf s = 2 := by
    rw [← orderOf_injective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
      (GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7 (by decide)),
      hs]
    exact (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective a).trans ha
  let f : X →* Equiv.Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp
    (e.toMonoidHom.comp ((QuotientGroup.mk' (center Y)).comp (inclusion hY.proper.le)))
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (e.injective.comp (six_quotient_embedding_injective d hY))
  have hfc (x : X) : f x ∈ centralizer ({s} : Set (Equiv.Perm (Fin 7))) := by
    have he := congrArg (fun b : MulAut (alternatingGroup (Fin 7)) =>
      (b (e (QuotientGroup.mk' (center Y) (inclusion hY.proper.le x))) :
        Equiv.Perm (Fin 7))) hs
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at he
    change s * f x * s⁻¹ =
      ((e (a (QuotientGroup.mk' (center Y) (inclusion hY.proper.le x)))) :
        Equiv.Perm (Fin 7)) at he
    rw [hfix] at he
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm
  have hc := Nat.card_le_card_of_injective (fun x => (⟨f x, hfc x⟩ :
    centralizer ({s} : Set (Equiv.Perm (Fin 7)))))
    (fun x y h => hf (congrArg (fun z :
      centralizer ({s} : Set (Equiv.Perm (Fin 7))) => z.val) h))
  obtain ⟨eX⟩ := d.six.model
  rw [Nat.card_congr eX.toEquiv, nat_card_alternatingGroup] at hc
  norm_num at hc
  exact (Nat.not_lt_of_ge hc) (seven_involution_centralizer_card s hs2)

/-- Screen every alternating alternative of the full Theorem C list. -/
theorem alternating_quotient [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    {n : ℕ} (hn : n ≤ 8) (e : (Y ⧸ center Y) ≃* alternatingGroup (Fin n)) :
    ClassicalGroup.IsPSL (Y ⧸ center Y) 4 2 := by
  have hlarge := quotient_card_gt_six d hY
  have hn6 : ¬ n ≤ 6 := by
    intro hsmall
    have hc : Nat.card (alternatingGroup (Fin n)) ≤ 360 := by
      interval_cases n
      · rw [Nat.card_unique]; decide
      · rw [Nat.card_unique]; decide
      all_goals rw [nat_card_alternatingGroup]; norm_num
    rw [← Nat.card_congr e.toEquiv] at hc
    omega
  have hn7 : n ≠ 7 := by
    rintro rfl
    exact not_quotient_seven d hY e
  have hn8 : n = 8 := by omega
  subst n
  exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
    ⟨e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two⟩⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
