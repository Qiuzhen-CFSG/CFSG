module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.TernaryLine

/-!
# The nine-group residual lift and its literal Frattini action

The residual preimage of an elementary nine-subgroup has that subgroup as
its two-core quotient. The quotient identification retains the original
projection on every element. Since the quotient is elementary, its
Frattini subgroup is trivial, and the same identification transports the
actual iterated quotient action in Definition 1.3.1.

Source: Aschbacher--Smith 15.4.9, printed p.1159.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SourceCubic
open FamilySource LocalSetup.TwoFactors.SourceFactors.Permutation
variable {G : Type*} [Group G] [Finite G]

private theorem nine_perfect {Q : Type*} [Group Q] (P : Subgroup Q)
    (hP : Nat.card P = 9) : IsPPerfect 2 P := by
  apply (pResidual_eq_top_iff 2 P).mp
  apply top_unique
  intro p _
  apply mem_pResidual_of_orderOf_coprime
  exact (by decide : Nat.Coprime 2 9).of_dvd_right (hP ▸ orderOf_dvd_natCard p)

private theorem residual_nine_quotient {Q : Type*} [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (P : Subgroup Q) (hP : Nat.card P = 9) :
    ∃ e : residualPreimage q P ⧸ pCore 2 (residualPreimage q P) ≃* P,
      ∀ x : residualPreimage q P,
        (e (QuotientGroup.mk' (pCore 2 (residualPreimage q P)) x) : Q) = q x := by
  let L := residualPreimage q P
  have him : L.map q = P := residualPreimage_image q hq P (nine_perfect P hP)
  let f := q.subgroupMap L
  have hf := q.subgroupMap_surjective L
  have hfk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let _ : Finite (L.map q) := Finite.of_surjective _ hf
  have hc : Nat.card (L.map q) = 9 := him ▸ hP
  have hp3 : IsPGroup 3 (L.map q) := IsPGroup.of_card (n := 2) (by simpa using hc)
  have hcore : pCore 2 (L.map q) = ⊥ := by
    have hd := IsPGroup.disjoint_of_coprime (pCore_isPGroup (p := 2))
      (hp3.to_subgroup ⊤) (by decide : Nat.Coprime 2 3)
    simpa using hd
  have hker : f.ker = pCore 2 L := by
    simpa only [hcore, MonoidHom.comap_bot] using f.comap_pCore_of_ker_isPGroup hf hfk
  let e : L ⧸ pCore 2 L ≃* P :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective f hf).trans (MulEquiv.subgroupCongr him))
  exact ⟨e, fun x => rfl⟩

/-- The nine-group residual quotient keeps the exact original projection. -/
theorem nine_lift_quotient (H : Subgroup G) (P : Subgroup (CoreQuotient H))
    (hP : Nat.card P = 9) :
    ∃ e : Chapter1.XiQuotient (lift H P) ≃* P,
      ∀ x : lift H P,
        (e (QuotientGroup.mk' (pCore 2 (lift H P)) x) : CoreQuotient H) =
          quotientMap H ⟨(x : G), lift_le H P x.property⟩ := by
  have hk : IsPGroup 2 (quotientMap H).ker := by
    rw [quotientMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨e, he⟩ := residual_nine_quotient (quotientMap H)
    (QuotientGroup.mk'_surjective _) hk P hP
  let f := ((residualPreimage (quotientMap H) P).equivMapOfInjective H.subtype H.subtype_injective).symm
  let e' := (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e
  refine ⟨e', ?_⟩
  intro x
  change (e (QuotientGroup.mk' _ (f x)) : CoreQuotient H) = _
  rw [he]
  congr 1
  apply Subtype.ext
  have hh := congrArg Subtype.val (f.symm_apply_apply x)
  exact hh

/-- The iterated Frattini quotient of the lift identifies with the same
elementary nine-group, compatibly with the original projection. -/
theorem nine_lift_frattini_quotient (H : Subgroup G)
    (P : Subgroup (CoreQuotient H)) [IsElementaryAbelian 3 P] (hP : Nat.card P = 9) :
    ∃ e : Chapter1.XiFrattiniQuotient (lift H P) ≃* P,
      ∀ x : lift H P,
        (e (QuotientGroup.mk' (frattini (Chapter1.XiQuotient (lift H P)))
          (QuotientGroup.mk' (pCore 2 (lift H P)) x)) : CoreQuotient H) =
          quotientMap H ⟨(x : G), lift_le H P x.property⟩ := by
  obtain ⟨e, he⟩ := nine_lift_quotient H P hP
  let : IsElementaryAbelian 3 (Chapter1.XiQuotient (lift H P)) :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  let : Fact (IsPGroup 3 (Chapter1.XiQuotient (lift H P))) :=
    ⟨IsElementaryAbelian.isPGroup (p := 3) (G := Chapter1.XiQuotient (lift H P))⟩
  let f := (frattiniQuotientEquivOfIsElementaryAbelian (p := 3)).trans e
  exact ⟨f, fun x => he x⟩

omit [Finite G] in
/-- Conjugation through the actual iterated quotient agrees with the
literal centralizer quotient map; no model action is substituted. -/
theorem nine_lift_action_compatible (T H : Subgroup G) (hTH : T ≤ H)
    (P : Subgroup (CoreQuotient H))
    (hn : T ≤ normalizer (lift H P : Set G))
    (e : Chapter1.XiFrattiniQuotient (lift H P) ≃* P)
    (he : ∀ x : lift H P,
      (e (QuotientGroup.mk' (frattini (Chapter1.XiQuotient (lift H P)))
        (QuotientGroup.mk' (pCore 2 (lift H P)) x)) : CoreQuotient H) =
        quotientMap H ⟨(x : G), lift_le H P x.property⟩)
    (t : T) (a : Chapter1.XiFrattiniQuotient (lift H P)) :
    (e (Chapter1.xiFrattiniAction T (lift H P) hn t a) : CoreQuotient H) =
      quotientMap H ⟨(t : G), hTH t.property⟩ * (e a : CoreQuotient H) *
        (quotientMap H ⟨(t : G), hTH t.property⟩)⁻¹ := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (frattini (Chapter1.XiQuotient (lift H P))) a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (lift H P)) a
  unfold Chapter1.xiFrattiniAction
  simp only [MonoidHom.coe_comp, Function.comp_apply, quotientAut_apply_mk]
  rw [he, he]
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SourceCubic
