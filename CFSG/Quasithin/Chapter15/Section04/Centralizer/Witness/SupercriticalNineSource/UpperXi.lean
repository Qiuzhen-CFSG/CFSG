module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SupercriticalNineSource.Lift
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SupercriticalNineSource.Opening

/-!
# Uppercase membership for the actual supercritical residual lifts

The original iterated quotient action is transported along the marked
isomorphism Y/O₂(Y) ≃ P. A normal nontrivial O₂(M), contained in the
original Sylow subgroup, provides the nontrivial two-core of YT required
by Chapter 1's H-family. This does not substitute properness for that
condition. Irreducibility on P/Φ(P) then gives uppercase Ξ membership.

Source: Aschbacher--Smith 15.4.10, printed p.1159, using Definition 1.3.1.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
open FamilySource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Both characteristic quotients carry the original conjugation action. -/
theorem normal_lift_frattini_action_compatible (T M : Subgroup G) (hTM : T ≤ M)
    (P : Subgroup (CoreQuotient M)) [P.Normal]
    (e : Chapter1.XiQuotient (lift M P) ≃* P)
    (he : ∀ y : lift M P,
      (e (QuotientGroup.mk' (pCore 2 (lift M P)) y) : CoreQuotient M) =
        quotientMap M ⟨(y : G), lift_le M P y.property⟩)
    (hn : T ≤ normalizer (lift M P : Set G))
    (t : T) (v : Chapter1.XiFrattiniQuotient (lift M P)) :
    let eF := QuotientGroup.congr _ _ e (frattini_map_equiv e)
    eF (Chapter1.xiFrattiniAction T (lift M P) hn t v) =
      quotientAut (frattini P)
        (MulAut.conjNormal (quotientMap M (inclusion hTM t))) (eF v) := by
  intro eF
  have hf (u : Chapter1.XiQuotient (lift M P)) :
      eF (QuotientGroup.mk' (frattini (Chapter1.XiQuotient (lift M P))) u) =
        QuotientGroup.mk' (frattini P) (e u) :=
    QuotientGroup.congr_mk' _ _ e (frattini_map_equiv e) u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective
    (frattini (Chapter1.XiQuotient (lift M P))) v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (lift M P)) v
  unfold Chapter1.xiFrattiniAction
  simp only [MonoidHom.coe_comp, Function.comp_apply, quotientAut_apply_mk]
  rw [hf, hf, quotientAut_apply_mk]
  apply congrArg (QuotientGroup.mk' (frattini P))
  apply Subtype.ext
  change (e (QuotientGroup.mk' (pCore 2 (lift M P)) _) : CoreQuotient M) =
    (MulAut.conjNormal (quotientMap M (inclusion hTM t))
      (e (QuotientGroup.mk' (pCore 2 (lift M P)) y)) : CoreQuotient M)
  rw [he, MulAut.conjNormal_apply, he]
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

/-- Characteristic two and nontriviality force a nontrivial original two-core. -/
theorem twoCore_ne_bot_of_nontrivial_overgroup (M X : Subgroup G)
    (hXM : X ≤ M) (hM : HasCharacteristicTwo M)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3) : M.pCoreIn 2 ≠ ⊥ := by
  intro hb
  have hi : pCore 2 M = ⊥ := by
    apply (Subgroup.map_injective M.subtype_injective)
    simpa only [pCoreIn, Subgroup.map_bot] using hb
  have ht : (⊤ : Subgroup M) ≤ ⊥ := by
    have hh := hM
    change centralizer (pCore 2 M : Set M) ≤ pCore 2 M at hh
    rw [hi] at hh
    intro x _
    apply hh
    intro y hy
    have hy1 : y = 1 := hy
    simp [hy1]
  have hX1 (x : X) : x = 1 := by
    apply Subtype.ext
    have hh : (⟨x, hXM x.property⟩ : M) = 1 := mem_bot.mp (ht (mem_top _))
    exact congrArg (fun m : M => (m : G)) hh
  let : Subsingleton X := ⟨fun x y => (hX1 x).trans (hX1 y).symm⟩
  have hc : Nat.card (X ⧸ pCore 2 X) = 1 := Nat.card_eq_one_iff_unique.mpr
    ⟨inferInstance, inferInstance⟩
  omega

/-- The literal residual lift belongs to uppercase Ξ whenever the odd
source quotient and original Sylow irreducibility have been established. -/
theorem normal_lift_mem_upper_Xi (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hMcore : M.pCoreIn 2 ≠ ⊥)
    (P : Subgroup (CoreQuotient M)) [P.Normal] (hp : IsPPerfect 2 P)
    (hshape : ∃ p : ℕ, p.Prime ∧ Odd p ∧ Chapter1.XiOddQuotient p P)
    (hirr : ∀ B : Subgroup (P ⧸ frattini P),
      (∀ t : T, ∀ b ∈ B, quotientAut (frattini P)
        (MulAut.conjNormal (quotientMap M (inclusion hTM t))) b ∈ B) → B = ⊥ ∨ B = ⊤) :
    lift M P ∈ Chapter1.Xi G (T : Subgroup G) := by
  let Y := lift M P
  have hYM : Y ≤ M := lift_le M P
  have hn : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    lift_normalized M T hTM P (by rw [normalizer_eq_top]; exact le_top)
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using
      pCoreIn_le_sylow M (T.subtype hTM)
  have hMQ : M ≤ normalizer (M.pCoreIn 2 : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hQjoin : M.pCoreIn 2 ≤ (Y ⊔ (T : Subgroup G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) (hQT.trans le_sup_right)
      ((sup_le hYM hTM).trans hMQ)
  have hH : Y ⊔ (T : Subgroup G) ∈ Chapter1.H G := by
    intro hb
    exact hMcore (le_bot_iff.mp (hb ▸ hQjoin))
  obtain ⟨e, he⟩ := normal_lift_quotient M P hp
  let eF := QuotientGroup.congr _ _ e (frattini_map_equiv e)
  refine ⟨lift_perfect M P, hn, hH, ?_, ?_⟩
  · obtain ⟨p, hp, ho, hs⟩ := hshape
    exact ⟨p, hp, ho, hs.of_mulEquiv e.symm⟩
  · intro A hA
    have hB : ∀ t : T, ∀ b ∈ A.map eF.toMonoidHom,
        quotientAut (frattini P)
          (MulAut.conjNormal (quotientMap M (inclusion hTM t))) b ∈ A.map eF.toMonoidHom := by
      rintro t b ⟨a, ha, rfl⟩
      have hc := normal_lift_frattini_action_compatible (T : Subgroup G) M hTM P e he hn t a
      change eF _ = _ at hc
      change quotientAut (frattini P)
        (MulAut.conjNormal (quotientMap M (inclusion hTM t))) (eF a) ∈ _
      rw [← hc]
      exact mem_map_of_mem eF.toMonoidHom (hA t a ha)
    rcases hirr _ hB with hb | ht
    · left
      apply (Subgroup.map_injective (f := eF.toMonoidHom) eF.injective)
      simpa only [Subgroup.map_bot] using hb
    · right
      apply (Subgroup.map_injective (f := eF.toMonoidHom) eF.injective)
      rw [← MonoidHom.range_eq_map, (MonoidHom.range_eq_top (f := eF.toMonoidHom)).mpr eF.surjective]
      exact ht

/-- The prime-five contradiction criterion for the source residual lift.
No quotient comparison or upper-family membership is left as a premise. -/
theorem five_lift_positive (T : Sylow 2 G) (M X : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M) (hM : HasCharacteristicTwo M)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (P : Subgroup (CoreQuotient M)) [P.Normal] (hp : IsPPerfect 2 P)
    (hshape : Chapter1.XiOddQuotient 5 P)
    (hirr : ∀ B : Subgroup (P ⧸ frattini P),
      (∀ t : T, ∀ b ∈ B, quotientAut (frattini P)
        (MulAut.conjNormal (quotientMap M (inclusion hTM t))) b ∈ B) → B = ⊥ ∨ B = ⊤)
    (m : M) (hm : orderOf (MulAut.conjNormal (quotientMap M m) : MulAut P) = 3) :
    lift M P ∈ Chapter3.XiPlus G (T : Subgroup G) := by
  have hXi := normal_lift_mem_upper_Xi T M hTM
    (twoCore_ne_bot_of_nontrivial_overgroup M X hXM hM hX3) P hp
    ⟨5, by decide, by decide, hshape⟩ hirr
  have h5 : 5 ∣ Nat.card P := by
    rcases hshape with ⟨_, hc⟩ | ⟨_, hc, _⟩ <;> rw [hc] <;> decide
  exact five_lift_mem_XiPlus T M P hp h5 hXi m hm

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
