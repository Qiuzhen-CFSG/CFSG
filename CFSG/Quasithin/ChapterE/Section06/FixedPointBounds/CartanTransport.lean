module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter

/-!
# Cartan witnesses in the literal centralizer action

The surjection from `C_M(U)` to its actual image in `Aut_G(V)` has kernel
`C_M(U) ∩ C_G(V)`. A cyclic Cartan subgroup acts faithfully exactly when
its ambient image meets this centralizer trivially. Mapping the complete
E.3.37 witness then gives the required lower bound on `n'`. If it is not
faithful, its nontrivial kernel has odd order and lies in `C_M(V)`.

These transport arguments do not construct a Cartan subgroup or assert the
4.4.13 contradiction. Those steps require the marked E.2.2 alternatives
and the elementary abelian, permuting subgroup required by 4.4.13(1).

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Proposition
E.6.27, printed p.257 (PDF p.268).
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The actual action map onto `Aut_L(V)`. -/
def localAction (V L : Subgroup G) (hL : L ≤ normalizer (V : Set G)) :
    L →* inducedAutomizer V L :=
  (V.normalizerMonoidHom.rangeRestrict.comp (inclusion hL)).codRestrict _
    (fun x => ⟨inclusion hL x, x.property, rfl⟩)

omit [Finite G] in
theorem localAction_surjective (V L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) :
    Function.Surjective (localAction V L hL) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

omit [Finite G] in
theorem mem_ker_localAction (V L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) (x : L) :
    x ∈ (localAction V L hL).ker ↔ (x : G) ∈ centralizer (V : Set G) := by
  change localAction V L hL x = 1 ↔ _
  have hval : localAction V L hL x = 1 ↔
      V.normalizerMonoidHom (inclusion hL x) = 1 := by
    constructor
    · exact fun h => congrArg (fun a : inducedAutomizer V L => (a : MulAut V)) h
    · intro h
      exact Subtype.ext (Subtype.ext h)
  rw [hval, ← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

/-- Faithfulness on the cyclic subgroup suffices; the abelian overgroup
may still have a nontrivial action kernel. -/
theorem faithful_cartan_bound {V L : Subgroup G}
    (hL : L ≤ normalizer (V : Set G)) {c : ℕ} (w : NPrimeWitness L c)
    (hfaithful : w.cyclicGroup.map L.subtype ⊓ centralizer (V : Set G) = ⊥) :
    c ≤ nPrime (inducedAutomizer V L) := by
  apply (w.map (localAction V L hL) (localAction_surjective V L hL) ?_).le_nPrime
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hxC : ((x : L) : G) ∈ centralizer (V : Set G) :=
    (mem_ker_localAction V L hL x).mp hx
  have hxB : ((x : L) : G) ∈ w.cyclicGroup.map L.subtype :=
    mem_map_of_mem L.subtype x.property
  have hx1 : ((x : L) : G) = 1 := by
    have hh : ((x : L) : G) ∈ w.cyclicGroup.map L.subtype ⊓
        centralizer (V : Set G) := ⟨hxB, hxC⟩
    simpa only [hfaithful, mem_bot] using hh
  exact Subtype.ext (Subtype.ext hx1)

omit [Finite G] in
/-- The fixed subgroup in the nonfaithful branch is nontrivial, odd, and
contained in the literal local centralizer used by hypothesis (4). -/
theorem nonfaithful_cartan_fixed {V M U : Subgroup G} {c : ℕ}
    (w : NPrimeWitness ↥(M ⊓ centralizer (U : Set G)) c)
    (hfaithful : w.cyclicGroup.map (M ⊓ centralizer (U : Set G)).subtype ⊓
      centralizer (V : Set G) ≠ ⊥) :
    let X := w.cyclicGroup.map (M ⊓ centralizer (U : Set G)).subtype ⊓
      centralizer (V : Set G)
    X ≠ ⊥ ∧ X ≤ M ⊓ centralizer (V : Set G) ∧ Odd (Nat.card X) := by
  dsimp only
  refine ⟨hfaithful, le_inf
    (inf_le_left.trans ((map_subtype_le _).trans inf_le_left)) inf_le_right, ?_⟩
  have hodd : Odd (Nat.card w.cyclicGroup) :=
    w.odd.of_dvd_nat (card_dvd_of_le w.cyclic_le)
  have himage := hodd.of_dvd_nat
    (card_map_dvd w.cyclicGroup (M ⊓ centralizer (U : Set G)).subtype)
  exact himage.of_dvd_nat (card_dvd_of_le inf_le_left)

omit [Finite G] in
/-- The nontrivial cyclic kernel lies in the fixed subgroup of the whole
abelian odd overgroup, the source's `C_Y(V)`. -/
theorem nonfaithful_cartan_overgroup_fixed {V M U : Subgroup G} {c : ℕ}
    (w : NPrimeWitness ↥(M ⊓ centralizer (U : Set G)) c)
    (hfaithful : w.cyclicGroup.map (M ⊓ centralizer (U : Set G)).subtype ⊓
      centralizer (V : Set G) ≠ ⊥) :
    let X := w.abelianGroup.map (M ⊓ centralizer (U : Set G)).subtype ⊓
      centralizer (V : Set G)
    X ≠ ⊥ ∧ X ≤ M ⊓ centralizer (V : Set G) ∧ Odd (Nat.card X) := by
  dsimp only
  refine ⟨?_, le_inf
    (inf_le_left.trans ((map_subtype_le _).trans inf_le_left)) inf_le_right, ?_⟩
  · intro hbot
    apply hfaithful
    exact bot_unique ((inf_le_inf_right _ (map_mono w.cyclic_le)).trans hbot.le)
  · exact (w.odd.of_dvd_nat (card_map_dvd _ _)).of_dvd_nat
      (card_dvd_of_le inf_le_left)

/-- The numerical hypothesis forces a nontrivial odd fixed subgroup, and
the odd-local hypothesis controls its full ambient normalizer. -/
theorem odd_local_of_large_cartan {V M U : Subgroup G}
    (hL : M ⊓ centralizer (U : Set G) ≤ normalizer (V : Set G))
    {c j : ℕ} (w : NPrimeWitness ↥(M ⊓ centralizer (U : Set G)) c)
    (hlarge : j < c)
    (hn : nPrime (inducedAutomizer V (M ⊓ centralizer (U : Set G))) ≤ j)
    (hodd : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ M ⊓ centralizer (V : Set G) →
      Odd (Nat.card X) → normalizer (X : Set G) ≤ M) :
    let X := w.cyclicGroup.map (M ⊓ centralizer (U : Set G)).subtype ⊓
      centralizer (V : Set G)
    X ≠ ⊥ ∧ X ≤ M ⊓ centralizer (V : Set G) ∧ Odd (Nat.card X) ∧
      normalizer (X : Set G) ≤ M := by
  have hnf : w.cyclicGroup.map (M ⊓ centralizer (U : Set G)).subtype ⊓
      centralizer (V : Set G) ≠ ⊥ := by
    intro he
    exact hlarge.not_ge ((faithful_cartan_bound hL w he).trans hn)
  obtain ⟨hne, hle, ho⟩ := nonfaithful_cartan_fixed w hnf
  exact ⟨hne, hle, ho, hodd _ hne hle ho⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

end
