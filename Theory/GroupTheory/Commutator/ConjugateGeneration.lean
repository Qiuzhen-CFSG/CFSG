module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Commutators and conjugate generation

For subgroups `A i` contained in `Q`, the commutator of their join with `Q`
is the join of their commutators with `Q`. Each individual commutator is
normalized by `Q`, which makes the elementary product identity applicable
throughout the generated subgroup.

Consequently, if `L` normalizes `Q` and `U ≤ Q`, then
`[⟨U^L⟩, Q] = ⟨[U,Q]^L⟩`. We also prove a centralization criterion:
if the `L`-orbit of `U` consists of `U` and `P`-conjugates of `A`, then a
subgroup `E ≤ U` normalized by `P` and centralizing both `U` and `A`
has its entire `L`-generated subgroup in the center of `⟨U^L⟩`.

These are the group-theoretic arguments in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 14.7.13(1),(3),
combined manuscript dated 1 March 2004, printed p. 1046.
-/

namespace Subgroup

public theorem commutator_iSup_of_le {G : Type*} [Group G] {ι : Sort*}
    (A : ι → Subgroup G) (Q : Subgroup G) (hA : ∀ i, A i ≤ Q) :
    ⁅⨆ i, A i, Q⁆ = ⨆ i, ⁅A i, Q⁆ := by
  let R := ⨆ i, ⁅A i, Q⁆
  have hQR : Q ≤ normalizer R :=
    (le_iInf fun i => normalizer_commutator_ge_right (A i) Q).trans
      (iInf_normalizer_le_normalizer_iSup _)
  apply le_antisymm
  · apply commutator_le.mpr
    intro x hx q hq
    revert q
    induction hx using iSup_induction' with
    | hp i x hx =>
        intro q hq
        exact (le_iSup (fun i => ⁅A i, Q⁆) i) (commutator_mem_commutator hx hq)
    | h1 =>
        intro q hq
        simpa only [commutatorElement_one_left] using R.one_mem
    | hmul x y hx _ ihx ihy =>
        intro q hq
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact R.mul_mem
          ((mem_normalizer_iff.mp (hQR ((iSup_le hA) hx)) _).mp (ihy q hq))
          (ihx q hq)
  · exact iSup_le fun i => commutator_mono (le_iSup A i) le_rfl

public theorem iSup_conjugates_le_of_le_normalizer {G : Type*} [Group G] (U L Q : Subgroup G)
    (hUQ : U ≤ Q) (hLQ : L ≤ normalizer Q) :
    (⨆ l : L, U.map (MulAut.conj (l : G)).toMonoidHom) ≤ Q := by
  apply iSup_le
  intro l
  rw [← mem_normalizer_iff_map_conj_eq.mp (hLQ l.property)]
  exact map_mono hUQ

public theorem le_normalizer_iSup_conjugates {G : Type*} [Group G] (U L : Subgroup G) :
    L ≤ normalizer ((⨆ l : L, U.map (MulAut.conj (l : G)).toMonoidHom) : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro l hl x hx
  have hm : (⨆ k : L, U.map (MulAut.conj (k : G)).toMonoidHom).map
      (MulAut.conj l).toMonoidHom ≤
      ⨆ k : L, U.map (MulAut.conj (k : G)).toMonoidHom := by
    rw [map_iSup]
    apply iSup_le
    intro k
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    apply (le_iSup (fun k : L => U.map (MulAut.conj (k : G)).toMonoidHom)
      ⟨l * k, L.mul_mem hl k.property⟩)
    refine ⟨u, hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev, mul_assoc]
  exact hm (mem_map_of_mem (MulAut.conj l).toMonoidHom hx)

public theorem commutator_iSup_conjugates {G : Type*} [Group G] (U L Q : Subgroup G)
    (hUQ : U ≤ Q) (hLQ : L ≤ normalizer Q) :
    ⁅⨆ l : L, U.map (MulAut.conj (l : G)).toMonoidHom, Q⁆ =
      ⨆ l : L, (⁅U, Q⁆).map (MulAut.conj (l : G)).toMonoidHom := by
  rw [commutator_iSup_of_le _ Q]
  · apply iSup_congr
    intro l
    have hmap : Q.map (MulAut.conj (l : G)).toMonoidHom = Q :=
      mem_normalizer_iff_map_conj_eq.mp (hLQ l.property)
    rw [map_commutator, hmap]
  · intro l
    exact (le_iSup (fun l : L => U.map (MulAut.conj (l : G)).toMonoidHom) l).trans
      (iSup_conjugates_le_of_le_normalizer U L Q hUQ hLQ)

public theorem iSup_conjugates_le_centralizer {G : Type*} [Group G] (E L S : Subgroup G)
    (hLS : L ≤ normalizer S) (hES : ⁅E, S⁆ = ⊥) :
    (⨆ l : L, E.map (MulAut.conj (l : G)).toMonoidHom) ≤ centralizer S := by
  apply iSup_le
  intro l
  apply commutator_eq_bot_iff_le_centralizer.mp
  have hm := congrArg (fun A : Subgroup G => A.map (MulAut.conj (l : G)).toMonoidHom) hES
  have hmap : S.map (MulAut.conj (l : G)).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp (hLS l.property)
  simpa only [map_commutator, map_bot, hmap] using hm

public theorem iSup_conjugates_le_center_of_two_orbits {G : Type*} [Group G]
    (U E A L P : Subgroup G) (hEU : E ≤ U)
    (hPE : P ≤ normalizer E) (hEUcomm : ⁅E, U⁆ = ⊥) (hEA : ⁅E, A⁆ = ⊥)
    (hcover : ∀ l : L, U.map (MulAut.conj (l : G)).toMonoidHom = U ∨
      ∃ p : P, U.map (MulAut.conj (l : G)).toMonoidHom =
        A.map (MulAut.conj (p : G)).toMonoidHom) :
    (⨆ l : L, E.map (MulAut.conj (l : G)).toMonoidHom) ≤
      (⨆ l : L, U.map (MulAut.conj (l : G)).toMonoidHom) ⊓
      centralizer ((⨆ l : L, U.map (MulAut.conj (l : G)).toMonoidHom) : Subgroup G) := by
  apply le_inf
  · exact iSup_mono fun l => map_mono hEU
  · apply iSup_conjugates_le_centralizer E L _ (le_normalizer_iSup_conjugates U L)
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    apply iSup_le
    intro l
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    rcases hcover l with heq | ⟨p, heq⟩
    · simpa only [heq] using hEUcomm
    · rw [heq]
      have hm := congrArg
        (fun B : Subgroup G => B.map (MulAut.conj (p : G)).toMonoidHom) hEA
      have hmap : E.map (MulAut.conj (p : G)).toMonoidHom = E :=
        mem_normalizer_iff_map_conj_eq.mp (hPE p.property)
      simpa only [map_commutator, map_bot, hmap] using hm

end Subgroup
