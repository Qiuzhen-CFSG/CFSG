module

public import CFSG.Quasithin.ChapterI.Section06To08.TightNormalizer.Basic
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# The normal closure and the product branch of I.7.7

The source's `W = ⟨Rˢ⟩` is the normal closure in `S`, embedded back in the
ambient group. We prove its universal property, the internal direct-product
conclusion when it equals `RS₁`, and the corrected intersection identity
`S₀ ∩ W = S₁` giving relative normality. The Frattini reduction uses I.7.5
on the actual conjugates inside `S`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, I.7.7(5--6), printed pp.427--428.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G]

/-- The normal closure of `R ∩ S` inside `S`, embedded in the ambient group.
All applications below have `R ≤ S`. This is not the ambient normal closure. -/
def tightNormalClosure (R S : Subgroup G) : Subgroup G :=
  (normalClosure (R.subgroupOf S : Set S)).map S.subtype

namespace TightNormalizerSetup
variable {K : Subgroup G} {g : G} {R S : Subgroup G}
variable (h : TightNormalizerSetup K g R S)
include h

omit h in
theorem normalClosure_le (R S : Subgroup G) : tightNormalClosure R S ≤ S := map_subtype_le _

theorem le_normalClosure : R ≤ tightNormalClosure R S := by
  calc
    R = (R.subgroupOf S).map S.subtype := (map_subgroupOf_eq_of_le h.hRS).symm
    _ ≤ tightNormalClosure R S := map_mono Subgroup.le_normalClosure

omit h in
theorem normalClosure_normal (R S : Subgroup G) : ((tightNormalClosure R S).subgroupOf S).Normal := by
  change (((normalClosure (R.subgroupOf S : Set S)).map S.subtype).comap S.subtype).Normal
  rw [comap_map_eq_self_of_injective S.subtype_injective]
  infer_instance

omit h in
theorem normalClosure_min {T : Subgroup G} (hT : (T.subgroupOf S).Normal)
    (hRT : R ≤ T) : tightNormalClosure R S ≤ T := by
  let : (T.comap S.subtype).Normal := hT
  apply map_le_iff_le_comap.mpr
  apply normalClosure_le_normal
  exact fun _ hx => hRT hx

theorem conjugate_le_normalClosure {s : G} (hs : s ∈ S) :
    conjSubgroup R s ≤ tightNormalClosure R S := by
  rintro x ⟨r, hr, rfl⟩
  have hn := (normal_subgroupOf_iff_le_normalizer (normalClosure_le R S)).mp
    (normalClosure_normal R S) hs
  exact (hn r).mp (h.le_normalClosure hr)

theorem normalClosure_le_iff {T : Subgroup G} : tightNormalClosure R S ≤ T ↔
    ∀ s : G, s ∈ S → conjSubgroup R s ≤ T := by
  constructor
  · exact fun hWT s hs => (h.conjugate_le_normalClosure hs).trans hWT
  · intro hT
    apply map_le_iff_le_comap.mpr
    change closure (Group.conjugatesOfSet (R.subgroupOf S : Set S)) ≤ _
    rw [Subgroup.closure_le]

    intro x hx
    obtain ⟨r, hr, hrx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨s, rfl⟩ := isConj_iff.mp hrx
    exact hT s s.property ⟨r, hr, rfl⟩

variable [Finite G]

theorem intersection_disjoint : Disjoint (S ⊓ conjSubgroup K g) R :=
  h.disjoint_conjugate.symm.mono inf_le_right le_rfl

omit [Finite G] in
/-- The intersection needed in the product branch is with `S₀`, not with `S`. -/
theorem intersection_inf_normalizer_sup :
    (S ⊓ conjSubgroup K g) ⊓
      (R ⊔ ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))) =
        (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) := by
  rw [sup_comm, ← h.normalizer_eq_sup, ← inf_assoc, inf_eq_left.mpr inf_le_left]

/-- The multiplication map in branch (b), together with the square isomorphism
and relative normality. The additional equality is discharged by the branch split. -/
theorem productBranch
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hW : tightNormalClosure R S =
      R ⊔ ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))) :
    let S0 := S ⊓ conjSubgroup K g
    let S1 := S0 ⊓ normalizer (R : Set G)
    (∃ f : R × S1 ≃* tightNormalClosure R S,
      ∀ r s, (f (r, s) : G) = (r : G) * (s : G)) ∧
    Nonempty (tightNormalClosure R S ≃* R × R) ∧
    S0 ⊓ tightNormalClosure R S = S1 ∧
    (S1.subgroupOf S0).Normal := by
  dsimp
  have hc : R ≤ centralizer
      (↑((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) : Set G) := by
    apply le_centralizer_iff.mpr
    rw [h.normalizer_eq_centralizer]
    exact inf_le_right
  obtain ⟨f, hf⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting R
    ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))
    (h.intersection_disjoint.symm.mono le_rfl inf_le_left) hc
  let fW := f.trans (MulEquiv.subgroupCongr hW.symm)
  have hi : (S ⊓ conjSubgroup K g) ⊓ tightNormalClosure R S =
      (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) := by
    rw [hW]
    exact h.intersection_inf_normalizer_sup
  refine ⟨⟨fW, hf⟩, ⟨fW.symm.trans ((MulEquiv.refl R).prodCongr e)⟩, hi, ?_⟩
  rw [← hi]
  apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
  apply le_trans _ inf_normalizer_le_normalizer_inf
  exact le_inf (S ⊓ conjSubgroup K g).le_normalizer
    (inf_le_left.trans ((normal_subgroupOf_iff_le_normalizer (normalClosure_le R S)).mp
      (normalClosure_normal R S)))

/-- I.7.5 forces the normal closure into the relative normalizer when
`R` has nontrivial Frattini subgroup. No commutativity assumption is needed. -/
theorem normalClosure_le_normalizer_of_frattini_ne_bot (hΦ : frattini R ≠ ⊥) :
    tightNormalClosure R S ≤ S ⊓ normalizer (R : Set G) := by
  refine le_inf (normalClosure_le R S) ?_
  apply h.normalClosure_le_iff.mpr
  intro s hs
  by_cases heq : conjSubgroup R s = R
  · rw [heq]
    exact R.le_normalizer
  · have hfamily := h.pgroupSetup.family_conjugate h.pgroupSetup.mem_family hs
    obtain ⟨_, hc⟩ := lemma_I_7_5_commuting h.pgroupSetup hΦ
      h.pgroupSetup.mem_family hfamily (Ne.symm heq)
    exact (le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _)


/-- In the proper-normalizer case, the normal closure contains the full
relative normalizer. A second conjugate and `R` already generate it. -/
theorem normalizer_le_normalClosure
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g) :
    S ⊓ normalizer (R : Set G) ≤ tightNormalClosure R S := by
  let N := S ⊓ normalizer (R : Set G)
  have hNS : N ≤ S := inf_le_left
  have hRN : R ≤ N := le_inf h.hRS R.le_normalizer
  have hnproper : N.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hSN : S ≤ N := subgroupOf_eq_top.mp htop
    exact hp.not_ge (le_inf le_rfl (inf_le_left.trans (hSN.trans inf_le_right)))
  let : Group.IsNilpotent S := h.hSp.isNilpotent
  obtain ⟨s, hsN, hsnot⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (N.subgroupOf S) hnproper)
  have hsNorm : (s : G) ∈ normalizer (N : Set G) := by
    rw [← subgroupOf_normalizer_eq hNS] at hsN
    exact hsN
  have hsR : (s : G) ∉ normalizer (R : Set G) := fun hs => hsnot ⟨s.property, hs⟩
  have hne : conjSubgroup R s ≠ R := fun heq =>
    hsR (mem_normalizer_iff_map_conj_eq.mpr heq)
  have hconj : conjSubgroup R s ≤ N :=
    (conjSubgroup_mono hRN s).trans_eq (mem_normalizer_iff_map_conj_eq.mp hsNorm)
  obtain ⟨f, _⟩ := lemma_I_7_4 h.pgroupSetup (h.hSle s.property) hne hconj
  obtain ⟨_, _, d, _⟩ := h.directProduct
  have hcard : Nat.card ↥(R ⊔ conjSubgroup R s) = Nat.card N := by
    rw [← Nat.card_congr f.toEquiv, ← Nat.card_congr d.toEquiv, Nat.card_prod,
      Nat.card_prod, Nat.card_congr e.toEquiv, card_conjSubgroup]
  have heq : R ⊔ conjSubgroup R s = N :=
    eq_of_le_of_card_ge (sup_le hRN hconj) hcard.symm.le
  rw [show S ⊓ normalizer (R : Set G) = N from rfl, ← heq]
  exact sup_le h.le_normalClosure (h.conjugate_le_normalClosure s.property)

/-- Once the product branch is excluded, I.7.5 gives a trivial Frattini
subgroup, hence a genuine elementary abelian two-group. -/
theorem elementary_of_normalClosure_ne_product
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hW : tightNormalClosure R S ≠
      R ⊔ ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))) :
    IsElementaryAbelian 2 R := by
  have hΦ : frattini R = ⊥ := by
    by_contra hΦ
    apply hW
    exact (le_antisymm (h.normalClosure_le_normalizer_of_frattini_ne_bot hΦ)
      (h.normalizer_le_normalClosure e hp)).trans (h.normalizer_eq_sup.trans (sup_comm _ _))
  let : Fact (IsPGroup 2 R) := ⟨h.hRp⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hΦ


/-- The remaining branch has the actual binary vector-space model, with the
source lower bound on its dimension. -/
theorem elementaryModel_of_normalClosure_ne_product
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hR2 : Nat.card R ≠ 2)
    (hW : tightNormalClosure R S ≠
      R ⊔ ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (R ≃* Multiplicative (Fin n → ZMod 2)) ∧
      Nat.card R = 2 ^ n := by
  classical
  let : IsElementaryAbelian 2 R := h.elementary_of_normalClosure_ne_product e hp hW
  let n := Module.finrank (ZMod 2) (Additive R)
  have hc : Nat.card R = 2 ^ n := by
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive R)
    change Nat.card R = _ at hcard
    simpa only [Nat.card_zmod] using hcard
  have hn : 2 ≤ n := by
    by_contra hn
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with hn' | hn'
    · have hc1 : Nat.card R = 1 := by simpa [hn'] using hc
      exact h.hRne (eq_bot_of_card_le R hc1.le)
    · exact hR2 (by simpa [hn'] using hc)
  exact ⟨n, hn, ⟨(Module.finBasis (ZMod 2) (Additive R)).equivFun.toAddEquiv.toMultiplicativeRight⟩, hc⟩

/-- The non-product branch is a strict enlargement of the relative normalizer. -/
theorem normalizer_lt_normalClosure
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hW : tightNormalClosure R S ≠
      R ⊔ ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))) :
    S ⊓ normalizer (R : Set G) < tightNormalClosure R S := by
  refine lt_of_le_of_ne (h.normalizer_le_normalClosure e hp) ?_
  intro heq
  exact hW (heq.symm.trans (h.normalizer_eq_sup.trans (sup_comm _ _)))


omit h [Finite G] in
/-- Conjugation inside `S` transports the actual relative normalizer. -/
theorem conjugate_normalizer {s : G} (hs : s ∈ S) :
    conjSubgroup (S ⊓ normalizer (R : Set G)) s =
      S ⊓ normalizer (conjSubgroup R s : Set G) := by
  change (S ⊓ normalizer (R : Set G)).map (MulAut.conj s).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj s).injective,
    map_normalizer_eq_of_bijective R (MulAut.conj s).bijective]
  rw [show S.map (MulAut.conj s).toMonoidHom = S from
    mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs)]
  rfl

/-- The comparison isomorphism and abelianness of `R` make its relative
normalizer abelian. -/
theorem normalizer_commutative [IsMulCommutative R]
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R) :
    IsMulCommutative ↥(S ⊓ normalizer (R : Set G)) := by
  obtain ⟨_, _, d, _⟩ := h.directProduct
  let f := d.symm.trans (e.prodCongr (MulEquiv.refl R))
  apply IsMulCommutative.of_comm
  intro x y
  apply f.injective
  simp only [map_mul, mul_comm]

/-- A conjugate which normalizes `N = N_S(R)` without lying in `N`.
The conjugating element is chosen in the normalizer of `N_S(N)`.
The printed proof's claim that it lies in `N_S(N)` cannot hold: such an
element would send `R ≤ N` back into `N`. -/
theorem exists_conjugate_in_second_normalizer [IsMulCommutative R]
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hW : tightNormalClosure R S ≠
      R ⊔ ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))) :
    ∃ y : G, y ∈ S ∧
      conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G) ∧
      ¬ conjSubgroup R y ≤ S ⊓ normalizer (R : Set G) := by
  let N := S ⊓ normalizer (R : Set G)
  let N1 := S ⊓ normalizer (N : Set G)
  have hNS : N ≤ S := inf_le_left
  have hRN : R ≤ N := le_inf h.hRS R.le_normalizer
  have hNN1 : N ≤ N1 := le_inf hNS N.le_normalizer
  have hN1S : N1 ≤ S := inf_le_left
  have hnproper : N1.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hSN1 : S ≤ N1 := subgroupOf_eq_top.mp htop
    have hn : (N.subgroupOf S).Normal :=
      (normal_subgroupOf_iff_le_normalizer hNS).mpr (hSN1.trans inf_le_right)
    have hWN : tightNormalClosure R S ≤ N := normalClosure_min hn hRN
    exact (h.normalizer_lt_normalClosure e hp hW).not_ge hWN
  let : Group.IsNilpotent S := h.hSp.isNilpotent
  obtain ⟨y, hyN, hynot⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (N1.subgroupOf S) hnproper)
  have hyNorm : (y : G) ∈ normalizer (N1 : Set G) := by
    rw [← subgroupOf_normalizer_eq hN1S] at hyN
    exact hyN
  have hconj : conjSubgroup R y ≤ N1 :=
    (conjSubgroup_mono (hRN.trans hNN1) y).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp hyNorm)
  refine ⟨y, y.property, hconj, ?_⟩
  intro hRyN
  let : IsMulCommutative N := h.normalizer_commutative e
  have hNC : N ≤ S ⊓ normalizer (conjSubgroup R y : Set G) := by
    refine le_inf hNS (le_trans ?_ (centralizer_le_normalizer _))
    intro x hx a ha
    exact setLike_mul_comm (s := N) (hRyN ha) hx
  have hconjN : conjSubgroup N y = S ⊓ normalizer (conjSubgroup R y : Set G) :=
    conjugate_normalizer y.property
  have hNconj : N = conjSubgroup N y :=
    eq_of_le_of_card_ge (hNC.trans_eq hconjN.symm) (card_conjSubgroup N y).le
  exact hynot ⟨y.property, mem_normalizer_iff_map_conj_eq.mpr hNconj.symm⟩


/-- The escaping conjugate from the normalizer construction has trivial
relative normalizer on `R`, by I.7.6. -/
theorem exists_conjugate_with_trivial_normalizer [IsMulCommutative R]
    (e : ↥((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G)) ≃* R)
    (hp : (S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G) < S ⊓ conjSubgroup K g)
    (hW : tightNormalClosure R S ≠
      R ⊔ ((S ⊓ conjSubgroup K g) ⊓ normalizer (R : Set G))) :
    ∃ y : G, y ∈ S ∧
      conjSubgroup R y ≤ S ⊓ normalizer (↑(S ⊓ normalizer (R : Set G)) : Set G) ∧
      ¬ conjSubgroup R y ≤ S ⊓ normalizer (R : Set G) ∧
      conjSubgroup R y ⊓ normalizer (R : Set G) = ⊥ := by
  obtain ⟨y, hy, hRy, hnot⟩ := h.exists_conjugate_in_second_normalizer e hp hW
  refine ⟨y, hy, hRy, hnot, ?_⟩
  by_contra hn
  have hne : conjSubgroup R y ≠ R := by
    intro heq
    apply hnot
    rw [heq]
    exact le_inf h.hRS R.le_normalizer
  obtain ⟨_, hc⟩ := lemma_I_7_6_commuting h.pgroupSetup (h.hSle hy) hne
    (hRy.trans inf_le_left) hn
  exact hnot (le_inf (hRy.trans inf_le_left)
    ((le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _)))

end TightNormalizerSetup
end CFSG.Quasithin.ChapterI.Section06To08
