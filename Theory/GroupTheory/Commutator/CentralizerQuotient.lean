module
public import Theory.GroupTheory.Commutator.CentralRow
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import Theory.GroupTheory.SubgroupConjugation

/-!
# A centralizer quotient detected by a commutator row

Two subgroups of bounded index whose displacements lie in disjoint layers
bound the index of the full centralizer. The proof uses the corresponding
commutator preimages, so neither subgroup must be ambient-normal.

If an actor fixes H modulo a central layer Z, each commutator row from H
is equivariant. Minimality of Z makes a nonzero row surjective. When the
centralizer index is at most |Z|, its kernel is the full centralizer of H,
giving an equivariant isomorphism Q/C_Q(H) with Z.

This is the algebra behind DGS85, Groups and Graphs, printed p.188(5).
The geometric input and its original completion maps are supplied by
CommutingThreeProfile.SuzukiCentralizerNatural.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- Two transverse displacement bounds control the actual centralizer index. -/
theorem centralizer_index_le_of_transverse_displacements
    (Q H U V D E : Subgroup G) [Finite Q]
    (hQU : Q ≤ normalizer (U : Set G)) (hQV : Q ≤ normalizer (V : Set G))
    (hUV : U ⊓ V = ⊥) (hDQ : D ≤ Q) (hEQ : E ≤ Q)
    (hD : ⁅D,H⁆ ≤ U) (hE : ⁅E,H⁆ ≤ V) {d e : ℕ}
    (hd : D.relIndex Q ≤ d) (he : E.relIndex Q ≤ e) :
    (centralizer (H : Set G)).relIndex Q ≤ d * e := by
  let P := commutatorPreimage Q H U
  let R := commutatorPreimage Q H V
  have hPR : P ⊓ R ≤ centralizer (H : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [←hUV]
    exact le_inf ((commutator_mono inf_le_left le_rfl).trans
      (commutator_commutatorPreimage_le Q H U hQU))
      ((commutator_mono inf_le_right le_rfl).trans
        (commutator_commutatorPreimage_le Q H V hQV))
  have hp : P.relIndex Q ≤ d :=
    (relIndex_le_of_le_left (le_commutatorPreimage hDQ hD) index_ne_zero_of_finite).trans hd
  have hr : R.relIndex Q ≤ e :=
    (relIndex_le_of_le_left (le_commutatorPreimage hEQ hE) index_ne_zero_of_finite).trans he
  exact (relIndex_le_of_le_left hPR index_ne_zero_of_finite).trans
    (relIndex_inf_le.trans (Nat.mul_le_mul hp hr))

/-- A nonzero central commutator row of minimal image, at the sharp index bound,
identifies the literal centralizer quotient with that image equivariantly. -/
theorem exists_equivariant_centralizer_quotient
    (A Q H Z : Subgroup G) [Finite Q] [Finite Z]
    (hAQ : A ≤ normalizer (Q : Set G))
    (hHQ : ⁅H,Q⁆ ≤ Z) (hHA : ⁅H,A⁆ ≤ Z)
    (hZQ : Z ≤ Q) (hZC : Z ≤ centralizer (Q : Set G))
    (hmin : ∀ N : Subgroup G, A ≤ normalizer (N : Set G) → N ≤ Z → N = ⊥ ∨ N = Z)
    (hne : ⁅H,Q⁆ ≠ ⊥) (hbound : (centralizer (H : Set G)).relIndex Q ≤ Nat.card Z) :
    ∃ hN : ((centralizer (H : Set G)).subgroupOf Q).Normal,
      let := hN
      ∃ E : (Q ⧸ (centralizer (H : Set G)).subgroupOf Q) ≃* Z,
        ∀ a : A, ∀ q : Q,
          (E (QuotientGroup.mk ⟨(a : G) * q * (a : G)⁻¹,
            (mem_normalizer_iff.mp (hAQ a.property) q).mp q.property⟩) : G) =
              (a : G) * E (QuotientGroup.mk q) * (a : G)⁻¹ := by
  classical
  obtain ⟨r,hr,s,hs,hne⟩ : ∃ r ∈ H, ∃ s ∈ Q, ⁅r,s⁆ ≠ 1 := by
    by_contra hh
    push Not at hh
    apply hne
    apply bot_unique
    exact commutator_le.mpr (fun r hr s hs => mem_bot.mpr (hh r hr s hs))
  let f : Q →* G := {
    toFun q := ⁅r,(q : G)⁆
    map_one' := by simp
    map_mul' q t := by
      change ⁅r,(q : G)*(t : G)⁆ = ⁅r,(q : G)⁆ * ⁅r,(t : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hc := hZC (hHQ (commutator_mem_commutator hr t.property)) q q.property
      calc
        _ = ⁅r,(q : G)⁆ * ((q : G) * ⁅r,(t : G)⁆) * (q : G)⁻¹ := by group
        _ = _ := by rw [hc]; group }
  have hfZ : f.range ≤ Z := by
    rintro _ ⟨q,rfl⟩
    exact hHQ (commutator_mem_commutator hr q.property)
  have heq (a : A) (q : Q) :
      f ⟨(a : G) * q * (a : G)⁻¹,
        (mem_normalizer_iff.mp (hAQ a.property) q).mp q.property⟩ =
        (a : G) * f q * (a : G)⁻¹ := by
    let t : Q := ⟨(a : G) * q * (a : G)⁻¹,
      (mem_normalizer_iff.mp (hAQ a.property) q).mp q.property⟩
    have hz : ⁅(a : G),r⁆ ∈ Z := hHA ((commutator_comm _ _).ge
      (commutator_mem_commutator a.property hr))
    have hzt : Commute ⁅(a : G),r⁆ (t : G) :=
      (hZC hz t t.property).symm
    have hzr : Commute ⁅(a : G),r⁆ ⁅r,(t : G)⁆ :=
      (hZC hz _ (hZQ (hHQ (commutator_mem_commutator hr t.property)))).symm
    have hh := map_commutatorElement (MulAut.conj (a : G)).toMonoidHom r (q : G)
    change (a : G) * ⁅r,(q : G)⁆ * (a : G)⁻¹ =
      ⁅(a : G)*r*(a : G)⁻¹,(t : G)⁆ at hh
    rw [show (a : G)*r*(a : G)⁻¹ = ⁅(a : G),r⁆ * r by group,
      commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_mul_comm.mpr hzt.eq,
      hzr.eq,mul_inv_cancel_right,mul_one] at hh
    exact hh.symm
  have hn : A ≤ normalizer (f.range : Set G) := by
    apply le_normalizer_iff.mpr
    rintro a ha z ⟨q,rfl⟩
    exact ⟨⟨a*q*a⁻¹,(mem_normalizer_iff.mp (hAQ ha) q).mp q.property⟩,heq ⟨a,ha⟩ q⟩
  have hrange : f.range = Z := (hmin f.range hn hfZ).resolve_left (by
    intro hh
    exact hne (mem_bot.mp (hh ▸ (show f (⟨s,hs⟩ : Q) ∈ f.range from ⟨⟨s,hs⟩,rfl⟩))))
  let g : Q →* Z := f.codRestrict Z (fun q => hfZ ⟨q,rfl⟩)
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨q,hq⟩ := (show (z : G) ∈ f.range from hrange.symm ▸ z.property)
    exact ⟨q,Subtype.ext hq⟩
  let C := (centralizer (H : Set G)).subgroupOf Q
  have hC : C ≤ g.ker := by
    intro q hq
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hq r hr)
  have hg : g.ker.index = Nat.card Z := by rw [index_ker,MonoidHom.range_eq_top.mpr hsurj,card_top]
  have hindex : C.index ≤ g.ker.index := hbound.trans_eq hg.symm
  have hker : C = g.ker := by
    apply eq_of_le_of_card_ge hC
    have hc := C.card_mul_index
    have hk := g.ker.card_mul_index
    have hp : 0 < g.ker.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
    nlinarith [Nat.mul_le_mul_left (Nat.card C) hindex]
  let hN : C.Normal := hker ▸ g.normal_ker
  let := hN
  let E := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hsurj)
  refine ⟨hN,E,?_⟩
  intro a q
  exact heq a q
end Subgroup
