module
public import Theory.GroupTheory.PResidual.CyclicConjugateImage
public import Theory.GroupTheory.PResidual.PrimeConjugateSpan
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.CoprimeQuotientSubgroups.PrimeLift

/-!
# Prime lifts in the residual of an exact conjugate span

A two-subgroup centralizing an action kernel modulo a normal two-group
has a faithful cyclic residual image modulo that two-group. When its
image moves a normal odd prime subgroup, the residual of its conjugates
under the prime preimage maps onto that prime subgroup. Coprime lifting
then constructs an actual prime-order subgroup in that same residual.

The conjugating subgroup is the literal preimage throughout; it is not
replaced by the whole ambient group. The application is the central cubic
lift in Aschbacher--Smith 15.1.24, printed p.1101, using the kernel bound
of 14.1.17(3), printed p.980.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

omit [Finite D] in
/-- The exact relative residual has kernel contained in Q after centralization modulo Q. -/
theorem twoResidual_conjugateSpan_kernel_le
    (f : G →* D) (Q R L : Subgroup G) [Q.Normal]
    (hQ : Q ≤ f.ker) (hR : IsPGroup 2 R)
    (hRL : R ≤ normalizer (L : Set G))
    (hcomm : ⁅f.ker,R⁆ ≤ Q)
    (hcyc : IsCyclic (((pResidual 2 (conjugateSpanBy R L)).map
      (conjugateSpanBy R L).subtype).map f)) :
    ((pResidual 2 (conjugateSpanBy R L)).map
      (conjugateSpanBy R L).subtype) ⊓ f.ker ≤ Q := by
  let E := (pResidual 2 (conjugateSpanBy R L)).map (conjugateSpanBy R L).subtype
  let B := L ⊔ R
  let q := QuotientGroup.mk' Q
  let g := QuotientGroup.lift Q f hQ
  have hspan : conjugateSpanBy R B = conjugateSpanBy R L :=
    conjugateSpanBy_sup_of_normalizes_seed R L R R.le_normalizer hRL
  have he : E.map q = (pResidual 2 (conjugateSpanBy (R.map q) (B.map q))).map
      (conjugateSpanBy (R.map q) (B.map q)).subtype := by
    change ((pResidual 2 (conjugateSpanBy R L)).map _).map q = _
    rw [←hspan,map_embedded_pResidual,map_conjugateSpanBy]
  have hcentral : R.map q ≤ centralizer (g.ker : Set (G ⧸ Q)) := by
    rw [QuotientGroup.ker_lift]
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,map_eq_bot_iff,QuotientGroup.ker_mk']
    exact hcomm
  have hcyc' : IsCyclic ((E.map q).map g) := by
    rw [map_map]
    exact hcyc
  have hdis : Disjoint (E.map q) g.ker := by
    rw [he] at hcyc' ⊢
    let := hcyc'
    exact disjoint_twoResidual_conjugateSpan_ker_of_cyclic_image
      g (R.map q) (B.map q) (map_mono le_sup_right) (hR.map q) hcentral
  intro x hx
  have hz : q x = 1 := disjoint_def.mp hdis (mem_map_of_mem q hx.1) hx.2
  exact (QuotientGroup.eq_one_iff x).mp hz

/-- A moving normal odd prime image has an actual prime lift in the specified relative residual. -/
theorem exists_prime_lift_in_twoResidual_conjugateSpan
    (f : G →* D) (hf : Function.Surjective f)
    (P : Subgroup D) [P.Normal] (hP : Nat.Prime (Nat.card P))
    (hodd : Odd (Nat.card P))
    (Q R : Subgroup G) [Q.Normal] (hQtwo : IsPGroup 2 Q)
    (hQ : Q ≤ f.ker) (hR : IsPGroup 2 R)
    (hcomm : ⁅f.ker,R⁆ ≤ Q)
    (hmove : ¬ R.map f ≤ centralizer (P : Set D)) :
    ∃ X : Subgroup G,
      X ≤ (pResidual 2 (conjugateSpanBy R (P.comap f))).map
        (conjugateSpanBy R (P.comap f)).subtype ∧
      Nat.card X = Nat.card P ∧ X.map f = P := by
  let L := P.comap f
  let E := (pResidual 2 (conjugateSpanBy R L)).map (conjugateSpanBy R L).subtype
  have hL : L.map f = P := map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hf]; exact le_top)
  have hspan : conjugateSpanBy (R.map f) (P ⊔ R.map f) =
      conjugateSpanBy (R.map f) P :=
    conjugateSpanBy_sup_of_normalizes_seed _ _ _ (R.map f).le_normalizer le_normalizer_of_normal
  have hEf : E.map f = P := by
    rw [show E = (pResidual 2 (conjugateSpanBy R L)).map _ from rfl,
      map_embedded_pResidual,map_conjugateSpanBy,hL,←hspan]
    exact prime_conjugateSpan_residual P (R.map f) (R.map f) hP hodd (hR.map f) le_rfl hmove
  let : Fact (Nat.card P).Prime := ⟨hP⟩
  let : IsCyclic P := isCyclic_of_prime_card rfl (p := Nat.card P)
  have hcyc : IsCyclic (E.map f) := hEf ▸ inferInstance
  have hker : E ⊓ f.ker ≤ Q := twoResidual_conjugateSpan_kernel_le
    f Q R L hQ hR le_normalizer_of_normal hcomm hcyc
  let r := f.subgroupMap E
  have hrker : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap]
    exact hQtwo.comap_subtype.of_injective (inclusion (show f.ker.subgroupOf E ≤ Q.subgroupOf E from
      fun x hx => hker ⟨x.property,hx⟩)) (inclusion_injective _)
  obtain ⟨n,hn⟩ := hrker.exists_card_eq
  have hcop : Nat.Coprime (Nat.card P) (Nat.card r.ker) := by
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  let : Fact (Nat.card P).Prime := ⟨hP⟩
  have htop : IsPGroup (Nat.card P) (⊤ : Subgroup (E.map f)) := by
    apply IsPGroup.of_card (n := 1)
    rw [card_top,Nat.card_congr (MulEquiv.subgroupCongr hEf).toEquiv,pow_one]
  obtain ⟨A,hA,⟨eA⟩⟩ := exists_prime_subgroup_equiv_of_surjective_coprime
    r (f.subgroupMap_surjective E) hcop ⊤ htop
  refine ⟨A.map E.subtype,map_subtype_le _,?_,?_⟩
  · rw [card_map_of_injective E.subtype_injective,Nat.card_congr eA.toEquiv,
      card_top,Nat.card_congr (MulEquiv.subgroupCongr hEf).toEquiv]
  · have hh := congrArg (map (E.map f).subtype) hA
    rw [←MonoidHom.range_eq_map,range_subtype] at hh
    exact (show (A.map E.subtype).map f = (A.map r).map (E.map f).subtype by
      rw [map_map,map_map]; rfl).trans (hh.trans hEf)

end Subgroup
