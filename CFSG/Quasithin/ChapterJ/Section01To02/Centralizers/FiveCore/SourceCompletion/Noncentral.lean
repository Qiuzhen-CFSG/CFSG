module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.SourceCompletion.Hyperplane
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.SourceCompletion.Seed
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.SourceCompletion.Quaternion
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.Inverter

/-!
# Noncentral action of the source five-inverter

Let i be the actual two-conjugator inverter in U^(hl). If it centralizes
C_Q(B₅), that quaternion group fixes the subgroup V^h⟨i⟩ of order at least
sixteen. The natural action has no transvections, so C_Q(B₅) lies in Q^(hl).
J.2.2 supplies w in U^(hl) ∩ Q outside HC. Commutation with w then gives a
homomorphism C_Q(B₅) → Z^(hl). By J.2.4(3), its kernel lies in Z: any other
kernel element would force w into HC. The image and kernel each have order
at most two, contradicting |C_Q(B₅)| = eight.

The final declaration supplies the full inverter record from the original
LocalSetup and Choices, discharging both the geometric seed and action
premises of the existing odd-core consumer.

Source: Aschbacher–Smith, J.2.7(5), printed p.436 (PDF p.447).
-/

public section
noncomputable section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  {B5 : Sylow 5 d.toTypeRuSetup.H}

private theorem HC_normalized : d.toTypeRuSetup.H ≤ normalizer d.toTypeRuSetup.HC :=
  (le_inf d.toTypeRuSetup.H.le_normalizer
    (d.ru2.natural.normalized.trans (normalizer_le_normalizer_centralizer _))).trans
    inf_normalizer_le_normalizer_inf

namespace FiveInverterSeed
variable (v : FiveInverterSeed B5)

theorem conjugate_center_le_U :
    d.toTypeRuSetup.Z.conjBy ((v.h:G)*(v.l:G)) ≤ d.toTypeRuSetup.U := by
  rw [conjBy_mul]
  have hh := map_mono (f := (MulAut.conj (v.h:G)).toMonoidHom)
    ((ConjugateIntersections.conjugateZ_le_V d v.l v.l.property).trans
      (le_conjugateSpan d.toTypeRuSetup.H d.V))
  exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp
    (d.ru2.natural.normalized v.h.property))

theorem conjugate_quaternion_of_centralizes (q : FiveQuaternionData B5)
    (hn : v.i ∈ centralizer (CQ B5 : Set G)) :
    CQ B5 ≤ d.toTypeRuSetup.Q.conjBy ((v.h:G)*(v.l:G)) := by
  let g : G := (v.h:G)*(v.l:G)
  let W := d.V.conjBy (v.h:G)
  let X := W ⊔ zpowers v.i
  have hWU : W ≤ d.toTypeRuSetup.U := by
    have hh := map_mono (f := (MulAut.conj (v.h:G)).toMonoidHom)
      (le_conjugateSpan d.toTypeRuSetup.H d.V)
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (d.ru2.natural.normalized v.h.property))
  have hWA : W ≤ d.toTypeRuSetup.U.conjBy g := by
    change W ≤ d.toTypeRuSetup.U.conjBy ((v.h:G)*(v.l:G))
    rw [conjBy_mul]
    exact map_mono (ConjugateIntersections.V_le_conjugateU d v.l v.l.property)
  have hXA : X ≤ d.toTypeRuSetup.U.conjBy g :=
    sup_le hWA (zpowers_le.mpr v.mem_conjugate)
  have hWcard : Nat.card W = 8 := by
    dsimp only [W]
    rw [conjBy,card_map_of_injective (MulAut.conj (v.h:G)).injective,d.ru1.card_V]
  have hXcard : 16 ≤ Nat.card X := by
    have hle : W ≤ X := le_sup_left
    have hc := card_le_of_le hle
    have hne : Nat.card W ≠ Nat.card X := by
      intro he
      have heq := eq_of_le_of_card_ge hle he.ge
      have hi : v.i ∈ X := (show zpowers v.i ≤ X from le_sup_right) (mem_zpowers v.i)
      rw [← heq] at hi
      exact v.not_mem_Q (d.toTypeRuSetup.HC_le_Q (d.U_le_HC (hWU hi)))
    obtain ⟨k,hk⟩ := card_dvd_of_le hle
    rw [hWcard] at hk hc hne
    omega
  have hCX : CQ B5 ≤ centralizer (X : Set G) := by
    dsimp only [X]
    apply le_centralizer_iff.mpr
    refine sup_le ?_ (zpowers_le.mpr hn)
    exact le_centralizer_iff.mp ((q.le_HC.trans inf_le_right).trans (centralizer_le hWU))
  intro t ht
  exact mem_conjugate_Q_of_centralizes_large_subgroup g X hXA hXcard
    v.conjugate_center_le_U (q.le_HC ht) (hCX ht)

theorem exists_conjugate_U_Q_outside_HC :
    ∃ w:G, w ∈ d.toTypeRuSetup.U.conjBy ((v.h:G)*(v.l:G)) ∧
      w ∈ d.toTypeRuSetup.Q ∧ w ∉ d.toTypeRuSetup.HC := by
  have hnot : ¬ ConjugateIntersections.conjugateU d v.l ≤ d.toTypeRuSetup.Q := by
    intro hh
    have hmap := map_mono (f := (MulAut.conj (v.h:G)).toMonoidHom) hh
    have hQ : d.toTypeRuSetup.Q.conjBy (v.h:G) = d.toTypeRuSetup.Q :=
      mem_normalizer_iff_map_conj_eq.mp (d.ru2.six.normalized v.h.property)
    have hi := hmap (show v.i ∈ (ConjugateIntersections.conjugateU d v.l).conjBy (v.h:G) by
      have hi := v.mem_conjugate
      change v.i ∈ d.toTypeRuSetup.U.conjBy ((v.h:G)*(v.l:G)) at hi
      rwa [conjBy_mul] at hi)
    exact v.not_mem_Q (hQ ▸ hi)
  have hn := ConjugateIntersections.inf_Q_not_le_HC d d.dualSection d.noRankOne
    v.l v.l.property hnot
  obtain ⟨w,hw,hnw⟩ := Set.not_subset.mp hn
  refine ⟨(MulAut.conj (v.h:G)) w,?_,?_,?_⟩
  · rw [conjBy_mul]
    exact mem_map.mpr ⟨w,hw.1,rfl⟩
  · exact (mem_normalizer_iff.mp (d.ru2.six.normalized v.h.property) w).mp hw.2
  · intro hh
    exact hnw ((mem_normalizer_iff.mp (HC_normalized v.h.property) w).mpr hh)

private def quaternionCommutator (q : FiveQuaternionData B5) (g w : G)
    (hZ : d.toTypeRuSetup.Z.conjBy g ≤ d.toTypeRuSetup.U)
    (hCQ : CQ B5 ≤ d.toTypeRuSetup.Q.conjBy g)
    (hw : w ∈ d.toTypeRuSetup.U.conjBy g) :
    CQ B5 →* d.toTypeRuSetup.Z.conjBy g := by
  have hcomm : ⁅d.toTypeRuSetup.Q.conjBy g,d.toTypeRuSetup.U.conjBy g⁆ ≤
      d.toTypeRuSetup.Z.conjBy g := by
    rw [conjBy,conjBy,← map_commutator]
    exact map_mono d.toTypeRuSetup.commutator_Q_U_le_Z
  have hc (t : CQ B5) : ⁅(t:G),w⁆ ∈ d.toTypeRuSetup.Z.conjBy g :=
    hcomm (commutator_mem_commutator (hCQ t.property) hw)
  exact {
    toFun t := ⟨⁅(t:G),w⁆,hc t⟩
    map_one' := Subtype.ext (commutatorElement_one_left _)
    map_mul' a b := by
      apply Subtype.ext
      change ⁅(a:G)*(b:G),w⁆ = ⁅(a:G),w⁆ * ⁅(b:G),w⁆
      have ha := (q.le_HC a.property).2 _ (hZ (hc b))
      rw [commutatorElement_mul_left_eq_conj_mul,← ha,mul_inv_cancel_right]
      exact (d.U_le_HC (hZ (hc a))).2 _ (hZ (hc b)) }

/-- The geometric inverter necessarily acts nontrivially on the actual quaternion group. -/
theorem noncentral (c : Choices d) (q : FiveQuaternionData B5) :
    v.i ∉ centralizer (CQ B5 : Set G) := by
  intro hn
  let g : G := (v.h:G)*(v.l:G)
  have hCQ := v.conjugate_quaternion_of_centralizes q hn
  obtain ⟨w,hwA,hwQ,hwHC⟩ := v.exists_conjugate_U_Q_outside_HC
  let δ := quaternionCommutator q g w v.conjugate_center_le_U hCQ hwA
  have hk : δ.ker ≤ d.toTypeRuSetup.Z.subgroupOf (CQ B5) := by
    intro t ht
    have he : ⁅(t:G),w⁆ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp ht)
    have htU : (t:G) ∈ d.toTypeRuSetup.U := by
      by_contra hnt
      have hf := ((SourceCompletion.fusion c).1 t (q.le_HC t.property) hnt).2.2
      have hwc : w ∈ centralizer ({(t:G)} : Set G) := by
        rw [mem_centralizer_singleton_iff]
        exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
      have hwm : w ∈ zpowers (t:G) ⊔ d.toTypeRuSetup.U := hf ▸ ⟨hwQ,hwc⟩
      exact hwHC ((sup_le (zpowers_le.mpr (q.le_HC t.property)) d.U_le_HC) hwm)
    have htZ : (t:G) ∈ CQ B5 ⊓ d.toTypeRuSetup.U := ⟨t.property,htU⟩
    rwa [q.inf_U] at htZ
  have hkcard : Nat.card δ.ker ≤ 2 := by
    have hh := card_le_of_le hk
    have hZCQ : d.toTypeRuSetup.Z ≤ CQ B5 := q.inf_U ▸ inf_le_left
    rwa [Nat.card_congr (subgroupOfEquivOfLe hZCQ).toEquiv,d.card_Z] at hh
  have hrange : Nat.card δ.range ≤ 2 := by
    have hh := Nat.card_le_card_of_injective _ δ.range.subtype_injective
    change Nat.card δ.range ≤ Nat.card (d.toTypeRuSetup.Z.conjBy g) at hh
    have hzcard : Nat.card (d.toTypeRuSetup.Z.conjBy g) = 2 := by
      change Nat.card (d.toTypeRuSetup.Z.map (MulAut.conj g).toMonoidHom) = 2
      rw [card_map_of_injective (MulAut.conj g).injective,d.card_Z]
    exact hh.trans_eq hzcard
  have hc := δ.ker.index_mul_card
  rw [index_ker,five_centralizer_card B5] at hc
  have hh := Nat.mul_le_mul hrange hkcard
  omega

end FiveInverterSeed

/-- The original source hypotheses produce all inverter and fusion fields. -/
theorem fiveInverterData_source (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H) :
    Nonempty (FiveInverterData c B5) := by
  obtain ⟨q⟩ := fiveQuaternionData_source c B5
  obtain ⟨v⟩ := fiveInverterSeed_source B5
  exact ⟨v.toData c (SourceCompletion.earlier c) q (v.noncentral c q)⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
