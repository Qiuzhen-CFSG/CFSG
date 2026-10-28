module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphSeeds

/-!
# Two-seed generation at a cubic Chapter 11 vertex

Two distinct neighboring centers each contain an element acting nontrivially
on the cubic star. These elements fix different neighbors, so together they
are transitive. The center pair normalizes the two-seed span, since the
commutator of each center with the opposite core lies in its own seed.
Consequently every neighboring seed lies in that span, which is precisely
the corrected Chapter 11 Vβ generated from Zα ∩ Qβ.

This proves the cubic instance of the generation step in (11.3). It uses
escape from the full local kernel, without identifying that kernel with Qβ.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.2)--(11.3), printed pp.168--171.
-/

public noncomputable section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph

private theorem fin_three_moves : ∀ (f k : Equiv.Perm (Fin 3)) (a c : Fin 3),
    a ≠ c → f a = a → k c = c → f ≠ 1 → k ≠ 1 →
    (f * k) a = c ∧ ∀ z : Fin 3, z = a ∨ z = c ∨ z = k a := by decide

private theorem three_moves {X : Type*} (hc : Nat.card X = 3)
    (f k : Equiv.Perm X) (a c : X)
    (hac : a ≠ c) (hfa : f a = a) (hkc : k c = c) (hf : f ≠ 1) (hk : k ≠ 1) :
    (f * k) a = c ∧ ∀ z : X, z = a ∨ z = c ∨ z = k a := by
  let := Nat.finite_of_card_ne_zero (show Nat.card X ≠ 0 by omega)
  let := Fintype.ofFinite X
  let e : X ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hc)
  let f' := e.symm.trans (f.trans e)
  let k' := e.symm.trans (k.trans e)
  have hf' : f' ≠ 1 := by
    intro he
    apply hf
    ext z
    apply e.injective
    simpa [f'] using Equiv.congr_fun he (e z)
  have hk' : k' ≠ 1 := by
    intro he
    apply hk
    ext z
    apply e.injective
    simpa [k'] using Equiv.congr_fun he (e z)
  obtain ⟨hm, hall⟩ := fin_three_moves f' k' (e a) (e c) (e.injective.ne hac)
    (by simpa [f'] using congrArg e hfa) (by simpa [k'] using congrArg e hkc) hf' hk'
  refine ⟨e.injective ?_,fun z => ?_⟩
  · simpa [f',k'] using hm
  · rcases hall (e z) with he | he | he
    · exact Or.inl (e.injective he)
    · exact Or.inr (Or.inl (e.injective he))
    · exact Or.inr (Or.inr (e.injective (by simpa [k'] using he)))

variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem adjacent_center_le (h : LocallyRankOneTriple P B)
    {a b : Vertex (family P)} (hab : (graph (family P)).Adj a b) :
    Z (family P) a ≤ stabilizer (family P) b :=
  ((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
    ((source_Z_Q_U h a).2.trans ((ballKernel_one_le_edge _ hab).trans inf_le_right))

private theorem conjugate_critical_escape (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) (he : ¬ Z (family P) a ≤ U (family P) b) :
    ¬ Z (family P) c ≤ U (family P) b := by
  let := finite_endpoints h
  obtain ⟨g,hg,hz,_,_⟩ := source_neighbor_conjugate h hab hbc
  intro hh
  have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hh
  rw [←hz,map_map,←U_translate] at hm
  have hZa : ((Z (family P) a).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom = Z (family P) a := by
    rw [←Z_translate,←Z_translate,inv_smul_smul]
  rw [←map_map,hZa,show g⁻¹ • b = b from (stabilizer (family P) b).inv_mem hg] at hm
  exact he hm

/-- The actual center-pair is transitive on the cubic star. -/
theorem source_cubic_center_pair_transitive (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3)
    (w : Vertex (family P)) (hbw : (graph (family P)).Adj b w) :
    ∃ g ∈ Z (family P) a ⊔ Z (family P) c, g • a = w := by
  classical
  let := finite_endpoints h
  have hab := source_critical_one_adjacent hc hb
  have hce := conjugate_critical_escape h hab hbc hc.2
  obtain ⟨x,hx,hxU⟩ := SetLike.not_le_iff_exists.mp hc.2
  obtain ⟨y,hy,hyU⟩ := SetLike.not_le_iff_exists.mp hce
  let x' : stabilizer (family P) b := ⟨x,adjacent_center_le h hab hx⟩
  let y' : stabilizer (family P) b := ⟨y,adjacent_center_le h hbc.symm hy⟩
  let f := localAction (family P) b x'
  let k := localAction (family P) b y'
  have hf : f ≠ 1 := by
    intro he
    apply hxU
    change x' ∈ (U (family P) b).subgroupOf (stabilizer (family P) b)
    rw [U_eq_localAction_kernel]
    exact he
  have hk : k ≠ 1 := by
    intro he
    apply hyU
    change y' ∈ (U (family P) b).subgroupOf (stabilizer (family P) b)
    rw [U_eq_localAction_kernel]
    exact he
  obtain ⟨hm,hall⟩ := three_moves hcard f k ⟨a,hab.symm⟩ ⟨c,hbc⟩
    (fun he => hac (congrArg Subtype.val he))
    (Subtype.ext (Z_le_stabilizer _ a hx)) (Subtype.ext (Z_le_stabilizer _ c hy)) hf hk
  rcases hall ⟨w,hbw⟩ with he | he | he
  · exact ⟨1,one_mem _,(one_smul G a).trans (congrArg Subtype.val he).symm⟩
  · exact ⟨x*y,mul_mem (mem_sup_left hx) (mem_sup_right hy),by
      have hm' := congrArg Subtype.val hm
      change x • (y • a) = c at hm'
      exact (mul_smul x y a).trans (hm'.trans (congrArg Subtype.val he).symm)⟩
  · exact ⟨y,mem_sup_right hy,(congrArg Subtype.val he).symm⟩

theorem source_center_pair_normalizes_pairSpan (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) :
    Z (family P) a ⊔ Z (family P) c ≤ normalizer
      (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) : Set G) := by
  have hzq (v : Vertex (family P)) : Z (family P) v ≤ Q (family P) v :=
    (source_Z_Q_U h v).1.trans (map_subtype_le _)
  have hcomm (v : Vertex (family P)) (hvb : (graph (family P)).Adj v b) :
      ⁅Q (family P) b, Z (family P) v⁆ ≤ Z (family P) v ⊓ Q (family P) b :=
    le_inf (le_normalizer_iff_commutator_le_right.mp
      (source_adjacent_core_normalizes_center h hvb))
      (le_normalizer_iff_commutator_le_left.mp
        ((hzq v).trans (source_adjacent_core_normalizes_core h hvb)))
  apply sup_le
  · exact le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono (pairSpan_le_core _ _ _) le_rfl).trans
        ((hcomm a hab).trans le_sup_left))
  · exact le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono (pairSpan_le_core _ _ _) le_rfl).trans
        ((hcomm c hbc.symm).trans le_sup_right))

theorem source_betaSpan_eq_pairSpan_of_center_pair_transitive
    (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (ht : ∀ w, (graph (family P)).Adj b w →
      ∃ g ∈ Z (family P) a ⊔ Z (family P) c, g • a = w) :
    betaSpan (stabilizer (family P) b) (Z (family P) a) =
      pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) := by
  let := finite_endpoints h
  apply le_antisymm ?_ (source_pairSpan_le_betaSpan h hab hbc)
  rw [source_betaSpan_eq_neighbor_span h hab]
  apply iSup_le
  intro w
  obtain ⟨g,hg,hga⟩ := ht w.val w.property
  have hgb : g • b = b :=
    sup_le (adjacent_center_le h hab) (adjacent_center_le h hbc.symm) hg
  have hmap : (Z (family P) a ⊓ Q (family P) b).map (MulAut.conj g).toMonoidHom =
      Z (family P) w.val ⊓ Q (family P) b := by
    rw [map_inf _ _ _ (MulAut.conj g).injective,←Z_translate,←Q_translate,hga,hgb]
  rw [←hmap]
  exact (map_mono (show Z (family P) a ⊓ Q (family P) b ≤
    pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) from le_sup_left)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        (source_center_pair_normalizes_pairSpan h hab hbc hg))

theorem source_cubic_betaSpan_eq_pairSpan (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3) :
    betaSpan (stabilizer (family P) b) (Z (family P) a) =
      pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) :=
  source_betaSpan_eq_pairSpan_of_center_pair_transitive h (source_critical_one_adjacent hc hb) hbc
    (source_cubic_center_pair_transitive h hc hb hbc hac hcard)

/-- The whole corrected cubic span has central derived subgroup equal to its
Frattini subgroup. Its nontriviality still requires the later source argument. -/
theorem source_cubic_betaSpan_commutator_frattini (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (hcard : Nat.card ((graph (family P)).neighborSet b) = 3) :
    let W := betaSpan (stabilizer (family P) b) (Z (family P) a)
    ⁅W,W⁆ = ⁅Z (family P) a ⊓ Q (family P) b, Z (family P) c ⊓ Q (family P) b⁆ ∧
      (frattini W).map W.subtype = ⁅W,W⁆ ∧
      ⁅W,W⁆ ≤ Z (family P) a ⊓ Z (family P) c ∧ ⁅⁅W,W⁆,W⁆ = ⊥ := by
  dsimp only
  rw [source_cubic_betaSpan_eq_pairSpan h hc hb hbc hac hcard]
  exact source_pairSpan_commutator_frattini h (source_critical_one_adjacent hc hb) hbc

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
