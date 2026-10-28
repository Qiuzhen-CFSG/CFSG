module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiNinePathOdd
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiOppositeSixPathOrder
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiOppositeSixPathOrder
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiThreePathExchange

/-!
# Regularity of the opposite source six-path

For a normalized nine-path `v₀--a--r--t--u--w--m--v--z--c`, put
`D = (Q_r ∩ Q_u) ∩ Q_m` and `E = D ∩ Q_z`.  The two-step core bounds
give `|E| ≥ q²`; oddness of the nine-path stabilizer makes `E` disjoint
from `Q_a`, so the left endpoint image has order `q²` and is transitive.
The opposite six-path `a--r--t--u--w--m--v` is therefore left-regular.

The final theorem applies this dichotomy to the literal source-minimal
nine-path and its original full-Borel complement.  Critical-pair data,
the nonzero branch commutator, natural-center data, both Sylow inclusions,
and the source path remain explicit hypotheses; this theorem does not
silently discharge those source premises.  The source parameter bound
and the remaining (12.6)--(12.9)/(13.1) assembly stay with the consumers.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(12.7)--(12.8), printed pp.184--186.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups Pointwise
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem disjoint_large_sup (A B E : Subgroup (G₀ L S)) [Finite A]
    (hE : E ≤ A) (hN : E ≤ normalizer (A ⊓ B : Set (G₀ L S)))
    (hd : E ⊓ B = ⊥) (hc : B.relIndex A ≤ Nat.card E) : E ⊔ (A ⊓ B) = A := by
  let N := A ⊓ B
  have hdis : Disjoint N E := by
    rw [disjoint_iff]
    apply bot_unique
    calc
      N ⊓ E ≤ E ⊓ B := le_inf inf_le_right (inf_le_left.trans inf_le_right)
      _ = ⊥ := hd
  have hcard := card_sup_eq_mul_of_normalizes_of_disjoint N E hN hdis
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) N A bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left] at hm
  change Nat.card N * (A ⊓ B).relIndex A = Nat.card A at hm
  rw [inf_relIndex_left] at hm
  apply eq_of_le_of_card_ge (sup_le hE inf_le_left)
  rw [sup_comm,hcard,←hm]
  exact Nat.mul_le_mul_left _ hc

private theorem restricted_core_lower
    {F : Bool → Subgroup (G₀ L S)} [∀ v : Vertex F, Finite (Q F v)]
    {i : Bool} {q : ℕ} (hq : 0 < q)
    (hs : (Q F (base F (!i))).relIndex (Q F (base F i)) = q^2)
    (hl : (Q F (base F i)).relIndex (Q F (base F (!i))) = q)
    (hcore : q^10 ≤ Nat.card (Q F (base F i)))
    {r t u w m v z : Vertex F} (hrt : r.type = i)
    (hrt' : (graph F).Adj r t) (htu : (graph F).Adj t u)
    (huw : (graph F).Adj u w) (hwm : (graph F).Adj w m)
    (hmv : (graph F).Adj m v) (hvz : (graph F).Adj v z)
    (hsmall : (Q F v).relIndex ((Q F r ⊓ Q F u) ⊓ Q F m) ≤ q) :
    q^2 ≤ Nat.card (((Q F r ⊓ Q F u) ⊓ Q F m) ⊓ Q F z : Subgroup (G₀ L S)) := by
  let D := (Q F r ⊓ Q F u) ⊓ Q F m
  have hDu : D ≤ Q F u := inf_le_left.trans inf_le_right
  let : Finite D := Finite.of_injective (inclusion hDu) (inclusion_injective _)
  have htt : t.type = !i := Bool.eq_not_iff.mpr (hrt ▸ hrt'.1.symm)
  have hut : u.type = i := (Bool.eq_not_iff.mpr (htt ▸ htu.1.symm)).trans (by simp)
  have hwt : w.type = !i := Bool.eq_not_iff.mpr (hut ▸ huw.1.symm)
  have hmt : m.type = i := (Bool.eq_not_iff.mpr (hwt ▸ hwm.1.symm)).trans (by simp)
  have hvt : v.type = !i := Bool.eq_not_iff.mpr (hmt ▸ hmv.1.symm)
  have hzt : z.type = i := (Bool.eq_not_iff.mpr (hvt ▸ hvz.1.symm)).trans (by simp)
  have hr : (Q F r).relIndex (Q F u) ≤ q^3 :=
    two_step_core_index (Q F u) (Q F t) (Q F r)
      (core_index_at (i := !i) (by simpa only [Bool.not_not] using hs) htt htu)
      (core_index_at hl hrt hrt')
  have hm : (Q F m).relIndex (Q F u) ≤ q^3 :=
    two_step_core_index (Q F u) (Q F w) (Q F m)
      (core_index_at (i := !i) (by simpa only [Bool.not_not] using hs) hwt huw.symm)
      (core_index_at hl hmt hwm.symm)
  have hidx : D.relIndex (Q F u) ≤ q^6 := by
    have he : D = Q F u ⊓ (Q F r ⊓ Q F m) := by dsimp only [D]; ac_rfl
    rw [he,inf_relIndex_left]
    exact (relIndex_inf_le.trans (Nat.mul_le_mul hr hm)).trans_eq (by ring)
  have hu : q^10 ≤ Nat.card (Q F u) := (core_card_at hut).symm ▸ hcore
  have hmult := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) D (Q F u) bot_le hDu
  rw [relIndex_bot_left,relIndex_bot_left] at hmult
  have hD : q^4 ≤ Nat.card D := by
    apply Nat.le_of_mul_le_mul_right (c := q^6) _ (by positivity)
    calc
      q^4*q^6 = q^10 := by ring
      _ ≤ Nat.card (Q F u) := hu
      _ = Nat.card D * D.relIndex (Q F u) := hmult.symm
      _ ≤ Nat.card D * q^6 := Nat.mul_le_mul_left _ hidx
  let K := D ⊓ Q F v
  let : Finite K := Finite.of_injective (inclusion (show K ≤ D from inf_le_left)) (inclusion_injective _)
  have he := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) K D bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at he
  have hK : q^3 ≤ Nat.card K := by
    apply Nat.le_of_mul_le_mul_right (c := q) _ hq
    calc
      q^3*q = q^4 := by ring
      _ ≤ Nat.card D := hD
      _ = Nat.card K * (Q F v).relIndex D := he.symm
      _ ≤ Nat.card K*q := Nat.mul_le_mul_left _ hsmall
  have hki : (Q F z).relIndex K ≤ q :=
    (relIndex_le_of_le_right inf_le_right
      (show ((Q F z).subgroupOf (Q F v)).index ≠ 0 from index_ne_zero_of_finite)).trans_eq
      (core_index_at hl hzt hvz.symm)
  have hkm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (K ⊓ Q F z) K bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at hkm
  have hkz : q^2 ≤ Nat.card (K ⊓ Q F z : Subgroup (G₀ L S)) := by
    apply Nat.le_of_mul_le_mul_right (c := q) _ hq
    calc
      q^2*q = q^3 := by ring
      _ ≤ Nat.card K := hK
      _ = Nat.card (K ⊓ Q F z : Subgroup (G₀ L S)) * (Q F z).relIndex K := hkm.symm
      _ ≤ Nat.card (K ⊓ Q F z : Subgroup (G₀ L S))*q := Nat.mul_le_mul_left _ hki
  let : Finite (D ⊓ Q F z : Subgroup (G₀ L S)) := Finite.of_injective
    (inclusion (show D ⊓ Q F z ≤ D from inf_le_left)) (inclusion_injective _)
  exact hkz.trans (Nat.card_le_card_of_injective
    (inclusion (inf_le_inf_right (Q F z) (show K ≤ D from inf_le_left))) (inclusion_injective _))

set_option backward.isDefEq.respectTransparency false in
private theorem opposite_six_path_regular_of_odd
    (h : HypothesisF11 L S) (i : Bool)
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hs : (Q (reducedFamily L S) (base (reducedFamily L S) (!i))).relIndex
      (Q (reducedFamily L S) (base (reducedFamily L S) i)) = (2^(2*n+1))^2)
    (hl : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = 2^(2*n+1))
    (hcore : (2^(2*n+1))^10 ≤ Nat.card (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hodd9 : Odd (Nat.card (pathStabilizer (reducedFamily L S) p)))
    (hsmallD :
      let F := reducedFamily L S
      (Q F (p.2.2.2.2.2.2.1 : Vertex F)).relIndex
        ((Q F (p.2.1 : Vertex F) ⊓ Q F (p.2.2.2.1 : Vertex F)) ⊓
          Q F (p.2.2.2.2.2.1 : Vertex F)) ≤ 2^(2*n+1)) :
    let F := reducedFamily L S
    let a : Vertex F := p.1
    let r : Vertex F := p.2.1
    let t : Vertex F := p.2.2.1
    let u : Vertex F := p.2.2.2.1
    let w : Vertex F := p.2.2.2.2.1
    let m : Vertex F := p.2.2.2.2.2.1
    let v : Vertex F := p.2.2.2.2.2.2.1
    let z : Vertex F := p.2.2.2.2.2.2.2.1
    let D := (Q F r ⊓ Q F u) ⊓ Q F m
    let E := D ⊓ Q F z
    E ⊓ Q F a = ⊥ ∧ Nat.card E = (2^(2*n+1))^2 ∧
      (E.map (G₀ L S).subtype) ⊓ (Q F a).map (G₀ L S).subtype = ⊥ ∧
      Nat.card (E.map (G₀ L S).subtype) = (2^(2*n+1))^2 ∧
      ∃ γ : BasedWalk (graph F) 6 a,
        γ.vertices = [a,r,t,u,w,m,v] ∧ γ.Nonbacktracking ∧
        D ≤ pathStabilizer F γ ∧
        D.map (G₀ L S).subtype ≤ (pathStabilizer F γ).map (G₀ L S).subtype ∧
        Theory.GroupAction.CubicTree.LeftRegular (A := G₀ L S) γ := by
  let F := reducedFamily L S
  let q := 2^(2*n+1)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : ∀ z : Vertex F, Finite (Q F z) := fun z =>
    Finite.of_injective (inclusion (Q_le_stabilizer F z)) (inclusion_injective _)
  let a : Vertex F := p.1
  let r : Vertex F := p.2.1
  let t : Vertex F := p.2.2.1
  let u : Vertex F := p.2.2.2.1
  let w : Vertex F := p.2.2.2.2.1
  let m : Vertex F := p.2.2.2.2.2.1
  let v : Vertex F := p.2.2.2.2.2.2.1
  let z : Vertex F := p.2.2.2.2.2.2.2.1
  let c : Vertex F := p.2.2.2.2.2.2.2.2.1
  have ha : (graph F).Adj v₀ a := p.1.property
  have har : (graph F).Adj a r := p.2.1.property
  have hrt : (graph F).Adj r t := p.2.2.1.property
  have htu : (graph F).Adj t u := p.2.2.2.1.property
  have huw : (graph F).Adj u w := p.2.2.2.2.1.property
  have hwm : (graph F).Adj w m := p.2.2.2.2.2.1.property
  have hmv : (graph F).Adj m v := p.2.2.2.2.2.2.1.property
  have hvz : (graph F).Adj v z := p.2.2.2.2.2.2.2.1.property
  have hzc : (graph F).Adj z c := p.2.2.2.2.2.2.2.2.1.property
  change r = base F i at hm
  change t = base F (!i) at hy
  let D := (Q F r ⊓ Q F u) ⊓ Q F m
  let E := D ⊓ Q F z
  change (Q F v).relIndex D ≤ q at hsmallD
  have hrtp : r.type = i := hm ▸ rfl
  have hat : a.type = !i := Bool.eq_not_iff.mpr (hrtp ▸ har.1)
  have hElow : q^2 ≤ Nat.card E :=
    restricted_core_lower (by positivity : 0 < q) hs hl hcore hrtp hrt htu huw hwm hmv hvz hsmallD
  have hDr : D ≤ Q F r := inf_le_left.trans inf_le_left
  have hDu : D ≤ Q F u := inf_le_left.trans inf_le_right
  have hDm : D ≤ Q F m := inf_le_right
  have hEr : E ≤ Q F r := inf_le_left.trans hDr
  have hEu : E ≤ Q F u := inf_le_left.trans hDu
  have hEm : E ≤ Q F m := inf_le_left.trans hDm
  have hEz : E ≤ Q F z := inf_le_right
  have hfix {H : Subgroup (G₀ L S)} {b d : Vertex F}
      (hH : H ≤ Q F b) (hbd : (graph F).Adj b d) : H ≤ stabilizer F d :=
    (hH.trans (source_Z_Q_U (reduced_triple h) b).2).trans
      ((ballKernel_one_le_edge F hbd).trans inf_le_right)
  let γ : BasedWalk (graph F) 6 a :=
    ⟨⟨r,har⟩,⟨⟨t,hrt⟩,⟨⟨u,htu⟩,⟨⟨w,huw⟩,⟨⟨m,hwm⟩,⟨⟨v,hmv⟩,PUnit.unit⟩⟩⟩⟩⟩⟩
  have hDγ : D ≤ pathStabilizer F γ := by
    intro d hd b hb'
    change b ∈ [a,r,t,u,w,m,v] at hb'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb'
    rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfix hDr har.symm hd
    · exact Q_le_stabilizer F r (hDr hd)
    · exact hfix hDr hrt hd
    · exact Q_le_stabilizer F u (hDu hd)
    · exact hfix hDu huw hd
    · exact Q_le_stabilizer F m (hDm hd)
    · exact hfix hDm hmv hd
  have hdis : E ⊓ Q F a = ⊥ := by
    apply eq_bot_iff.mpr
    intro d hd
    have hdfix : d ∈ pathStabilizer F p := by
      intro b hb'
      change b ∈ [v₀,a,r,t,u,w,m,v,z,c] at hb'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hb'
      rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hfix (le_rfl : Q F a ≤ Q F a) ha.symm hd.2
      · exact Q_le_stabilizer F a hd.2
      · exact Q_le_stabilizer F r (hEr hd.1)
      · exact hfix hEr hrt hd.1
      · exact Q_le_stabilizer F u (hEu hd.1)
      · exact hfix hEu huw hd.1
      · exact Q_le_stabilizer F m (hEm hd.1)
      · exact hfix hEm hmv hd.1
      · exact Q_le_stabilizer F z (hEz hd.1)
      · exact hfix hEz hzc hd.1
    have hpE : IsPGroup 2 E := (isPGroup_pCoreIn 2 (stabilizer F r)).to_le hEr
    obtain ⟨j,hj⟩ := hpE (⟨d,hd.1⟩ : E)
    have hdp : orderOf d ∣ 2^j := by
      simpa only [Subgroup.orderOf_mk] using orderOf_dvd_of_pow_eq_one hj
    have hdo : orderOf d ∣ Nat.card (pathStabilizer F p) := by
      simpa only [Subgroup.orderOf_mk] using orderOf_dvd_natCard (⟨d,hdfix⟩ : pathStabilizer F _)
    exact mem_bot.mpr (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hodd9.coprime_two_right.pow_right j) hdo hdp))
  have hindex : (Q F a).relIndex E = Nat.card E := by
    rw [←inf_relIndex_left,hdis,relIndex_bot_left]
  have hia : (Q F a).relIndex (Q F r) = q^2 :=
    core_index_at (i := !i) (by simpa only [Bool.not_not] using hs) hat har
  have hEcard : Nat.card E = q^2 := le_antisymm (by
    rw [←hindex]
    exact (relIndex_le_of_le_right hEr
      (show ((Q F a).subgroupOf (Q F r)).index ≠ 0 from index_ne_zero_of_finite)).trans_eq hia) hElow
  have hnQ (b : Vertex F) : stabilizer F b ≤ normalizer (Q F b : Set (G₀ L S)) :=
    (stabilizer F b).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F b)))
  have hnorm : E ≤ normalizer (Q F r ⊓ Q F a : Set (G₀ L S)) :=
    (le_inf (hEr.trans (Q F r).le_normalizer) ((hfix hEr har.symm).trans (hnQ a))).trans
      inf_normalizer_le_normalizer_inf
  have hsup : E ⊔ (Q F r ⊓ Q F a) = Q F r :=
    disjoint_large_sup (Q F r) (Q F a) E hEr hnorm hdis (hia ▸ hElow)
  refine ⟨hdis,hEcard,?_,?_,γ,rfl,?_,hDγ,map_mono hDγ,?_⟩
  · rw [←Subgroup.map_inf _ _ _ (G₀ L S).subtype_injective,hdis,Subgroup.map_bot]
  · rw [card_map_of_injective (G₀ L S).subtype_injective]
    exact hEcard
  · exact ⟨hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2.1, trivial⟩
  · intro b d hb' hd'
    change (graph F).Adj a b ∧ b ≠ r at hb'
    change (graph F).Adj a d ∧ d ≠ r at hd'
    obtain ⟨g,hg,hgd⟩ := suzuki_neighbor_core_transitive_at h (!i) hn eSuz Ry
      (by simpa only [Bool.not_not] using hRy) hat har hb'.1 hd'.1 hb'.2 hd'.2
    have hg' : g ∈ (E : Set (G₀ L S)) * ((Q F r ⊓ Q F a : Subgroup (G₀ L S)) : Set (G₀ L S)) := by
      rw [←coe_mul_of_left_le_normalizer_right E (Q F r ⊓ Q F a) hnorm,hsup]
      exact hg
    obtain ⟨e',he',f,hf,rfl⟩ := hg'
    have hfb : f • b = b := hfix (le_rfl : Q F a ≤ Q F a) hb'.1 hf.2
    refine ⟨e',hDγ (show (e' : G₀ L S) ∈ D from he'.1),?_⟩
    rwa [mul_smul,hfb] at hgd

private theorem suzuki_base_core_index
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    {x : Vertex (reducedFamily L S)} (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (Q (reducedFamily L S) x) = (2^(2*n+1))^2 := by
  obtain ⟨P,_,hi,_⟩ := source_common_sylow_core_index h i e R hR
  rw [inf_relIndex_left] at hi
  exact hi.trans (suzukiSylow_card hn (MulEquiv.refl _) P)

private theorem linear_base_core_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    {x : Vertex (reducedFamily L S)} (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (Q (reducedFamily L S) x) = Nat.card k := by
  obtain ⟨P,_,hi,_⟩ := source_common_sylow_core_index h i e R hR
  rw [inf_relIndex_left] at hi
  exact hi.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 P).symm.toEquiv)

theorem source_suzuki_opposite_six_path_small_left_regular
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    {σ : Vertex (reducedFamily L S)}
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) 1, Q (reducedFamily L S) (p.1 : Vertex (reducedFamily L S))⁆ ≤ Z (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)))
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) v₀ (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hc6 : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) (!i)))
    (hc2 : IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hc8 : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hbranchw : ⁅V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1 ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1, star L S (!i)⁆)
    (hsmallD :
      let F := reducedFamily L S
      (Q F (p.2.2.2.2.2.2.1 : Vertex F)).relIndex
        ((Q F (p.2.1 : Vertex F) ⊓ Q F (p.2.2.2.1 : Vertex F)) ⊓
          Q F (p.2.2.2.2.2.1 : Vertex F)) ≤ 2^(2*n+1)) :
    let F := reducedFamily L S
    let a : Vertex F := p.1
    let r : Vertex F := p.2.1
    let t : Vertex F := p.2.2.1
    let u : Vertex F := p.2.2.2.1
    let w : Vertex F := p.2.2.2.2.1
    let m : Vertex F := p.2.2.2.2.2.1
    let v : Vertex F := p.2.2.2.2.2.2.1
    let z : Vertex F := p.2.2.2.2.2.2.2.1
    let D := (Q F r ⊓ Q F u) ⊓ Q F m
    let E := D ⊓ Q F z
    E ⊓ Q F a = ⊥ ∧ Nat.card E = (2^(2*n+1))^2 ∧
      (E.map (G₀ L S).subtype) ⊓ (Q F a).map (G₀ L S).subtype = ⊥ ∧
      Nat.card (E.map (G₀ L S).subtype) = (2^(2*n+1))^2 ∧
      ∃ γ : BasedWalk (graph F) 6 a,
        γ.vertices = [a,r,t,u,w,m,v] ∧ γ.Nonbacktracking ∧
        D ≤ pathStabilizer F γ ∧
        D.map (G₀ L S).subtype ≤ (pathStabilizer F γ).map (G₀ L S).subtype ∧
        Theory.GroupAction.CubicTree.LeftRegular (A := G₀ L S) γ := by
  let F := reducedFamily L S
  let q := 2^(2*n+1)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : ∀ z : Vertex F, Finite (Q F z) := fun z =>
    Finite.of_injective (inclusion (Q_le_stabilizer F z)) (inclusion_injective _)
  have hodd9 := (source_suzuki_nine_path_odd h i hb p hp hm hy T R hT hR e hz hcard hcardy
    hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hmin hnat
    hc6 hc2 hc8 hbranchw).1
  have hcore : q^10 ≤ Nat.card (Q F (base F i)) := by
    have hxm : (graph F).Adj (p.1 : Vertex F) (base F i) := by
      rw [←hm]
      exact p.2.1.property
    cases i <;>
      exact (source_suzuki_core_order_lower (k := k) h _ hb hc p.1.property.symm
        hxm hn hfield eSuz e R hR Ry hRy hzy hcommy T hT hnat hfull
        (hcardy.trans hfield)).2.1

  have hs := suzuki_base_core_index h (!i) hn eSuz Ry hRy
  have hl := (linear_base_core_index h i e T hT).trans hfield
  exact opposite_six_path_regular_of_odd h i p hp hm hy hn eSuz Ry hRy hs hl hcore hodd9 hsmallD


private theorem suzuki_complement_invariant_small_or_transitive_at
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    {a x : Vertex (reducedFamily L S)} (ha : a.type = i)
    (hax : (graph (reducedFamily L S)).Adj a x)
    (D C : Subgroup (G₀ L S)) (hD : D ≤ Q (reducedFamily L S) x)
    (hC : C ≤ stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)
    (hK : (pCore 2 (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a :
      Subgroup (G₀ L S))).IsComplement'
        (C.subgroupOf (stabilizer (reducedFamily L S) x ⊓ stabilizer (reducedFamily L S) a)))
    (hodd : Odd (Nat.card C)) (hnorm : C ≤ normalizer (D : Set (G₀ L S))) :
    (Q (reducedFamily L S) a).relIndex D ≤ 2^(2*n+1) ∨
      ((Q (reducedFamily L S) a).relIndex D = (2^(2*n+1))^2 ∧
      ∀ u v, (graph (reducedFamily L S)).Adj a u → (graph (reducedFamily L S)).Adj a v →
        u ≠ x → v ≠ x → ∃ d ∈ D, d • u = v) := by
  let F := reducedFamily L S
  obtain ⟨g,hga,hgx⟩ := incident_common_translate F hax.2
  have hx : x.type = !i := Bool.eq_not_iff.mpr (ha ▸ hax.1.symm)
  rw [ha] at hga
  rw [hx] at hgx
  have hga' : g⁻¹ • a = base F i := by rw [←hga,inv_smul_smul]
  have hgx' : g⁻¹ • x = base F (!i) := by rw [←hgx,inv_smul_smul]
  let c := (MulAut.conj g⁻¹).toMonoidHom
  let D' := D.map c
  let C' := C.map c
  have hD' : D' ≤ Q F (base F (!i)) := by
    have hh := map_mono (f := c) hD
    change D' ≤ (Q F x).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rwa [←Q_translate F,hgx'] at hh
  have hC' : C' ≤ stabilizer F (base F (!i)) ⊓ stabilizer F (base F i) := by
    rintro t ⟨d,hd,rfl⟩
    have hdx : d • x = x := (hC hd).1
    have hda : d • a = a := (hC hd).2
    constructor
    · change (g⁻¹*d*(g⁻¹)⁻¹) • base F (!i) = base F (!i)
      rw [inv_inv,mul_smul,mul_smul,hgx,hdx,hgx']
    · change (g⁻¹*d*(g⁻¹)⁻¹) • base F i = base F i
      rw [inv_inv,mul_smul,mul_smul,hga,hda,hga']
  have hadj : (graph F).Adj (base F (!i)) (base F i) :=
    ⟨by change (!i) ≠ i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F (!i) i⟩
  have hc : Nat.card C' = Nat.card C := card_map_of_injective (MulAut.conj g⁻¹).injective
  have hK' := source_edge_complement_transfer h hax.symm hadj
    (C.subgroupOf (stabilizer F x ⊓ stabilizer F a)) hK C' hC'
    (hc.symm ▸ hodd) (hc.trans (Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv).symm)
  have hnorm' : C' ≤ normalizer (D' : Set (G₀ L S)) :=
    (map_mono hnorm).trans (D.le_normalizer_map c)
  have hidx : (Q F (base F i)).relIndex D' = (Q F a).relIndex D := by
    have hh := relIndex_map_map_of_injective (Q F a) D (f := c) (MulAut.conj g⁻¹).injective
    change ((Q F a).map (MulAut.conj g⁻¹).toMonoidHom).relIndex D' = _ at hh
    rwa [←Q_translate F,hga'] at hh
  rcases suzuki_complement_invariant_small_or_transitive h i hn e T hT
    D' C' hD' hC' hK' (hc.symm ▸ hodd) hnorm' with hs | ⟨hi,ht⟩
  · exact Or.inl (hidx ▸ hs)
  right
  refine ⟨hidx.symm.trans hi,?_⟩
  intro u v hu hv hux hvx
  have hadj' {z : Vertex F} (hz : (graph F).Adj a z) :
      (graph F).Adj (base F i) (g⁻¹ • z) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g⁻¹).map_adj_iff.mpr hz
    change (graph F).Adj (g⁻¹ • a) (g⁻¹ • z) at hh
    rwa [hga'] at hh
  have hne {z : Vertex F} (hz : z ≠ x) : g⁻¹ • z ≠ base F (!i) := by
    rw [←hgx']
    exact fun he => hz ((MulAction.injective g⁻¹) he)
  obtain ⟨t,ht,he⟩ := ht _ _ (hadj' hu) (hadj' hv) (hne hux) (hne hvx)
  obtain ⟨d,hd,rfl⟩ := ht
  refine ⟨d,hd,?_⟩
  apply MulAction.injective g⁻¹
  change (g⁻¹*d*(g⁻¹)⁻¹) • (g⁻¹ • u) = g⁻¹ • v at he
  simpa only [inv_inv,mul_smul,smul_inv_smul] using he

private theorem opposite_six_path_complement_dichotomy
    (h : HypothesisF11 L S) (i : Bool)
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (C : Subgroup (G₀ L S))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) : Subgroup (G₀ L S))).IsComplement'
        (C.subgroupOf (stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ⊓
          stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)))))
    (hoddC : Odd (Nat.card C))
    (hfixC :
      let F := reducedFamily L S
      ∀ z ∈ [(p.1 : Vertex F),p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2.1],
        C ≤ stabilizer F z) :
    let F := reducedFamily L S
    let a : Vertex F := p.1
    let r : Vertex F := p.2.1
    let t : Vertex F := p.2.2.1
    let u : Vertex F := p.2.2.2.1
    let w : Vertex F := p.2.2.2.2.1
    let m : Vertex F := p.2.2.2.2.2.1
    let v : Vertex F := p.2.2.2.2.2.2.1
    let D := (Q F r ⊓ Q F u) ⊓ Q F m
    ∃ γ : BasedWalk (graph F) 6 a,
      γ.vertices = [a,r,t,u,w,m,v] ∧ γ.Nonbacktracking ∧
      D ≤ pathStabilizer F γ ∧
      D.map (G₀ L S).subtype ≤ (pathStabilizer F γ).map (G₀ L S).subtype ∧
      ((Q F v).relIndex D ≤ 2^(2*n+1) ∨
        Theory.GroupAction.CubicTree.RightRegular (A := G₀ L S) γ) := by
  let F := reducedFamily L S
  let a : Vertex F := p.1
  let r : Vertex F := p.2.1
  let t : Vertex F := p.2.2.1
  let u : Vertex F := p.2.2.2.1
  let w : Vertex F := p.2.2.2.2.1
  let m : Vertex F := p.2.2.2.2.2.1
  let v : Vertex F := p.2.2.2.2.2.2.1
  have har : (graph F).Adj a r := p.2.1.property
  have hrt : (graph F).Adj r t := p.2.2.1.property
  have htu : (graph F).Adj t u := p.2.2.2.1.property
  have huw : (graph F).Adj u w := p.2.2.2.2.1.property
  have hwm : (graph F).Adj w m := p.2.2.2.2.2.1.property
  have hmv : (graph F).Adj m v := p.2.2.2.2.2.2.1.property
  let D := (Q F r ⊓ Q F u) ⊓ Q F m
  let γ : BasedWalk (graph F) 6 a :=
    ⟨⟨r,har⟩,⟨⟨t,hrt⟩,⟨⟨u,htu⟩,⟨⟨w,huw⟩,⟨⟨m,hwm⟩,⟨⟨v,hmv⟩,PUnit.unit⟩⟩⟩⟩⟩⟩
  have hDr : D ≤ Q F r := inf_le_left.trans inf_le_left
  have hDu : D ≤ Q F u := inf_le_left.trans inf_le_right
  have hDm : D ≤ Q F m := inf_le_right
  have hDs {b z : Vertex F} (hb : D ≤ Q F b) (hbz : (graph F).Adj b z) : D ≤ stabilizer F z :=
    (hb.trans (source_Z_Q_U (reduced_triple h) b).2).trans
      ((ballKernel_one_le_edge F hbz).trans inf_le_right)
  have hDγ : D ≤ pathStabilizer F γ := by
    intro d hd z hz
    change z ∈ [a,r,t,u,w,m,v] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hDs hDr har.symm hd
    · exact Q_le_stabilizer F r (hDr hd)
    · exact hDs hDr hrt hd
    · exact Q_le_stabilizer F u (hDu hd)
    · exact hDs hDu huw hd
    · exact Q_le_stabilizer F m (hDm hd)
    · exact hDs hDm hmv hd
  change ∀ z ∈ [a,r,t,u,w,m,v], C ≤ stabilizer F z at hfixC
  have hCrt : C ≤ stabilizer F r ⊓ stabilizer F t :=
    le_inf (hfixC r (by simp)) (hfixC t (by simp))
  have hKrt : (pCore 2 (stabilizer F r ⊓ stabilizer F t : Subgroup (G₀ L S))).IsComplement'
      (C.subgroupOf (stabilizer F r ⊓ stabilizer F t)) := by
    change r = base F i at hm
    change t = base F (!i) at hy
    rw [hm,hy]
    exact hK
  have hCmv : C ≤ stabilizer F m ⊓ stabilizer F v :=
    le_inf (hfixC m (by simp)) (hfixC v (by simp))
  have hKmv := source_edge_complement_transfer h hrt hmv
    (C.subgroupOf (stabilizer F r ⊓ stabilizer F t)) hKrt C hCmv hoddC
    (Nat.card_congr (subgroupOfEquivOfLe hCrt).toEquiv).symm
  have hnQ (b : Vertex F) : stabilizer F b ≤ normalizer (Q F b : Set (G₀ L S)) :=
    (stabilizer F b).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F b)))
  have hnorm : C ≤ normalizer (D : Set (G₀ L S)) :=
    (le_inf ((le_inf ((hfixC r (by simp)).trans (hnQ r))
      ((hfixC u (by simp)).trans (hnQ u))).trans inf_normalizer_le_normalizer_inf)
      ((hfixC m (by simp)).trans (hnQ m))).trans inf_normalizer_le_normalizer_inf
  have htt : t.type = !i := congrArg Subgroup.CosetGeometry.Vertex.type hy
  have hut : u.type = i := (Bool.eq_not_iff.mpr (htt ▸ htu.1.symm)).trans (by simp)
  have hwt : w.type = !i := Bool.eq_not_iff.mpr (hut ▸ huw.1.symm)
  have hmt : m.type = i := (Bool.eq_not_iff.mpr (hwt ▸ hwm.1.symm)).trans (by simp)
  have hvt : v.type = !i := Bool.eq_not_iff.mpr (hmt ▸ hmv.1.symm)
  refine ⟨γ,rfl,?_,hDγ,map_mono hDγ,?_⟩
  · exact ⟨hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2.1,trivial⟩
  · rcases suzuki_complement_invariant_small_or_transitive_at h (!i) hn eSuz Ry
      (by simpa only [Bool.not_not] using hRy) hvt hmv.symm D C hDm hCmv hKmv hoddC hnorm with hs | ⟨_,ht⟩
    · exact Or.inl hs
    right
    intro b d hb hd
    change (graph F).Adj v b ∧ b ≠ m at hb
    change (graph F).Adj v d ∧ d ≠ m at hd
    obtain ⟨g,hg,he⟩ := ht b d hb.1 hd.1 hb.2 hd.2
    exact ⟨g,hDγ hg,he⟩

private theorem middle_six_vertices
    {F : Bool → Subgroup (G₀ L S)} {v₀ : Vertex F}
    (p : BasedWalk (graph F) 9 v₀) {z : Vertex F}
    (hz : z ∈ [(p.1 : Vertex F),p.2.1,p.2.2.1,p.2.2.2.1,
      p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2.1]) : z ∈ p.vertices := by
  have hz' : z ∈
      ([(p.1 : Vertex F),p.2.1,p.2.2.1,p.2.2.2.1,
        p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2.1] ++
        [(p.2.2.2.2.2.2.2.1 : Vertex F),(p.2.2.2.2.2.2.2.2.1 : Vertex F)]) :=
    List.mem_append_left _ hz
  simpa [BasedWalk.vertices] using List.mem_cons_of_mem v₀ hz'

set_option backward.isDefEq.respectTransparency false in
theorem source_suzuki_opposite_six_path_endpoint_regular
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {v₀ : Vertex (reducedFamily L S)}
    (p : BasedWalk (graph (reducedFamily L S)) 9 v₀) (hp : p.Nonbacktracking)
    (hm : (p.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) i)
    (hy : (p.2.2.1 : Vertex (reducedFamily L S)) = base (reducedFamily L S) (!i))
    {σ : Vertex (reducedFamily L S)}
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)) 1, Q (reducedFamily L S) (p.1 : Vertex (reducedFamily L S))⁆ ≤ Z (reducedFamily L S) (p.1 : Vertex (reducedFamily L S)))
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) v₀ (base (reducedFamily L S) (!i)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hc6 : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (base (reducedFamily L S) (!i)))
    (hc2 : IsCriticalPair (reducedFamily L S)
      (p.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hc8 : IsCriticalPair (reducedFamily L S)
      (p.2.2.2.2.2.2.2.1 : Vertex (reducedFamily L S)) (p.2.2.2.2.1 : Vertex (reducedFamily L S)))
    (hbranchw : ⁅V (reducedFamily L S) (p.2.2.2.2.1 : Vertex (reducedFamily L S)) 1 ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1, star L S (!i)⁆)
    (C : Subgroup (G₀ L S))
    (hK : (pCore 2 (stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ⊓
      stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) : Subgroup (G₀ L S))).IsComplement'
        (C.subgroupOf (stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ⊓
          stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)))))
    (hoddC : Odd (Nat.card C))
    (hfixC : C ≤ pathStabilizer (reducedFamily L S) p) :
    let F := reducedFamily L S
    let a : Vertex F := p.1
    let r : Vertex F := p.2.1
    let t : Vertex F := p.2.2.1
    let u : Vertex F := p.2.2.2.1
    let w : Vertex F := p.2.2.2.2.1
    let m : Vertex F := p.2.2.2.2.2.1
    let v : Vertex F := p.2.2.2.2.2.2.1
    let D := (Q F r ⊓ Q F u) ⊓ Q F m
    ∃ γ : BasedWalk (graph F) 6 a,
      γ.vertices = [a,r,t,u,w,m,v] ∧ γ.Nonbacktracking ∧
      D ≤ pathStabilizer F γ ∧
      D.map (G₀ L S).subtype ≤ (pathStabilizer F γ).map (G₀ L S).subtype ∧
      C ≤ pathStabilizer F γ ∧
      C.map (G₀ L S).subtype ≤ (pathStabilizer F γ).map (G₀ L S).subtype ∧
      (Theory.GroupAction.CubicTree.LeftRegular (A := G₀ L S) γ ∨
        Theory.GroupAction.CubicTree.RightRegular (A := G₀ L S) γ) := by
  let F := reducedFamily L S
  have hfix : ∀ z ∈ [(p.1 : Vertex F),p.2.1,p.2.2.1,p.2.2.2.1,
      p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2.1], C ≤ stabilizer F z := by
    intro z hz c hc
    exact hfixC hc z (middle_six_vertices p hz)
  obtain ⟨γ,hγv,hγn,hDγ,hDγo,hcases⟩ :=
    opposite_six_path_complement_dichotomy h i p hp hm hy hn eSuz Ry hRy C hK hoddC hfix
  rcases hcases with hs | hr
  · obtain ⟨_,_,_,_,δ,hδv,hδn,hDδ,hDδo,hl⟩ :=
      source_suzuki_opposite_six_path_small_left_regular h i hb p hp hm hy T R hT hR e
        hz hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy
        hc hmin hnat hc6 hc2 hc8 hbranchw hfull hs
    have hCδ : C ≤ pathStabilizer F δ := by
      intro c hc z hz
      exact hfix z (hδv ▸ hz) hc
    exact ⟨δ,hδv,hδn,hDδ,hDδo,hCδ,map_mono hCδ,Or.inl hl⟩
  · have hCγ : C ≤ pathStabilizer F γ := by
      intro c hc z hz
      exact hfix z (hγv ▸ hz) hc
    exact ⟨γ,hγv,hγn,hDγ,hDγo,hCγ,map_mono hCγ,Or.inr hr⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
