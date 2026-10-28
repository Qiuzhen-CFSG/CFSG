module

public import Theory.GroupTheory.Recognition.HeldM22A10.Setup
public import Theory.GroupTheory.Recognition.HeldM22A10.LocalStructure
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.CentralizerModels
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.ModelInvolutions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.Exhaustion

/-!
# The A10 branch of Held recognition: final reduction

We retain two explicit obligations from Held's proof: the double transposition
transported through the given centralizer equivalence is not conjugate to the
distinguished central involution and has ambient centralizer order 2880; and
there is a subgroup Q containing that whole centralizer with Q isomorphic to
A10. These assertions are not assumed to follow from LocalData here.

Given them, the proof is complete. The centralizer of the distinguished
involution inside Q has order 384, so it belongs to the four-transposition
class under any Q-to-A10 equivalence. Nonconjugacy places the transported
double transposition in the other class. Comparing centralizer orders shows
that Q contains its full ambient centralizer too. The two model classes then
show that Q contains the ambient centralizer of every one of its involutions.
The elementary exhaustion lemma forces Q = G and gives the required actual
multiplicative equivalence.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756. The pending local analysis is in Sections 2 and 4;
the overgroup construction is Lemma 5.11. This module proves the conditional
assembly corresponding to Lemma 5.12, not yet unconditional Theorem B.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10
universe u v
namespace A10Identification

private theorem centralizer_card_equiv {G : Type u} {K : Type v} [Group G] [Group K]
    (f : G ≃* K) (x : G) :
    Nat.card (centralizer ({x} : Set G)) = Nat.card (centralizer ({f x} : Set K)) := by
  apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
  intro a
  change a ∈ centralizer ({x} : Set G) ↔ f a ∈ centralizer ({f x} : Set K)
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro ha
    simpa only [map_mul] using congrArg f ha
  · intro ha
    apply f.injective
    simpa only [map_mul] using ha

private theorem centralizer_card_conj {G : Type u} [Group G] {x y : G}
    (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set G)) = Nat.card (centralizer ({y} : Set G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have he : (MulAut.conj g) x = y := hg
  simpa only [he] using centralizer_card_equiv (MulAut.conj g) x

private theorem subgroup_centralizer_card {G : Type u} [Group G]
    (Q : Subgroup G) (x : Q)
    (hC : centralizer ({(x : G)} : Set G) ≤ Q) :
    Nat.card (centralizer ({x} : Set Q)) =
      Nat.card (centralizer ({(x : G)} : Set G)) := by
  have hsub : centralizer ({x} : Set Q) =
      (centralizer ({(x : G)} : Set G)).subgroupOf Q := by
    ext y
    simp only [mem_centralizer_singleton_iff, mem_subgroupOf, Subtype.ext_iff]
    rfl
  rw [hsub]
  exact Nat.card_congr (subgroupOfEquivOfLe hC).toEquiv

private theorem centralizer_le_of_card_eq {G : Type u} [Group G] [Finite G]
    (Q : Subgroup G) (x : Q)
    (hcard : Nat.card (centralizer ({x} : Set Q)) =
      Nat.card (centralizer ({(x : G)} : Set G))) :
    centralizer ({(x : G)} : Set G) ≤ Q := by
  let C : Subgroup G := (centralizer ({x} : Set Q)).map Q.subtype
  have hC : C ≤ centralizer ({(x : G)} : Set G) := by
    rintro a ⟨b, hb, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hb))
  have hc : Nat.card C = Nat.card (centralizer ({(x : G)} : Set G)) := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective]
    exact hcard
  have he := Subgroup.eq_of_le_of_card_ge hC hc.ge
  exact he ▸ Subgroup.map_subtype_le (centralizer ({x} : Set Q))

private theorem centralizer_le_of_conjugate {G : Type u} [Group G] [Finite G]
    (Q : Subgroup G) {x y : Q}
    (hC : centralizer ({(x : G)} : Set G) ≤ Q) (hxy : IsConj x y) :
    centralizer ({(y : G)} : Set G) ≤ Q := by
  apply centralizer_le_of_card_eq Q y
  calc
    Nat.card (centralizer ({y} : Set Q)) = Nat.card (centralizer ({x} : Set Q)) :=
      (centralizer_card_conj hxy).symm
    _ = Nat.card (centralizer ({(x : G)} : Set G)) := subgroup_centralizer_card Q x hC
    _ = Nat.card (centralizer ({(y : G)} : Set G)) :=
      centralizer_card_conj (Q.subtype.map_isConj hxy)

private theorem isConj_of_equiv {G : Type u} {K : Type v} [Group G] [Group K]
    (f : G ≃* K) {x y : G} (h : IsConj (f x) (f y)) : IsConj x y := by
  simpa only [MulEquiv.coe_toMonoidHom, f.symm_apply_apply] using f.symm.toMonoidHom.map_isConj h

end A10Identification
open A10Identification

/-- Conditional final assembly; the ambient local analysis and the A10 overgroup
are separate proof obligations. -/
public theorem a10Identification_of_local_analysis_and_overgroup
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880)
    (Q : Subgroup G) (hHQ : D.centralizer ≤ Q) (f : Q ≃* alternatingGroup (Fin 10)) :
    Nonempty (G ≃* alternatingGroup (Fin 10)) := by
  let z : Q := ⟨D.z, hHQ D.centralInvolution.property⟩
  let m : Q := ⟨D.a10NoncentralInvolution e, hHQ (D.a10NoncentralInvolution_mem e)⟩
  have hz : orderOf z = 2 := by simpa only [z, Subgroup.orderOf_mk] using D.z_order
  have hm : orderOf m = 2 := by
    simpa only [m, Subgroup.orderOf_mk] using D.a10NoncentralInvolution_order e
  have hzcard : Nat.card (centralizer ({z} : Set Q)) = 384 :=
    (subgroup_centralizer_card Q z hHQ).trans D.centralizer_card
  have hzimage : IsConj CentralizerModels.a10Involution (f z) := by
    rcases involution_classes (f z) ((f.orderOf_eq z).trans hz) with h | h
    · exact h
    · have hc : Nat.card (centralizer ({f z} : Set (alternatingGroup (Fin 10)))) = 2880 :=
        (centralizer_card_conj h).symm.trans centralizer_noncentral_card
      have he := centralizer_card_equiv f z
      rw [hzcard, hc] at he
      contradiction
  have hmimage : IsConj doubleTransposition (f m) := by
    rcases involution_classes (f m) ((f.orderOf_eq m).trans hm) with h | h
    · exact False.elim (hfusion (Q.subtype.map_isConj
        (isConj_of_equiv f (hzimage.symm.trans h))))
    · exact h
  have hmcard : Nat.card (centralizer ({m} : Set Q)) = 2880 :=
    (centralizer_card_equiv f m).trans
      ((centralizer_card_conj hmimage).symm.trans centralizer_noncentral_card)
  have hCm : centralizer ({(m : G)} : Set G) ≤ Q :=
    centralizer_le_of_card_eq Q m (hmcard.trans hcentralizer.symm)
  have hC : ∀ t ∈ Q, orderOf t = 2 → centralizer ({t} : Set G) ≤ Q := by
    intro t ht hto
    let tq : Q := ⟨t, ht⟩
    have htq : orderOf tq = 2 := by simpa only [tq, Subgroup.orderOf_mk] using hto
    rcases involution_classes (f tq) ((f.orderOf_eq tq).trans htq) with h | h
    · exact centralizer_le_of_conjugate Q hHQ (isConj_of_equiv f (hzimage.symm.trans h))
    · exact centralizer_le_of_conjugate Q hCm (isConj_of_equiv f (hmimage.symm.trans h))
  have hQ : Q = ⊤ := eq_top_of_centralizers_of_not_isConj Q hC z.property D.z_order
    m.property (D.a10NoncentralInvolution_order e) hfusion
  let qG : Q ≃* G := (MulEquiv.subgroupCongr hQ).trans Subgroup.topEquiv
  exact ⟨qG.symm.trans f⟩

end Theory.GroupTheory.HeldM22A10
