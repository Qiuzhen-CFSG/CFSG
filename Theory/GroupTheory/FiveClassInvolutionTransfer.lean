module
public import Theory.GroupTheory.InvolutionFusionCover
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Transfer obstruction for a five-class involution configuration

Two index-two subgroups force three marked involutions to fuse. Bounds on
Sylow centralizers then make their centralizer Sylow subgroup fully centralized.
A fourth involution commuting with one of them must enter that Sylow subgroup,
contrary to its stated class cover.

This is the terminal transfer argument in Aschbacher--Smith, The Classification
of Quasithin Groups, Lemma 2.4.34, printed p.548. The local class covers remain
explicit, so the result applies to a marked local model without strengthening
its local conjugacies to an assumed ambient classification.
-/

public section
namespace Sylow
open Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem orderOf_conj_eq {a b : G} (h : IsConj a b) :
    orderOf b = orderOf a := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (MulAut.conj g).orderOf_eq a

/-- Thompson transfer through a three-class cover fuses an involution to the
remaining representative when the other two classes have been excluded. -/
theorem isConj_of_index_two_three_class_cover
    (T : Sylow 2 G) (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (U : Subgroup T) (hU : U.index = 2) (a b x s : T)
    (hx : orderOf (x : G) = 2)
    (hxa : ¬ IsConj (x : G) (a : G)) (hxb : ¬ IsConj (x : G) (b : G))
    (hcover : ∀ t : T, t ∈ U → orderOf (t : G) = 2 →
      IsConj (a : G) (t : G) ∨ IsConj (b : G) (t : G) ∨
        IsConj (s : G) (t : G)) :
    IsConj (x : G) (s : G) := by
  obtain ⟨t, ht, hxt⟩ :=
    T.exists_isConj_mem_of_index_two_ambient hno U hU (x : G) hx
  rcases hcover t ht ((orderOf_conj_eq hxt).trans hx) with hat | hbt | hst
  · exact (hxa (hxt.trans hat.symm)).elim
  · exact (hxb (hxt.trans hbt.symm)).elim
  · exact hxt.trans hst.symm

/-- The marked five-class local configuration cannot occur in a finite group
without a normal subgroup of index two. All class covers refer to ambient
conjugacy; a local model supplies them by mapping its literal conjugators. -/
theorem five_class_involution_transfer_false
    (T : Sylow 2 G) (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (U V : Subgroup T) (hU : U.index = 2) (hV : V.index = 2)
    (a b x s y : T) (hx : orderOf (x : G) = 2) (hb : orderOf (b : G) = 2)
    (hxa : ¬ IsConj (x : G) (a : G)) (hxb : ¬ IsConj (x : G) (b : G))
    (hba : ¬ IsConj (b : G) (a : G))
    (hUcover : ∀ t : T, t ∈ U → orderOf (t : G) = 2 →
      IsConj (a : G) (t : G) ∨ IsConj (b : G) (t : G) ∨
        IsConj (s : G) (t : G))
    (hVcover : ∀ t : T, t ∈ V → orderOf (t : G) = 2 →
      IsConj (a : G) (t : G) ∨ IsConj (b : G) (t : G) ∨
        IsConj (y : G) (t : G))
    (hbound : ∀ t : T, orderOf (t : G) = 2 →
      IsConj (a : G) (t : G) ∨ IsConj (b : G) (t : G) ∨
        Nat.card (centralizer ({t} : Set T)) ≤ Nat.card (centralizer ({s} : Set T)))
    (hcentralizer : ∀ t : T, t ∈ centralizer ({s} : Set T) →
      orderOf (t : G) = 2 →
      IsConj (a : G) (t : G) ∨ IsConj (x : G) (t : G) ∨
        IsConj (s : G) (t : G) ∨ IsConj (y : G) (t : G))
    (hbx : Commute b x) : False := by
  have hxs := T.isConj_of_index_two_three_class_cover hno U hU a b x s
    hx hxa hxb hUcover
  have hxy := T.isConj_of_index_two_three_class_cover hno V hV a b x y
    hx hxa hxb hVcover
  have hs : orderOf (s : G) = 2 := (orderOf_conj_eq hxs).trans hx
  have hmax (t : T) (hst : IsConj (s : G) (t : G)) :
      Nat.card (centralizer ({t} : Set T)) ≤
        Nat.card (centralizer ({s} : Set T)) := by
    rcases hbound t ((orderOf_conj_eq hst).trans hs) with hat | hbt | hle
    · exact (hxa ((hxs.trans hst).trans hat.symm)).elim
    · exact (hxb ((hxs.trans hst).trans hbt.symm)).elim
    · exact hle
  obtain ⟨P, hP⟩ := T.exists_centralizer_sylow_of_card_bound s hmax
  obtain ⟨g, hg⟩ := isConj_iff.mp hxs
  let C : Subgroup G := centralizer ({(s : G)} : Set G)
  have hbC : MulAut.conj g (b : G) ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hg]
    change (MulAut.conj g) (b : G) * (MulAut.conj g) (x : G) =
      (MulAut.conj g) (x : G) * (MulAut.conj g) (b : G)
    exact ((hbx.map (T : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom).eq
  let bC : C := ⟨MulAut.conj g (b : G), hbC⟩
  have hbCorder : orderOf bC = 2 ^ 1 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (MulAut.conj g (b : G)) = 2 ^ 1
    rw [(MulAut.conj g).orderOf_eq, hb, pow_one]
  obtain ⟨p, hbp⟩ := P.exists_isConj_of_orderOf_eq_prime_pow hbCorder
  have hpmap : ((p : C) : G) ∈
      (centralizer ({s} : Set T)).map (T : Subgroup G).subtype := by
    rw [← hP]
    exact mem_map_of_mem _ p.property
  obtain ⟨t, hts, htp⟩ := hpmap
  have hbt : IsConj (b : G) (t : G) := by
    have hbbC : IsConj (b : G) (bC : G) := isConj_iff.mpr ⟨g, rfl⟩
    apply hbbC.trans
    change IsConj (C.subtype bC) ((T : Subgroup G).subtype t)
    rw [htp]
    exact C.subtype.map_isConj hbp
  rcases hcentralizer t hts ((orderOf_conj_eq hbt).trans hb) with hat | hxt | hst | hyt
  · exact hba (hbt.trans hat.symm)
  · exact hxb (hxt.trans hbt.symm)
  · exact hxb ((hxs.trans hst).trans hbt.symm)
  · exact hxb ((hxy.trans hyt).trans hbt.symm)

end Sylow
