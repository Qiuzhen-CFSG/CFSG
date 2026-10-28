module
public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Transport
public import Theory.GroupTheory.Hall.Conjugacy

/-!
# Reduction of Cartan rigidity to a fixed Sylow–torus pair

Sylow conjugacy and Hall conjugacy in the solvable Sylow normalizer carry
an arbitrary Cartan complement to the displayed one. The action and its
quadratic identity are transported by the same genuine group equivalence.
Source: Aschbacher–Smith F.1.3(5), printed p.260.
-/

@[expose] public section
open Subgroup Subgroup.OddHall
namespace CFSG.Quasithin.ChapterF.Source.Unitary
variable {G H : Type*} [Group G] [Group H]

/-- The pointwise quadratic-action assertion for one actual subgroup pair. -/
def PairRigidity (U D : Subgroup G) : Prop :=
  ∀ a : MulAut G, Odd (orderOf a) → U.map a.toMonoidHom = U →
    D.map a.toMonoidHom = D →
    (∀ x ∈ D, a (a x * x⁻¹) = a x * x⁻¹) → ∀ x ∈ D, a x = x

/-- Transport the pair assertion, including the literal displacement identity. -/
theorem pairRigidity_of_equiv (e : G ≃* H) (U D : Subgroup G)
    (hr : PairRigidity (U.map e.toMonoidHom) (D.map e.toMonoidHom)) :
    PairRigidity U D := by
  intro a hao haU haD hquad
  let b := MulAut.congr e a
  have hb : Odd (orderOf b) := by rwa [(MulAut.congr e).orderOf_eq]
  have hbq (x : G) : b (e x) = e (a x) := by
    change e (a (e.symm (e x))) = e (a x)
    rw [e.symm_apply_apply]
  have hmap (V : Subgroup G) :
      (V.map e.toMonoidHom).map b.toMonoidHom = (V.map a.toMonoidHom).map e.toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact hbq x
  have hf := hr b hb (by rw [hmap, haU]) (by rw [hmap, haD]) (by
    rintro z ⟨x,hx,rfl⟩
    change b (b (e x) * (e x)⁻¹) = b (e x) * (e x)⁻¹
    rw [hbq, ← map_inv, ← map_mul, hbq, hquad x hx])
  intro x hx
  apply e.injective
  rw [← hbq]
  exact hf (e x) (mem_map_of_mem e.toMonoidHom hx)

/-- The pair assertion also transports in the forward direction. -/
theorem pairRigidity_map (e : G ≃* H) {U D : Subgroup G} (hr : PairRigidity U D) :
    PairRigidity (U.map e.toMonoidHom) (D.map e.toMonoidHom) := by
  apply pairRigidity_of_equiv e.symm
  have hc : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    exact e.symm_apply_apply x
  simpa only [map_map, hc, map_id] using hr

/-- Hall conjugacy takes any odd complement to the displayed one inside the
same Sylow normalizer; the conjugating element still normalizes the Sylow. -/
theorem pairRigidity_of_odd_complement [Finite G] (S : Sylow 2 G)
    (D E : Subgroup G) (hD : D ≤ normalizer (S : Set G))
    (hE : E ≤ normalizer (S : Set G))
    (hoD : Nat.Coprime 2 (Nat.card D)) (hoE : Nat.Coprime 2 (Nat.card E))
    (hsD : (S : Subgroup G) ⊔ D = normalizer (S : Set G))
    (hsE : (S : Subgroup G) ⊔ E = normalizer (S : Set G))
    (hsolv : Group.IsSolvable (normalizer (S : Set G)))
    (hr : PairRigidity (S : Subgroup G) D) : PairRigidity (S : Subgroup G) E := by
  let B := normalizer (S : Set G)
  have hd := oddHall_of_normalized_sup S.isPGroup' hoD hD hsD
  have he := oddHall_of_normalized_sup S.isPGroup' hoE hE hsE
  obtain ⟨g, hg⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hd he
  have hEg : E = D.map (MulAut.conj (g : G)).toMonoidHom := by
    have hh := congrArg (Subgroup.map B.subtype) hg
    rw [map_subgroupOf_eq_of_le hE, map_map] at hh
    have hc : B.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp B.subtype := by ext x; rfl
    rw [hc, ← map_map, map_subgroupOf_eq_of_le hD] at hh
    exact hh
  have hSg : (S : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp g.property
  simpa only [hSg, ← hEg] using pairRigidity_map (MulAut.conj (g : G)) hr

/-- One explicit odd complement in one solvable Sylow normalizer suffices
for the full intrinsic Cartan statement. -/
theorem cartanRigidity_of_standard_pair [Finite G] (S : Sylow 2 G) (D : Subgroup G)
    (hD : D ≤ normalizer (S : Set G)) (hoD : Nat.Coprime 2 (Nat.card D))
    (hsD : (S : Subgroup G) ⊔ D = normalizer (S : Set G))
    (hsolv : Group.IsSolvable (normalizer (S : Set G)))
    (hr : PairRigidity (S : Subgroup G) D) : CartanQuadraticRigidity G := by
  intro T E hE hoE hdE hsE
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  let e := MulAut.conj g
  have hTS : (T : Subgroup G).map e.toMonoidHom = S := congrArg Sylow.toSubgroup hg
  have hN : (normalizer (T : Set G)).map e.toMonoidHom = normalizer (S : Set G) := by
    have hh := Subgroup.map_equiv_normalizer_eq (T : Subgroup G) e
    change (normalizer (T : Set G)).map e.toMonoidHom = _ at hh
    rw [hTS] at hh
    exact hh
  apply pairRigidity_of_equiv e (T : Subgroup G) E
  rw [hTS]
  apply pairRigidity_of_odd_complement S D (E.map e.toMonoidHom) hD
    (hN ▸ Subgroup.map_mono hE) hoD
  · rwa [← Nat.card_congr (E.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
  · exact hsD
  · rw [← hTS, ← Subgroup.map_sup, hsE, hN]
  · exact hsolv
  · exact hr

end CFSG.Quasithin.ChapterF.Source.Unitary
