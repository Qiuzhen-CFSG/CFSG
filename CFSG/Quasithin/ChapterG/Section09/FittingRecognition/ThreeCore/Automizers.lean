module

public import CFSG.Quasithin.ChapterA.Section01.RankActions.AutomorphismQuotient
public import Theory.SpecificGroups.GL2.SemidihedralSylow

/-!
# Elementary two-sections of three-group automizers

A.1.25 constructs an actual homomorphism Aut(P) → GL₂(3) with three-group
kernel when P has three-rank at most two. That kernel vanishes in an
elementary two-quotient. A Sylow two-subgroup of the remaining matrix
subgroup surjects onto the quotient and embeds in a semidihedral Sylow
of GL₂(3). Its cyclic subgroup of index two has an image of order at most
two, still of index at most two. Thus the elementary quotient has order
at most four; no arbitrary quotient-rank monotonicity is used.

The final transport lemma constructs the literal automizer section from
faithfulness on a normal subgroup's image under a covering map.

Source: Aschbacher--Smith, A.1.25(2), printed p.25, and the covering
automizer step in the proof of G.9.4, printed p.355, PDF p.366.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition

open Subgroup Matrix

universe u v

private theorem elementary_image_card_le_four
    {P S E : Type*} [Group P] [Finite P] [Group S] [Finite S]
    [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (C : Subgroup P) [IsCyclic C] (hi : C.index ≤ 2)
    (k : S →* P) (hk : Function.Injective k)
    (f : S →* E) (hf : Function.Surjective f) : Nat.card E ≤ 4 := by
  let D := C.comap k
  let kd : D →* C := (k.comp D.subtype).codRestrict C (fun x => x.property)
  let : IsCyclic D := isCyclic_of_injective kd (by
    intro x y hxy
    apply Subtype.ext
    exact hk (congrArg Subtype.val hxy))
  let I := D.map f
  let : IsCyclic I := isCyclic_of_surjective (f.subgroupMap D) (f.subgroupMap_surjective D)
  have hcard : Nat.card I ≤ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by decide) ((Monoid.exponent_dvd_of_monoidHom I.subtype I.subtype_injective).trans
      (IsElementaryAbelian.exponent_dvd_p 2 E))
  have hiD : D.index ≤ 2 := by
    rw [show D = C.comap k from rfl, C.index_comap k]
    exact (C.relIndex_le_of_le_right (show k.range ≤ ⊤ from le_top)
      (by simpa only [C.relIndex_top_right] using C.index_ne_zero_of_finite)).trans
      (by simpa only [C.relIndex_top_right] using hi)
  have hiI : I.index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero D.index_ne_zero_of_finite) (D.index_map_dvd hf)).trans hiD
  have hmul := I.index_mul_card
  nlinarith

private theorem gl_three_elementary_section_card
    (H : Subgroup (GL (Fin 2) (ZMod 3)))
    {E : Type u} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (f : H →* E) (hf : Function.Surjective f) : Nat.card E ≤ 4 := by
  obtain ⟨P, n, hn, hcard, a, b, ha, hb, hc, hg, hz, hscalar⟩ :=
    GeneralLinearGroup.exists_semidihedral_sylow (ZMod 3) (by rw [Nat.card_zmod])
  let C := zpowers a
  have hi : C.index = 2 := by
    have h := C.index_mul_card
    have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
      omega
    rw [show Nat.card C = 2 ^ (n - 1) by rw [Nat.card_zpowers, ha]] at h
    have hh := h.trans hcard
    rw [hp] at hh
    exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ (n - 1)) hh
  let S : Sylow 2 H := Classical.choice inferInstance
  obtain ⟨T, hT⟩ := (S.isPGroup'.map H.subtype).exists_le_sylow
  let s : S →* GL (Fin 2) (ZMod 3) := H.subtype.comp (S : Subgroup H).subtype
  let k : S →* P := (T.equiv P).toMonoidHom.comp
    (s.codRestrict T (fun x => hT (mem_map.mpr ⟨x, x.property, rfl⟩)))
  have hk : Function.Injective k := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hh := congrArg (fun z : T => (z : GL (Fin 2) (ZMod 3))) ((T.equiv P).injective hxy)
    exact hh
  have hsurj : Function.Surjective (f.comp (S : Subgroup H).subtype) := by
    let U := S.mapSurjective hf
    have htop : (U : Subgroup E) = ⊤ :=
      (U.is_maximal' ((IsElementaryAbelian.isPGroup 2 E).to_subgroup ⊤) le_top).symm
    intro y
    have hy : y ∈ (S : Subgroup H).map f := by
      rw [← Sylow.coe_mapSurjective hf S, htop]
      trivial
    obtain ⟨x, hx, he⟩ := hy
    exact ⟨⟨x, hx⟩, he⟩
  exact elementary_image_card_le_four C hi.le k hk _ hsurj

/-- Every elementary two-group section of the automorphism group of a finite
rank-two three-group has order at most four. The three-group action kernel is
killed before passing to the actual ternary matrix subgroup. -/
theorem three_automorphism_elementary_section_card
    {P : Type u} [Group P] [Finite P] (hP : IsPGroup 3 P) (hr : primeRank 3 P ≤ 2)
    (H : Subgroup (MulAut P)) {E : Type v} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (f : H →* E) (hf : Function.Surjective f) :
    Nat.card E ≤ 4 := by
  obtain ⟨r, hr⟩ := CFSG.Quasithin.ChapterA.RankActions.smallRankAutomorphismRepresentation
    3 (by decide) P hP hr
  let a := r.comp H.subtype
  have hker : IsPGroup 3 a.ker := by
    let j : a.ker →* r.ker := (H.subtype.comp a.ker.subtype).codRestrict r.ker
      (fun x => x.property)
    exact hr.of_injective j (by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : r.ker => (z : MulAut P)) hxy)
  have hbot : a.ker.map f = ⊥ := by
    exact disjoint_top.mp (IsPGroup.disjoint_of_ne 3 2 (by decide) (a.ker.map f) ⊤
      (hker.map f) ((IsElementaryAbelian.isPGroup 2 E).to_subgroup ⊤))
  have hk : a.rangeRestrict.ker ≤ f.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    intro x hx
    have hm := mem_map_of_mem f hx
    rw [hbot, mem_bot] at hm
    exact hm
  let q := a.rangeRestrict.liftOfSurjective a.rangeRestrict_surjective ⟨f, hk⟩
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨a.rangeRestrict x, a.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ x⟩
  exact gl_three_elementary_section_card a.range q hq

variable {D G : Type u} [Group D] [Group G]

/-- A faithful actor on a normal subgroup's image is a section of the
literal covering conjugation image. The section map is induced by the original
surjection on the actor preimage. -/
theorem exists_automizer_section (f : D →* G) (hs : Function.Surjective f)
    (B : Subgroup D) [B.Normal] (A : Subgroup G)
    (hf : A ⊓ centralizer (B.map f : Set G) = ⊥) :
    ∃ H : Subgroup (MulAut B), H ≤ (MulAut.conjNormal : D →* MulAut B).range ∧
      ∃ q : H →* A, Function.Surjective q := by
  let E := A.comap f
  let a : E →* MulAut B := (MulAut.conjNormal : D →* MulAut B).comp E.subtype
  let p : E →* A := {
    toFun x := ⟨f x, x.property⟩
    map_one' := Subtype.ext f.map_one
    map_mul' x y := Subtype.ext (f.map_mul x y) }
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨y, hy⟩ := hs x
    exact ⟨⟨y, by change f y ∈ A; rw [hy]; exact x.property⟩, Subtype.ext hy⟩
  have hk : a.rangeRestrict.ker ≤ p.ker := by
    intro x hx
    have ha : a x = 1 := congrArg Subtype.val hx
    have hcent : f x ∈ centralizer (B.map f : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      have he := congrArg (fun t : MulAut B => (t ⟨z, hz⟩ : D)) ha
      change (x : D) * z * (x : D)⁻¹ = z at he
      have he' : (x : D) * z = z * x := (mul_inv_eq_iff_eq_mul).mp he
      simpa only [map_mul] using congrArg f he'.symm
    have hx1 : f x = 1 := by
      have hm : f x ∈ A ⊓ centralizer (B.map f : Set G) := ⟨x.property, hcent⟩
      rwa [hf, mem_bot] at hm
    exact Subtype.ext hx1
  let q := a.rangeRestrict.liftOfSurjective a.rangeRestrict_surjective ⟨p, hk⟩
  have he (x : E) : q (a.rangeRestrict x) = p x :=
    a.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ x
  refine ⟨a.range, ?_, q, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨a.rangeRestrict x, he x⟩

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
