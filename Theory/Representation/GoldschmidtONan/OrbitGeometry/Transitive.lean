module

public import Theory.Representation.GoldschmidtONan.OrbitGeometry.RegularBranches

/-!
# The transitive branch of the TI orbit geometry

Suppose the fixed-space orbit has both a member contained in the moved space
and a nonfixed member disjoint from it. Their Y-suborbits, together with the
fixed space, cover every nonzero vector. The first member's transitive
stabilizer action transports to give transitivity on all nonzero vectors.
The TI partition then shows that the fixed-space orbit has odd cardinality.

If the moved space itself were an orbit member, the stabilizer of the fixed
space would fix precisely those two members. Transporting this pair gives a
fixed-point-free involution of the orbit, contradicting odd cardinality.
Thus two distinct Y-images of the first member lie in the moved space; their
disjointness gives the square cardinality bound by an injective addition map.

Source: GLS, Number 2, Chapter C, Proposition 14.2, Step 2,
`refs/KGroup/GLS2/ChapterC.tex`. The theorem takes the two actual suborbit
branches explicitly for use in the final case assembly.
-/

open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
namespace Representation.GoldschmidtONan
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

private theorem orbit_cover_of_mixed [Finite X] [Finite V] (h : Input ρ Y)
    {W U : Submodule (ZMod 2) V} (hW : W ∈ fixedOrbit ρ Y)
    (hWD : W ≤ displacementSpan ρ Y ⊤) (hU : U ∈ fixedOrbit ρ Y)
    (hUF : U ≠ fixedSpace ρ Y) (hUD : Disjoint U (displacementSpan ρ Y ⊤)) :
    ∀ v : V, v ≠ 0 → ∃ S ∈ fixedOrbit ρ Y, v ∈ S := by
  intro v hv0
  by_cases hvF : v ∈ fixedSpace ρ Y
  · exact ⟨_, fixed_mem_fixedOrbit, hvF⟩
  by_cases hvD : v ∈ displacementSpan ρ Y ⊤
  · have hv : v ∈ nonzeroSuborbitUnion ρ Y W := by
      rw [(h.suborbit_of_le_moved hW hWD).1]
      exact ⟨hvD, hv0⟩
    obtain ⟨_, y, hy⟩ := hv
    exact ⟨_, map_mem_fixedOrbit hW y, hy⟩
  · have hv : v ∈ nonzeroSuborbitUnion ρ Y U := by
      rw [h.suborbit_of_disjoint_moved hU hUF hUD]
      exact ⟨hvF, hvD⟩
    obtain ⟨_, y, hy⟩ := hv
    exact ⟨_, map_mem_fixedOrbit hU y, hy⟩

private theorem nonzero_transitive_of_cover (h : Input ρ Y)
    {W : Submodule (ZMod 2) V} (hW : W ∈ fixedOrbit ρ Y)
    (hWD : W ≤ displacementSpan ρ Y ⊤)
    (hc : ∀ v : V, v ≠ 0 → ∃ S ∈ fixedOrbit ρ Y, v ∈ S) :
    NonzeroTransitive ρ := by
  intro v hv0 w hw0
  obtain ⟨S, hS, hvS⟩ := hc v hv0
  obtain ⟨T, hT, hwT⟩ := hc w hw0
  obtain ⟨a, ha⟩ := exists_map_eq_of_mem_fixedOrbit hW hS
  obtain ⟨b, hb⟩ := exists_map_eq_of_mem_fixedOrbit hW hT
  obtain ⟨v', hv', hav⟩ := (show v ∈ W.map (ρ a) from ha ▸ hvS)
  obtain ⟨w', hw', hbw⟩ := (show w ∈ W.map (ρ b) from hb ▸ hwT)
  have hv'0 : v' ≠ 0 := fun he => hv0 (by simpa [he] using hav.symm)
  have hw'0 : w' ≠ 0 := fun he => hw0 (by simpa [he] using hbw.symm)
  obtain ⟨y, _, hy⟩ := (h.suborbit_of_le_moved hW hWD).2 v' hv' hv'0 w' hw' hw'0
  refine ⟨b * y * a⁻¹, ?_⟩
  rw [← hav]
  calc
    ρ (b * y * a⁻¹) (ρ a v') = ρ (b * y) v' := by
      rw [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
    _ = w := by rw [map_mul, Module.End.mul_apply, hy, hbw]

private theorem card_nonzero (A : Type*) [AddCommGroup A] [Finite A] :
    Nat.card {a : A // a ≠ 0} = Nat.card A - 1 := by
  classical
  let := Fintype.ofFinite A
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Nat.card_eq_fintype_card]

private theorem orbit_card_mul (h : Input ρ Y) [Finite V]
    (hc : ∀ v : V, v ≠ 0 → ∃ S ∈ fixedOrbit ρ Y, v ∈ S) :
    Nat.card {v : V // v ≠ 0} = Nat.card (fixedOrbit ρ Y) * (Nat.card (fixedSpace ρ Y) - 1) := by
  classical
  let Ω := fixedOrbit ρ Y
  let f : (Σ W : Ω, {v : W.val // v ≠ 0}) → {v : V // v ≠ 0} := fun a =>
    ⟨a.2.val.val, fun he => a.2.property (Subtype.ext he)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨S, v⟩ ⟨T, w⟩ he
      have he' : (v.val : V) = w.val := congrArg Subtype.val he
      have hST : S = T := Subtype.ext (h.orbit_eq_of_common_nonzero S.property T.property
        v.val.property (he' ▸ w.val.property) (fun he => v.property (Subtype.ext he)))
      subst T
      congr 1
      exact Subtype.ext (Subtype.ext he')
    · intro v
      obtain ⟨W, hW, hvW⟩ := hc v v.property
      exact ⟨⟨⟨W, hW⟩, ⟨⟨v, hvW⟩, fun he => v.property (congrArg Subtype.val he)⟩⟩, rfl⟩
  let := Fintype.ofFinite Ω
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sigma]
  have he : ∀ W : Ω, Nat.card {v : W.val // v ≠ 0} = Nat.card (fixedSpace ρ Y) - 1 := by
    intro W
    rw [card_nonzero, card_eq_fixed_of_mem_fixedOrbit W.property]
  simp only [he, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  rfl

private theorem odd_orbit_card_of_cover [Finite X] [Finite V] (h : Input ρ Y)
    (hc : ∀ v : V, v ≠ 0 → ∃ S ∈ fixedOrbit ρ Y, v ∈ S) :
    Odd (Nat.card (fixedOrbit ρ Y)) := by
  have hm := orbit_card_mul h hc
  have he : Even (Nat.card V) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card]
    exact even_two.pow_of_ne_zero (by have := h.dimension_ge_three; omega)
  have ho : Odd (Nat.card V - 1) := by
    have hp : 0 < Nat.card V := Nat.card_pos
    exact (Nat.odd_sub' (by omega)).mpr (by simpa using he)
  rw [← card_nonzero V, hm] at ho
  exact (Nat.odd_mul.mp ho).1

/-- A transitive finite action whose point stabilizer fixes exactly two points
has even degree: transport the second point to construct a commuting involution. -/
private theorem even_card_of_two_fixed {A : Type*} [Finite A] [MulAction X A]
    (a b : A) (hab : a ≠ b)
    (ht : ∀ u v : A, ∃ x : X, x • u = v)
    (hle : ∀ x : X, x • a = a → x • b = b)
    (hfix : ∀ u : A, (∀ x : X, x • a = a → x • u = u) → u = a ∨ u = b) :
    Even (Nat.card A) := by
  classical
  choose g hg using ht a
  let f : A → A := fun u => g u • b
  have hf (x : X) : f (x • a) = x • b := by
    have hs : (x⁻¹ * g (x • a)) • a = a := by
      rw [mul_smul, hg, inv_smul_smul]
    have hb := hle _ hs
    have hh := congrArg (fun u : A => x • u) hb
    simpa only [mul_smul, smul_inv_smul] using hh
  have he (x : X) (u : A) : f (x • u) = x • f u := by
    conv_lhs => rw [← hg u, ← mul_smul, hf]
    exact mul_smul x (g u) b
  have hfa : f a = b := by simpa only [one_smul] using hf 1
  have hsurj : Function.Surjective f := by
    intro u
    obtain ⟨x, hx⟩ := ht b u
    exact ⟨x • a, (hf x).trans hx⟩
  have hinj := Finite.injective_iff_surjective.mpr hsurj
  have hfb : f b = a := by
    rcases hfix (f b) (fun x hx => by rw [← he, hle x hx]) with ha | hb
    · exact ha
    · exact False.elim (hab (hinj (hfa.trans hb.symm)))
  have hinv : Function.Involutive f := by
    intro u
    rw [← hg u, hf, he, hfb]
  have hne : ∀ u : A, f u ≠ u := by
    intro u hu
    rw [← hg u, hf] at hu
    exact hab (MulAction.injective (g u) hu).symm
  let := Fintype.ofFinite A
  have hz : (Nat.card A : ZMod 2) = 0 := by
    have hs := Finset.sum_ninvolution (s := Finset.univ) (f := fun _ : A => (1 : ZMod 2)) f
      (fun _ => by decide) (fun u _ => hne u) (fun _ => Finset.mem_univ _) hinv
    simpa only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (ZMod 2),
      smul_eq_mul, mul_one, Nat.card_eq_fintype_card] using hs
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp hz)

local instance orbitAction : MulAction X (fixedOrbit ρ Y) where
  smul x W := ⟨W.val.map (ρ x), map_mem_fixedOrbit W.property x⟩
  one_smul W := Subtype.ext (orbit_map_one W.val)
  mul_smul x y W := Subtype.ext (orbit_map_mul W.val x y)

private theorem even_orbit_card_of_moved_mem [Finite X] [Finite V] (h : Input ρ Y)
    (hD : displacementSpan ρ Y ⊤ ∈ fixedOrbit ρ Y) :
    Even (Nat.card (fixedOrbit ρ Y)) := by
  let a : fixedOrbit ρ Y := ⟨fixedSpace ρ Y, fixed_mem_fixedOrbit⟩
  let b : fixedOrbit ρ Y := ⟨displacementSpan ρ Y ⊤, hD⟩
  apply even_card_of_two_fixed (X := X) a b
  · exact fun he => h.fixed_ne_moved (congrArg Subtype.val he)
  · intro u v
    obtain ⟨x, hx⟩ := exists_map_eq_of_mem_fixedOrbit u.property v.property
    exact ⟨x, Subtype.ext hx⟩
  · intro x hx
    exact Subtype.ext (h.moved_map_of_fixed_map x (congrArg Subtype.val hx))
  · intro u hu
    by_cases hUF : u.val = fixedSpace ρ Y
    · exact Or.inl (Subtype.ext hUF)
    right
    obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.nontrivial
    have hyu : u.val.map (ρ y) = u.val := congrArg Subtype.val
      (hu y (Subtype.ext (fixed_map_actor y)))
    have hle := h.orbit_le_moved_of_stabilizer_ne_one u.property hUF hy1 hyu
    apply Subtype.ext
    exact Submodule.eq_of_le_of_finrank_eq hle
      ((finrank_eq_fixed_of_mem_fixedOrbit u.property).trans
        (finrank_eq_fixed_of_mem_fixedOrbit hD).symm)

private theorem fixed_card_sq_le_of_odd_orbit [Finite X] [Finite V] (h : Input ρ Y)
    (ho : Odd (Nat.card (fixedOrbit ρ Y)))
    {W : Submodule (ZMod 2) V} (hW : W ∈ fixedOrbit ρ Y)
    (hWD : W ≤ displacementSpan ρ Y ⊤) :
    Nat.card (fixedSpace ρ Y) ^ 2 ≤ Nat.card (displacementSpan ρ Y ⊤) := by
  have hnD : displacementSpan ρ Y ⊤ ∉ fixedOrbit ρ Y := fun hD =>
    (Nat.not_even_iff_odd.mpr ho) (even_orbit_card_of_moved_mem h hD)
  have hlt : W < displacementSpan ρ Y ⊤ :=
    lt_of_le_of_ne hWD (fun he => hnD (he ▸ hW))
  obtain ⟨d, hdD, hdW⟩ := SetLike.exists_of_lt hlt
  have hd0 : d ≠ 0 := fun he => hdW (he ▸ W.zero_mem)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h.orbit_ne_bot hW)
  obtain ⟨y, hy⟩ := h.transitive w (hWD hw) hw0 d hdD hd0
  let U := W.map (ρ y)
  have hU : U ∈ fixedOrbit ρ Y := map_mem_fixedOrbit hW y
  have hUD : U ≤ displacementSpan ρ Y ⊤ := by
    rintro _ ⟨v, hv, rfl⟩
    exact moved_mem_action y (hWD hv)
  have hWU : W ≠ U := by
    intro he
    exact hdW (he ▸ (show d ∈ U from ⟨w, hw, hy⟩))
  have hdis := h.ti W hW U hU hWU
  let f : W × U → displacementSpan ρ Y ⊤ := fun p =>
    ⟨(p.1 : V) + p.2, (displacementSpan ρ Y ⊤).add_mem (hWD p.1.property) (hUD p.2.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have he : (a.1 : V) + a.2 = (b.1 : V) + b.2 := congrArg Subtype.val hab
    have hd : (a.1 : V) - b.1 = (b.2 : V) - a.2 := by
      apply sub_eq_sub_iff_add_eq_add.mpr
      simpa only [add_comm] using he
    have hz : (a.1 : V) - b.1 = 0 := Submodule.disjoint_def.mp hdis _
      (W.sub_mem a.1.property b.1.property) (hd ▸ U.sub_mem b.2.property a.2.property)
    have h1 : a.1 = b.1 := Subtype.ext (sub_eq_zero.mp hz)
    have h2 : a.2 = b.2 := Subtype.ext (by simpa only [h1, add_right_inj] using he)
    exact Prod.ext h1 h2
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod, card_eq_fixed_of_mem_fixedOrbit hW,
    card_eq_fixed_of_mem_fixedOrbit hU, pow_two] using hc

/-- The mixed Step 2 branch: one orbit member lies in the moved space and
another nonfixed member is disjoint from it. These genuine suborbit witnesses
give nonzero transitivity, odd orbit cardinality and the square size bound. -/
public theorem Input.transitiveGeometry_of_mixed_suborbits [Finite X] [Finite V] (h : Input ρ Y)
    {W U : Submodule (ZMod 2) V} (hW : W ∈ fixedOrbit ρ Y)
    (hWD : W ≤ displacementSpan ρ Y ⊤) (hU : U ∈ fixedOrbit ρ Y)
    (hUF : U ≠ fixedSpace ρ Y) (hUD : Disjoint U (displacementSpan ρ Y ⊤)) :
    TransitiveGeometry ρ Y := by
  have hc := orbit_cover_of_mixed h hW hWD hU hUF hUD
  have ho := odd_orbit_card_of_cover h hc
  exact ⟨nonzero_transitive_of_cover h hW hWD hc, ho,
    fixed_card_sq_le_of_odd_orbit h ho hW hWD⟩
end Representation.GoldschmidtONan
