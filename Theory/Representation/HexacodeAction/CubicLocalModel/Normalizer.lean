module

public import Theory.Representation.HexacodeAction.CubicLocalModel.Orders.PointStabilizer
public import Theory.Representation.HexacodeAction.OuterTwo
public import Theory.Representation.BinaryPermutationMulAction
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PPerfectHom

/-!
# Normalizer and centralizer calculations for the covered cubic model

The fixed space of the actual point residual is exactly its defining line,
so its normalizer in the cover is the full line stabilizer. The central
kernel of inner conjugation lies in the point residual. Consequently the
inner part of its automorphism normalizer is the image of that stabilizer.
The outer automorphism group is a two-group; residual transport then places
every two-perfect normalizing subgroup in the inner point-residual image.

The natural six-letter action also has trivial centralizer in the automorphism
group of its binary natural module. Two explicit three-cycles determine a
marked duad, and the alternating action moves it to every nonzero vector.
All finite checks concern only six-letter permutations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed p.954/PDF p.971; natural-module geometry from §B.3 and
Notation 13.2.1. The concrete cover and coordinate map are from the licensed
ATLAS port re-exported by `Orders.PointStabilizer`.
-/

@[expose] public section

namespace Representation.Hexacode.CubicLocalModel

open Subgroup
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

private abbrev Ω := Fin 6
private abbrev V := Multiplicative (natural Ω)

private def cycleA : Equiv.Perm Ω := Equiv.swap 0 1 * Equiv.swap 1 2
private def cycleB : Equiv.Perm Ω := Equiv.swap 1 2 * Equiv.swap 1 3

private theorem cycles_even :
    cycleA ∈ alternatingGroup Ω ∧ cycleB ∈ alternatingGroup Ω := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem cycles_fix :
    naturalRepresentation Ω cycleA (pairVector 4 5) = pairVector 4 5 ∧
    naturalRepresentation Ω cycleB (pairVector 4 5) = pairVector 4 5 := by
  constructor
  · rw [pairVector_map]
    change pairVector 4 5 = pairVector 4 5
    rfl
  · rw [pairVector_map]
    change pairVector 4 5 = pairVector 4 5
    rfl

private theorem cycles_fixed (v : natural Ω)
    (ha : naturalRepresentation Ω cycleA v = v)
    (hb : naturalRepresentation Ω cycleB v = v) :
    v = 0 ∨ v = pairVector 4 5 := by
  rcases vector_cases v with rfl | ⟨⟨⟨i, j⟩, hij⟩, rfl⟩
  · exact Or.inl rfl
  · change naturalRepresentation Ω cycleA (pairVector i j) = pairVector i j at ha
    change naturalRepresentation Ω cycleB (pairVector i j) = pairVector i j at hb
    rw [pairVector_map] at ha hb
    change pairVector i j = 0 ∨ pairVector i j = pairVector 4 5
    have hA : pair (cycleA i) (cycleA j) = pair i j :=
      (pairVector_eq_iff (cycleA.injective.ne hij.ne) hij.ne).mp ha
    have hB : pair (cycleB i) (cycleB j) = pair i j :=
      (pairVector_eq_iff (cycleB.injective.ne hij.ne) hij.ne).mp hb
    have hfixed : ∀ i j : Ω, i < j →
        pair (cycleA i) (cycleA j) = pair i j →
        pair (cycleB i) (cycleB j) = pair i j →
        i = 4 ∧ j = 5 := by
      decide +kernel
    rcases hfixed i j hij hA hB with ⟨rfl, rfl⟩
    exact Or.inr rfl

private def rawDuadMover
    (d : Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.Duad) :
    Equiv.Perm Ω :=
  Equiv.swap ((Equiv.swap 4 d.val.1) 5) d.val.2 * Equiv.swap 4 d.val.1

private def duadMover
    (d : Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.Duad) :
    Equiv.Perm Ω :=
  if Equiv.Perm.sign (rawDuadMover d) = 1 then rawDuadMover d
  else rawDuadMover d * Equiv.swap 0 1

set_option maxRecDepth 4096 in
private theorem duadMover_even : ∀ d :
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.Duad,
    duadMover d ∈ alternatingGroup Ω := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem duadMover_apply : ∀ d :
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.Duad,
    duadMover d 4 = d.val.1 ∧ duadMover d 5 = d.val.2 := by
  decide +kernel

private theorem line_image (W : Submodule (ZMod 2) (natural Ω))
    (hdim : Module.finrank (ZMod 2) W = 1) :
    ∃ g : Equiv.Perm Ω, g ∈ alternatingGroup Ω ∧
      canonicalLine.map (naturalRepresentation Ω g) = W := by
  have hW : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    contradiction
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨d, rfl⟩ := (vector_cases v).resolve_left hv0
  refine ⟨duadMover d, duadMover_even d, ?_⟩
  rw [canonicalLine, Submodule.map_span, Set.image_singleton,
    pairVector_map, (duadMover_apply d).1, (duadMover_apply d).2]
  exact (eq_span_singleton_of_mem_of_finrank_eq_one hdim hv hv0).symm

private theorem coordinate_ker_eq :
    (coordinate : H →* Equiv.Perm Ω).ker = Atlas.Codes.hexEvenCoordinate.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change (Atlas.Codes.hexEvenCoordinate x).val = (1 : alternatingGroup Ω).val ↔
    Atlas.Codes.hexEvenCoordinate x = 1
  exact Subtype.ext_iff.symm

private theorem coordinate_kernel_card :
    Nat.card (coordinate : H →* Equiv.Perm Ω).ker = 3 := by
  rw [coordinate_ker_eq, Representation.Hexacode.even_kernel_eq_center,
    Representation.Hexacode.even_center_card]

private theorem kernel_cube_eq_one {x : H}
    (hx : x ∈ (coordinate : H →* Equiv.Perm Ω).ker) : x ^ 3 = 1 := by
  let z : (coordinate : H →* Equiv.Perm Ω).ker := ⟨x, hx⟩
  have hz : z ^ 3 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [← coordinate_kernel_card]
    exact orderOf_dvd_natCard z
  exact congrArg Subtype.val hz

private theorem line_generator_fixed
    (W : Submodule (ZMod 2) (natural Ω))
    (hdim : Module.finrank (ZMod 2) W = 1)
    (x : stabilizer W) (w : natural Ω) (hw : w ∈ W) (hw0 : w ≠ 0) :
    naturalRepresentation Ω (coordinate x) w = w := by
  have hmem : naturalRepresentation Ω (coordinate x) w ∈ W :=
    (x.property w).2 hw
  have hspan : W = Submodule.span (ZMod 2) {w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim hw hw0
  have hmem' : naturalRepresentation Ω (coordinate (x : H)) w ∈
      Submodule.span (ZMod 2) {w} := by
    rw [← hspan]
    exact hmem
  obtain ⟨c : ZMod 2, hc⟩ := Submodule.mem_span_singleton.mp hmem'
  fin_cases c
  · exfalso
    apply hw0
    have hz : naturalRepresentation Ω (coordinate x) w = 0 := by
      change (0 : ZMod 2) • w = naturalRepresentation Ω (coordinate x) w at hc
      simpa using hc.symm
    have h := congrArg (naturalRepresentation Ω (coordinate x)⁻¹) hz
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] using h
  · change (1 : ZMod 2) • w = naturalRepresentation Ω (coordinate x) w at hc
    simpa using hc.symm

private theorem canonicalLine_map_cycleA :
    canonicalLine.map (naturalRepresentation Ω cycleA) = canonicalLine := by
  rw [canonicalLine, Submodule.map_span, Set.image_singleton]
  exact congrArg (fun v => Submodule.span (ZMod 2) {v}) cycles_fix.1

private theorem canonicalLine_map_cycleB :
    canonicalLine.map (naturalRepresentation Ω cycleB) = canonicalLine := by
  rw [canonicalLine, Submodule.map_span, Set.image_singleton]
  exact congrArg (fun v => Submodule.span (ZMod 2) {v}) cycles_fix.2

private theorem conjugate_line_map (g h : Equiv.Perm Ω)
    (hline : canonicalLine.map (naturalRepresentation Ω h) = canonicalLine) :
    (canonicalLine.map (naturalRepresentation Ω g)).map
        (naturalRepresentation Ω (g * h * g⁻¹)) =
      canonicalLine.map (naturalRepresentation Ω g) := by
  simp only [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  rw [← Submodule.map_comp (naturalRepresentation Ω g)
      (naturalRepresentation Ω g⁻¹), ← Module.End.mul_eq_comp,
    ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id,
    Submodule.map_id, hline]

private theorem mem_stabilizer_of_map_eq
    (W : Submodule (ZMod 2) (natural Ω)) (x : H)
    (hmap : W.map (naturalRepresentation Ω (coordinate x)) = W) :
    x ∈ stabilizer W := by
  have hmap_inv : W.map (naturalRepresentation Ω (coordinate x)⁻¹) = W := by
    calc
      W.map (naturalRepresentation Ω (coordinate x)⁻¹) =
          (W.map (naturalRepresentation Ω (coordinate x))).map
            (naturalRepresentation Ω (coordinate x)⁻¹) := by rw [hmap]
      _ = W := by
        rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul,
          inv_mul_cancel, map_one, Module.End.one_eq_id, Submodule.map_id]
  change ∀ v, naturalRepresentation Ω (coordinate x) v ∈ W ↔ v ∈ W
  intro v
  constructor
  · intro hv
    rw [← hmap_inv]
    refine ⟨naturalRepresentation Ω (coordinate x) v, hv, ?_⟩
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  · intro hv
    rw [← hmap]
    exact Submodule.mem_map_of_mem hv

private theorem lift_cubic_mem_pointResidual
    (W : Submodule (ZMod 2) (natural Ω))
    (_hdim : Module.finrank (ZMod 2) W = 1)
    (c : Equiv.Perm Ω) (hc : c ∈ alternatingGroup Ω)
    (hmap : W.map (naturalRepresentation Ω c) = W)
    (hcube : c ^ 3 = 1) :
    ∃ x : pointResidual W, coordinate x = c := by
  let ca : alternatingGroup Ω := ⟨c, hc⟩
  obtain ⟨x, hx⟩ := Atlas.Codes.hexEvenCoordinate_surjective ca
  have hxcoord : coordinate x = c := by
    exact congrArg Subtype.val hx
  have hstab : x ∈ stabilizer W := by
    apply mem_stabilizer_of_map_eq W x
    simpa only [hxcoord] using hmap
  have hker : x ^ 3 ∈ (coordinate : H →* Equiv.Perm Ω).ker := by
    rw [MonoidHom.mem_ker, map_pow, hxcoord, hcube]
  have hx9 : x ^ 9 = 1 := by
    simpa only [← pow_mul] using kernel_cube_eq_one hker
  have hx3 : (⟨x, hstab⟩ : stabilizer W) ^ 3 = 1 :=
    Orders.stabilizer_cube_eq_one_of_ninth W (show (⟨x, hstab⟩ : stabilizer W) ^ 9 = 1 by
      exact Subtype.ext hx9)
  have hcop : Nat.Coprime 2 (orderOf (⟨x, hstab⟩ : stabilizer W)) :=
    Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hx3) (by decide)
  exact ⟨⟨x, ⟨⟨x, hstab⟩, mem_pResidual_of_orderOf_coprime hcop, rfl⟩⟩,
    hxcoord⟩

private theorem pointResidual_fixed_iff
    (W : Submodule (ZMod 2) (natural Ω))
    (hdim : Module.finrank (ZMod 2) W = 1) (v : natural Ω) :
    (∀ x : pointResidual W,
      naturalRepresentation Ω (coordinate x) v = v) ↔ v ∈ W := by
  obtain ⟨g, hg, hW⟩ := line_image W hdim
  let cA := g * cycleA * g⁻¹
  let cB := g * cycleB * g⁻¹
  have hcA : cA ∈ alternatingGroup Ω := by
    exact (alternatingGroup Ω).mul_mem
      ((alternatingGroup Ω).mul_mem hg cycles_even.1) ((alternatingGroup Ω).inv_mem hg)
  have hcB : cB ∈ alternatingGroup Ω := by
    exact (alternatingGroup Ω).mul_mem
      ((alternatingGroup Ω).mul_mem hg cycles_even.2) ((alternatingGroup Ω).inv_mem hg)
  have hAline : W.map (naturalRepresentation Ω cA) = W := by
    rw [← hW]
    exact conjugate_line_map g cycleA canonicalLine_map_cycleA
  have hBline : W.map (naturalRepresentation Ω cB) = W := by
    rw [← hW]
    exact conjugate_line_map g cycleB canonicalLine_map_cycleB
  have hA3 : cA ^ 3 = 1 := by
    dsimp [cA]
    calc
      (g * cycleA * g⁻¹) ^ 3 = g * cycleA ^ 3 * g⁻¹ := conj_pow
      _ = 1 := by rw [show cycleA ^ 3 = 1 by decide +kernel]; simp
  have hB3 : cB ^ 3 = 1 := by
    dsimp [cB]
    calc
      (g * cycleB * g⁻¹) ^ 3 = g * cycleB ^ 3 * g⁻¹ := conj_pow
      _ = 1 := by rw [show cycleB ^ 3 = 1 by decide +kernel]; simp
  obtain ⟨xA, hxA⟩ := lift_cubic_mem_pointResidual W hdim cA hcA hAline hA3
  obtain ⟨xB, hxB⟩ := lift_cubic_mem_pointResidual W hdim cB hcB hBline hB3
  constructor
  · intro hv
    have ha : naturalRepresentation Ω cA v = v := by
      simpa only [← hxA] using hv xA
    have hb : naturalRepresentation Ω cB v = v := by
      simpa only [← hxB] using hv xB
    let w := naturalRepresentation Ω g⁻¹ v
    have ha' : naturalRepresentation Ω cycleA w = w := by
      have h := congrArg (naturalRepresentation Ω g⁻¹) ha
      simpa only [w, cA, ← Module.End.mul_apply, ← map_mul, mul_assoc,
        inv_mul_cancel_left] using h
    have hb' : naturalRepresentation Ω cycleB w = w := by
      have h := congrArg (naturalRepresentation Ω g⁻¹) hb
      simpa only [w, cB, ← Module.End.mul_apply, ← map_mul, mul_assoc,
        inv_mul_cancel_left] using h
    have hvw : naturalRepresentation Ω g w = v := by
      simp only [w, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    rcases cycles_fixed w ha' hb' with hzero | hpair
    · rw [hzero, map_zero] at hvw
      rw [← hvw]
      exact W.zero_mem
    · rw [← hvw, hpair, ← hW]
      exact Submodule.mem_map_of_mem
        (Submodule.subset_span (show pairVector 4 5 ∈ {pairVector 4 5} by simp))
  · intro hv x
    let w₀ := naturalRepresentation Ω g (pairVector 4 5)
    have hw₀ : w₀ ∈ W := by
      rw [← hW]
      exact Submodule.mem_map_of_mem (Submodule.subset_span (by simp))
    have hw₀0 : w₀ ≠ 0 := by
      intro h
      apply pairVector45_ne_zero
      have h' := congrArg (naturalRepresentation Ω g⁻¹) h
      rw [map_zero] at h'
      simpa only [w₀, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] using h'
    have hspan : W = Submodule.span (ZMod 2) {w₀} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hdim hw₀ hw₀0
    rw [hspan] at hv
    obtain ⟨c : ZMod 2, hc⟩ := Submodule.mem_span_singleton.mp hv
    fin_cases c
    · change (0 : ZMod 2) • w₀ = v at hc
      have hc0 : v = 0 := by simpa only [zero_smul] using hc.symm
      rw [hc0]
      simp
    · change (1 : ZMod 2) • w₀ = v at hc
      have hc1 : v = w₀ := by simpa only [one_smul] using hc.symm
      rw [hc1]
      have hfix := line_generator_fixed W hdim
        (⟨(x : H), map_subtype_le _ x.property⟩ : stabilizer W) w₀ hw₀ hw₀0
      exact hfix

private theorem pointResidual_normalizer_eq_stabilizer
    (W : Submodule (ZMod 2) (natural Ω))
    (hdim : Module.finrank (ZMod 2) W = 1) :
    normalizer (pointResidual W : Set H) = stabilizer W := by
  have hforward : stabilizer W ≤ normalizer (pointResidual W : Set H) := by
    simpa only [pointResidual, residual] using
      (Subgroup.le_normalizer_embedded_pResidual 2 (stabilizer W))
  have hpreserve (z : H) (hz : z ∈ normalizer (pointResidual W : Set H))
      (v : natural Ω) (hv : v ∈ W) :
      naturalRepresentation Ω (coordinate z) v ∈ W := by
    apply (pointResidual_fixed_iff W hdim _).mp
    intro y
    have hy := y.property
    have hy' : z⁻¹ * (y : H) * z ∈ pointResidual W := by
      have he := (mem_normalizer_iff.mp hz) (z⁻¹ * (y : H) * z)
      apply he.mpr
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hy
    have hfix := (pointResidual_fixed_iff W hdim v).mpr hv
    have hfix' := hfix ⟨z⁻¹ * (y : H) * z, hy'⟩
    have hh := congrArg (naturalRepresentation Ω (coordinate z)) hfix'
    change naturalRepresentation Ω (coordinate y)
        (naturalRepresentation Ω (coordinate z) v) =
      naturalRepresentation Ω (coordinate z) v
    simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left] using hh
  apply le_antisymm
  · intro z hz
    change ∀ v, naturalRepresentation Ω (coordinate z) v ∈ W ↔ v ∈ W
    intro v
    constructor
    · intro hv
      have hz' := (normalizer (pointResidual W : Set H)).inv_mem hz
      have hvinv := hpreserve z⁻¹ hz' (naturalRepresentation Ω (coordinate z) v) hv
      simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] using hvinv
    · exact hpreserve z hz v
  · exact hforward

private theorem center_le_pointResidual
    (W : Submodule (ZMod 2) (natural Ω)) :
    center H ≤ pointResidual W := by
  intro z hz
  have hk : z ∈ (coordinate : H →* Equiv.Perm Ω).ker := by
    rw [coordinate_ker_eq]
    rw [Representation.Hexacode.even_kernel_eq_center]
    exact hz
  have hz3 : z ^ 3 = 1 := kernel_cube_eq_one hk
  have hstab : z ∈ stabilizer W := by
    change ∀ v, naturalRepresentation Ω (coordinate z) v ∈ W ↔ v ∈ W
    intro v
    rw [MonoidHom.mem_ker.mp hk, map_one, Module.End.one_apply]
  refine ⟨⟨z, hstab⟩, ?_, rfl⟩
  exact mem_pResidual_of_orderOf_coprime
    (Nat.Coprime.of_dvd_right
      (orderOf_dvd_of_pow_eq_one (Subtype.ext hz3)) (by decide))

private theorem inner_normalizer_eq
    (W : Submodule (ZMod 2) (natural Ω))
    (hdim : Module.finrank (ZMod 2) W = 1) :
    normalizer ((pointResidual W).map (MulAut.conj : H →* MulAut H) : Set (MulAut H)) ⊓
        MulAut.innerSubgroup H =
      (stabilizer W).map (MulAut.conj : H →* MulAut H) := by
  let I : Subgroup H := pointResidual W
  let K : Subgroup (MulAut H) := I.map (MulAut.conj : H →* MulAut H)
  have hcenter : center H ≤ I := center_le_pointResidual W
  have hmap (z : H) (hz : MulAut.conj z ∈ normalizer (K : Set (MulAut H)))
      (y : H) (hy : y ∈ I) : z * y * z⁻¹ ∈ I := by
    have hky := (mem_normalizer_iff.mp hz) (MulAut.conj y)
    have hk : MulAut.conj (z * y * z⁻¹) ∈ K := by
      simpa only [map_mul, map_inv] using
        hky.mp (mem_map_of_mem (MulAut.conj : H →* MulAut H) hy)
    obtain ⟨i, hi, heq⟩ := hk
    have heq' (t : H) :
        (z * y * z⁻¹) * t * (z * y * z⁻¹)⁻¹ = i * t * i⁻¹ := by
      exact congrArg (fun a : MulAut H => a t) heq.symm
    have hc : (z * y * z⁻¹) * i⁻¹ ∈ center H := by
      rw [mem_center_iff]
      intro t
      have hh := heq' (i⁻¹ * t * i)
      calc
        t * ((z * y * z⁻¹) * i⁻¹) =
            (i * (i⁻¹ * t * i) * i⁻¹) * ((z * y * z⁻¹) * i⁻¹) := by group
        _ = ((z * y * z⁻¹) * (i⁻¹ * t * i) * (z * y * z⁻¹)⁻¹) *
              ((z * y * z⁻¹) * i⁻¹) := by rw [hh]
        _ = ((z * y * z⁻¹) * i⁻¹) * t := by group
    have hcI : (z * y * z⁻¹) * i⁻¹ ∈ I := hcenter hc
    simpa [mul_assoc] using I.mul_mem hcI hi
  have hforward : (stabilizer W).map (MulAut.conj : H →* MulAut H) ≤
      normalizer (K : Set (MulAut H)) ⊓ MulAut.innerSubgroup H := by
    rintro f ⟨z, hz, rfl⟩
    refine ⟨?_, ⟨z, rfl⟩⟩
    exact le_normalizer_map (MulAut.conj : H →* MulAut H)
      (mem_map_of_mem (MulAut.conj : H →* MulAut H)
        ((pointResidual_normalizer_eq_stabilizer W hdim).ge hz))
  apply le_antisymm ?_ hforward
  rintro f ⟨hf, ⟨z, rfl⟩⟩
  have hzN : z ∈ normalizer (I : Set H) := by
    apply mem_normalizer_iff.mpr
    intro y
    constructor
    · exact hmap z hf y
    · have hz' : MulAut.conj z⁻¹ ∈ normalizer (K : Set (MulAut H)) :=
        by
          simpa only [← map_inv] using (normalizer (K : Set (MulAut H))).inv_mem hf
      have h := hmap z⁻¹ hz' (z * y * z⁻¹)
      simpa [mul_assoc] using h
  refine ⟨z, ?_, rfl⟩
  exact (pointResidual_normalizer_eq_stabilizer W hdim).le hzN

/- A two-perfect subgroup of the point-residual normalizer is contained in
the residual itself.  The proof first removes the outer two-group and then
uses the two-group quotient of the point stabilizer. -/
public theorem twoPerfect_normalizer_pointResidual
    (W : Submodule (ZMod 2) (natural Ω))
    (hdim : Module.finrank (ZMod 2) W = 1)
    (D : Subgroup (MulAut H)) (hD : IsPPerfect 2 D)
    (hDnorm : D ≤ normalizer
      ((pointResidual W).map (MulAut.conj : H →* MulAut H) : Set (MulAut H))) :
    D ≤ (pointResidual W).map (MulAut.conj : H →* MulAut H) := by
  let I : Subgroup H := pointResidual W
  let K : Subgroup (MulAut H) := I.map (MulAut.conj : H →* MulAut H)
  let qOuter : MulAut H →* MulAut.Outer H :=
    QuotientGroup.mk' (MulAut.innerSubgroup H)
  have hDinner : D ≤ MulAut.innerSubgroup H := by
    have hf := hD.hom_eq_one_of_isPGroup
      Representation.Hexacode.even_outer_two (qOuter.comp D.subtype)
    intro d hd
    apply (QuotientGroup.eq_one_iff _).mp
    exact congrArg (fun f : D →* MulAut.Outer H => f ⟨d, hd⟩) hf
  let Q : Subgroup (MulAut H) :=
    normalizer (K : Set (MulAut H)) ⊓ MulAut.innerSubgroup H
  have hDQ : D ≤ Q := le_inf hDnorm hDinner
  have hQeq : Q = (stabilizer W).map (MulAut.conj : H →* MulAut H) := by
    exact inner_normalizer_eq W hdim
  have hr := embedded_pResidual_mono 2 hDQ
  rw [(pResidual_eq_top_iff 2 D).mpr hD,
    ← MonoidHom.range_eq_map, range_subtype, hQeq] at hr
  have he := map_embedded_pResidual 2 (stabilizer W) (MulAut.conj : H →* MulAut H)
  exact hr.trans_eq he.symm

/-- The embedded two-residual of the automorphism normalizer is precisely
its actual inner point-residual image. -/
theorem pointResidual_inner_normalizer_residual
    (W : Submodule (ZMod 2) Natural)
    (hdim : Module.finrank (ZMod 2) W = 1) :
    let I := (pointResidual W).map (MulAut.conj : H →* MulAut H)
    let N := normalizer (I : Set (MulAut H))
    (pResidual 2 N).map N.subtype = I := by
  dsimp only
  let I := (pointResidual W).map (MulAut.conj : H →* MulAut H)
  let N := normalizer (I : Set (MulAut H))
  have hI : IsPPerfect 2 I :=
    (isPPerfect_embedded_pResidual 2 (stabilizer W)).of_surjective
      ((MulAut.conj : H →* MulAut H).subgroupMap (pointResidual W))
      ((MulAut.conj : H →* MulAut H).subgroupMap_surjective (pointResidual W))
  apply le_antisymm
  · exact twoPerfect_normalizer_pointResidual W hdim _
      (isPPerfect_embedded_pResidual 2 N) (map_subtype_le _)
  · have hm := embedded_pResidual_mono 2 I.le_normalizer
    rw [(pResidual_eq_top_iff 2 I).mpr hI,
      ← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm

private theorem natural_commuting_eq_one
    (f : MulAut V)
    (hf : ∀ g ∈ alternatingGroup Ω,
      f * naturalMulAction Ω g = naturalMulAction Ω g * f) : f = 1 := by
  let a := AddEquiv.toMultiplicative.symm f
  have h45 : f (Multiplicative.ofAdd (pairVector 4 5)) =
      Multiplicative.ofAdd (pairVector 4 5) := by
    have ha := DFunLike.congr_fun (hf cycleA cycles_even.1)
      (Multiplicative.ofAdd (pairVector 4 5))
    have hb := DFunLike.congr_fun (hf cycleB cycles_even.2)
      (Multiplicative.ofAdd (pairVector 4 5))
    change f (naturalMulAction Ω cycleA (Multiplicative.ofAdd (pairVector 4 5))) =
      naturalMulAction Ω cycleA (f (Multiplicative.ofAdd (pairVector 4 5))) at ha
    change f (naturalMulAction Ω cycleB (Multiplicative.ofAdd (pairVector 4 5))) =
      naturalMulAction Ω cycleB (f (Multiplicative.ofAdd (pairVector 4 5))) at hb
    have ha' : naturalRepresentation Ω cycleA (a (pairVector 4 5)) =
        a (pairVector 4 5) := by
      simpa [a, naturalMulAction_apply, cycles_fix.1] using
        (congrArg Multiplicative.toAdd ha).symm
    have hb' : naturalRepresentation Ω cycleB (a (pairVector 4 5)) =
        a (pairVector 4 5) := by
      simpa [a, naturalMulAction_apply, cycles_fix.2] using
        (congrArg Multiplicative.toAdd hb).symm
    rcases cycles_fixed _ ha' hb' with h | h
    · exact False.elim (pairVector45_ne_zero (by
        apply a.injective
        simpa using h))
    · simpa [a] using congrArg Multiplicative.ofAdd h
  have hp (d : Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.Duad) :
      f (Multiplicative.ofAdd (duadVector d)) =
      Multiplicative.ofAdd (duadVector d) := by
    let g := duadMover d
    have hg := DFunLike.congr_fun (hf g (duadMover_even d))
      (Multiplicative.ofAdd (pairVector 4 5))
    have hcomm : f (naturalMulAction Ω g (Multiplicative.ofAdd (pairVector 4 5))) =
        naturalMulAction Ω g (f (Multiplicative.ofAdd (pairVector 4 5))) := by
      change f (naturalMulAction Ω g (Multiplicative.ofAdd (pairVector 4 5))) =
        naturalMulAction Ω g (f (Multiplicative.ofAdd (pairVector 4 5))) at hg
      exact hg
    rw [naturalMulAction_apply, naturalMulAction_apply, h45] at hcomm
    change f (Multiplicative.ofAdd (naturalRepresentation Ω g (pairVector 4 5))) =
      Multiplicative.ofAdd (naturalRepresentation Ω g (pairVector 4 5)) at hcomm
    have hd := duadMover_apply d
    rw [pairVector_map, hd.1, hd.2] at hcomm
    exact hcomm
  apply MulEquiv.ext
  intro v
  obtain rfl | ⟨d, rfl⟩ := vector_cases v.toAdd
  · exact map_one f
  · exact hp d

/-- The centralizer of the natural alternating-six action is trivial. -/
public theorem naturalAlternating_centralizer :
    Subgroup.centralizer
      ((alternatingGroup Ω).map (naturalMulAction Ω) :
        Set (MulAut (Multiplicative (natural Ω)))) = ⊥ := by
  apply le_antisymm
  · intro f hf
    exact (Subgroup.mem_bot).2 (natural_commuting_eq_one f (by
      intro g hg
      exact (mem_centralizer_iff.mp hf (naturalMulAction Ω g)
        (mem_map_of_mem (naturalMulAction Ω) hg)).symm))
  · exact bot_le

end Representation.Hexacode.CubicLocalModel
