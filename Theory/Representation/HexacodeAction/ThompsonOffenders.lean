module

public import Theory.Representation.HexacodeAction.Field
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.Operators
public import Theory.Representation.BinaryOffender.Basic
public import Theory.Representation.BinaryOffender.Stability
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.FiniteFieldSemilinearDisplacement
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.Representation.HexacodeAction.PairCore
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Thompson offenders in the hexacode action

This is the concrete finite calculation used by the covered-six Thompson
argument. The coordinate projection embeds every elementary two-subgroup of
the even cover in `A₆`, and the quadratic field structure then forces every binary offender in
the even cover to have rank two and a four-dimensional fixed space.  A direct
determinant calculation identifies the subgroup with the pointwise kernel of
that fixed space.  Odd involutions are semilinear and cannot occur in a best
offender. The eight-word Sylow calculation gives uniqueness inside a
common two-subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.4.2(8), printed p.86; K.1.3, printed p.453;
and the covered-six paragraph of 13.6.22, printed p.932. The F₄-line is
projective: its vector dimension is two and its binary dimension is four.

The Sylow, even-kernel and outer-exclusion proofs are adapted from the
existing `CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders`
modules, preserving those source APIs. The code, monomial lifts and field
coordinates are the licensed ATLAS constructions by Gerald Höhn and
contributors; see `LICENSES/ATLAS.txt` and the original attributions under
`Theory.AtlasPort.OtherSporadic.Codes`. No CFSG module is imported here.
-/

public section

open Atlas.Codes Subgroup Representation Representation.BinaryOffender

namespace Representation.Hexacode.ThompsonOffenders

/-! ## The concrete even Sylow subgroup -/

namespace SylowModel

abbrev Bits := Fin 2 × Fin 2 × Fin 2
abbrev PairBits := Fin 2 × Fin 2

def z : HexEvenAutomorphisms := ⟨hexLift 0 * hexLift 2, by simp⟩
def t : HexEvenAutomorphisms := ⟨hexLift 0 * hexLift 4, by simp⟩
def s : HexEvenAutomorphisms := ⟨hexLift 1 * hexLift 0 * hexLift 2 * hexLift 1, by simp⟩

def word (p : Bits) : HexEvenAutomorphisms :=
  z ^ p.1.val * s ^ p.2.1.val * t ^ p.2.2.val

def mulBits (p q : Bits) : Bits :=
  (p.1 + q.1 + p.2.2 * q.2.1, p.2.1 + q.2.1, p.2.2 + q.2.2)
def invBits (p : Bits) : Bits := (p.1 + p.2.1 * p.2.2, p.2.1, p.2.2)

set_option maxRecDepth 4096 in
theorem word_mul (p q : Bits) : word (mulBits p q) = word p * word q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply _root_.Equiv.ext; intro i; revert p q i; decide +kernel
  · funext i; apply LinearEquiv.ext; intro u; revert p q i u; decide +kernel

set_option maxRecDepth 4096 in
theorem word_inv (p : Bits) : word (invBits p) = (word p)⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  apply Monomial.ext
  · apply _root_.Equiv.ext; intro i; revert p i; decide +kernel
  · funext i; apply LinearEquiv.ext; intro u; revert p i u; decide +kernel

theorem word_injective : Function.Injective word := by
  intro p q he
  have hc := congrArg (fun g : HexEvenAutomorphisms => hexCoordinateSixHom g.val) he
  exact (by decide +kernel : ∀ p q : Bits,
    hexCoordinateSixHom (word p).val = hexCoordinateSixHom (word q).val → p = q) p q hc

private def rangeSubgroup {I : Type*} (f : I → HexEvenAutomorphisms)
    (ho : ∃ i, f i = 1) (hm : ∀ i j, ∃ k, f k = f i * f j)
    (hi : ∀ i, ∃ j, f j = (f i)⁻¹) : Subgroup HexEvenAutomorphisms where
  carrier := Set.range f
  one_mem' := ho
  mul_mem' := by rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩; exact hm i j
  inv_mem' := by rintro _ ⟨i, rfl⟩; exact hi i

def sylowGroup : Subgroup HexEvenAutomorphisms := rangeSubgroup word
  ⟨(0, 0, 0), by simp [word]⟩ (fun p q => ⟨mulBits p q, word_mul p q⟩)
  (fun p => ⟨invBits p, word_inv p⟩)

def lineWord (p : PairBits) := word (p.1, p.2, 0)
def planeWord (p : PairBits) := word (p.1, 0, p.2)

def lineGroup : Subgroup HexEvenAutomorphisms := rangeSubgroup lineWord
  ⟨(0, 0), by simp [lineWord, word]⟩
  (fun p q => ⟨(p.1 + q.1, p.2 + q.2), by
    simpa [lineWord, mulBits] using word_mul (p.1, p.2, 0) (q.1, q.2, 0)⟩)
  (fun p => ⟨p, by simpa [lineWord, invBits] using word_inv (p.1, p.2, 0)⟩)

def planeGroup : Subgroup HexEvenAutomorphisms := rangeSubgroup planeWord
  ⟨(0, 0), by simp [planeWord, word]⟩
  (fun p q => ⟨(p.1 + q.1, p.2 + q.2), by
    simpa [planeWord, mulBits] using word_mul (p.1, 0, p.2) (q.1, 0, q.2)⟩)
  (fun p => ⟨p, by simpa [planeWord, invBits] using word_inv (p.1, 0, p.2)⟩)

theorem sylowGroup_card : Nat.card sylowGroup = 8 := by
  change Nat.card (Set.range word) = 8
  rw [Nat.card_range_of_injective word_injective]
  simp [Bits]

theorem lineGroup_card : Nat.card lineGroup = 4 := by
  change Nat.card (Set.range lineWord) = 4
  have hi : Function.Injective lineWord := by
    intro p q h
    have hh := word_injective h
    exact Prod.ext (congrArg (fun p : Bits => p.1) hh)
      (congrArg (fun p : Bits => p.2.1) hh)
  rw [Nat.card_range_of_injective hi]
  simp [PairBits]

theorem planeGroup_card : Nat.card planeGroup = 4 := by
  change Nat.card (Set.range planeWord) = 4
  have hi : Function.Injective planeWord := by
    intro p q h
    have hh := word_injective h
    exact Prod.ext (congrArg (fun p : Bits => p.1) hh)
      (congrArg (fun p : Bits => p.2.2) hh)
  rw [Nat.card_range_of_injective hi]
  simp [PairBits]

private theorem elementary_of_inv (A : Subgroup HexEvenAutomorphisms)
    (h : ∀ x ∈ A, x⁻¹ = x) : IsElementaryAbelian 2 A := by
  have hi (x : A) : x⁻¹ = x := Subtype.ext (h x x.property)
  exact {
    toIsMulCommutative := ⟨⟨fun x y => by
      calc x * y = (x * y)⁻¹ := (hi _).symm
           _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
           _ = y * x := by rw [hi, hi]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun g => by
        calc g ^ 2 = g * g := pow_two g
             _ = g⁻¹ * g := congrArg (fun a => a * g) (hi g).symm
             _ = 1 := inv_mul_cancel g) }

theorem lineGroup_elementary : IsElementaryAbelian 2 lineGroup := by
  apply elementary_of_inv
  rintro _ ⟨p, rfl⟩
  simpa [lineWord, invBits] using (word_inv (p.1, p.2, 0)).symm

theorem planeGroup_elementary : IsElementaryAbelian 2 planeGroup := by
  apply elementary_of_inv
  rintro _ ⟨p, rfl⟩
  simpa [planeWord, invBits] using (word_inv (p.1, 0, p.2)).symm

theorem lineGroup_le_sylow : lineGroup ≤ sylowGroup := by
  rintro _ ⟨p, rfl⟩
  exact ⟨(p.1, p.2, 0), rfl⟩

theorem planeGroup_le_sylow : planeGroup ≤ sylowGroup := by
  rintro _ ⟨p, rfl⟩
  exact ⟨(p.1, 0, p.2), rfl⟩

theorem word_mem_line (p : Bits) : word p ∈ lineGroup ↔ p.2.2 = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact (congrArg (fun p : Bits => p.2.2) (word_injective hq)).symm
  · intro h
    refine ⟨(p.1, p.2.1), ?_⟩
    change word (p.1, p.2.1, 0) = word (p.1, p.2.1, p.2.2)
    rw [h]

theorem word_mem_plane (p : Bits) : word p ∈ planeGroup ↔ p.2.1 = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact (congrArg (fun p : Bits => p.2.1) (word_injective hq)).symm
  · intro h
    refine ⟨(p.1, p.2.2), ?_⟩
    change word (p.1, 0, p.2.2) = word (p.1, p.2.1, p.2.2)
    rw [h]

private theorem compatible (p q : Bits)
    (hp : word p ^ 2 = 1) (hq : word q ^ 2 = 1)
    (hpq : (word p * word q) ^ 2 = 1) : p.2.1 = 0 ∨ q.2.2 = 0 := by
  let f := hexCoordinateSixHom.comp hexSign.ker.subtype
  have h (g : HexEvenAutomorphisms) (hg : g ^ 2 = 1) : f g ^ 2 = 1 := by
    rw [← map_pow, hg, map_one]
  have hh := h (word p * word q) hpq
  rw [map_mul] at hh
  exact (by decide +kernel : ∀ p q : Bits,
    f (word p) ^ 2 = 1 → f (word q) ^ 2 = 1 →
    (f (word p) * f (word q)) ^ 2 = 1 → p.2.1 = 0 ∨ q.2.2 = 0)
      p q (h _ hp) (h _ hq) hh

theorem elementary_exhaustion (A : Subgroup HexEvenAutomorphisms)
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ sylowGroup) :
    A ≤ lineGroup ∨ A ≤ planeGroup := by
  classical
  let _ := hA
  by_cases h : A ≤ planeGroup
  · exact Or.inr h
  · left
    obtain ⟨x, hx, hxp⟩ := Set.not_subset.mp h
    obtain ⟨p, rfl⟩ := hAT hx
    have hp : p.2.1 ≠ 0 := fun hh => hxp ((word_mem_plane p).mpr hh)
    intro y hy
    obtain ⟨q, rfl⟩ := hAT hy
    apply (word_mem_line q).mpr
    exact (compatible p q
      (elemPow_eq_one_of_isElementaryAbelian _ hx)
      (elemPow_eq_one_of_isElementaryAbelian _ hy)
      (elemPow_eq_one_of_isElementaryAbelian _ (A.mul_mem hx hy))).resolve_left hp

theorem fourGroup_exhaustion (A : Subgroup HexEvenAutomorphisms)
    (hA : IsElementaryAbelian 2 A) (hAT : A ≤ sylowGroup) (hc : Nat.card A = 4) :
    A = lineGroup ∨ A = planeGroup := by
  rcases elementary_exhaustion A hA hAT with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hc, lineGroup_card]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hc, planeGroup_card]))

end SylowModel

@[expose] noncomputable def standardSylow : Sylow 2 HexEvenAutomorphisms :=
  (IsPGroup.of_card (show Nat.card SylowModel.sylowGroup = 2 ^ 3 by
      rw [SylowModel.sylowGroup_card]; decide)).toSylow (by
    have h := SylowModel.sylowGroup.card_mul_index
    rw [SylowModel.sylowGroup_card, hexEven_card] at h
    have hi : SylowModel.sylowGroup.index = 135 := by omega
    rw [hi]; decide)

@[simp] theorem standardSylow_coe :
    (standardSylow : Subgroup HexEvenAutomorphisms) = SylowModel.sylowGroup := rfl

private def parameterFixed (u : HexEvenAutomorphisms) (p : Fin 3 → K) : Prop :=
  Monomial.act SylowModel.z.val.val (systematicEncoder p) = systematicEncoder p ∧
    Monomial.act u.val.val (systematicEncoder p) = systematicEncoder p

private instance (u : HexEvenAutomorphisms) (p : Fin 3 → K) : Decidable (parameterFixed u p) :=
  inferInstanceAs (Decidable
    (Monomial.act SylowModel.z.val.val (systematicEncoder p) = systematicEncoder p ∧
      Monomial.act u.val.val (systematicEncoder p) = systematicEncoder p))

private noncomputable def fixedEquiv (u : HexEvenAutomorphisms)
    (A : Subgroup HexEvenAutomorphisms)
    (h : ∀ v, v ∈ fixedSpace evenAction A ↔
      evenAction SylowModel.z v = v ∧ evenAction u v = v) :
    fixedSpace evenAction A ≃ {p : Fin 3 → K // parameterFixed u p} where
  toFun v := ⟨hexProjection firstThree v.val, by
    obtain ⟨hz, hu⟩ := (h v.val).mp v.property
    change Monomial.act SylowModel.z.val.val (systematicEncoder (hexProjection firstThree v.val)) = _ ∧
      Monomial.act u.val.val (systematicEncoder (hexProjection firstThree v.val)) = _
    rw [systematic_reconstruct]
    exact ⟨congrArg Subtype.val hz, congrArg Subtype.val hu⟩⟩
  invFun p := ⟨⟨systematicEncoder p, systematic_mem p⟩, (h _).mpr
    ⟨Subtype.ext p.property.1, Subtype.ext p.property.2⟩⟩
  left_inv v := Subtype.ext (Subtype.ext (systematic_reconstruct v.val))
  right_inv p := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl

private theorem mem_fixedSpace_line (v : hexacode) :
    v ∈ fixedSpace evenAction SylowModel.lineGroup ↔
      evenAction SylowModel.z v = v ∧ evenAction SylowModel.s v = v := by
  constructor
  · intro hv
    constructor
    · simpa [SylowModel.lineWord, SylowModel.word] using hv
        ⟨SylowModel.lineWord (1, 0), ⟨(1, 0), rfl⟩⟩
    · simpa [SylowModel.lineWord, SylowModel.word] using hv
        ⟨SylowModel.lineWord (0, 1), ⟨(0, 1), rfl⟩⟩
  · rintro ⟨hz, hs⟩ ⟨g, ⟨a, b⟩, rfl⟩
    fin_cases a <;> fin_cases b <;>
      simp [SylowModel.lineWord, SylowModel.word, map_mul, Module.End.mul_apply, hz, hs]

private theorem mem_fixedSpace_plane (v : hexacode) :
    v ∈ fixedSpace evenAction SylowModel.planeGroup ↔
      evenAction SylowModel.z v = v ∧ evenAction SylowModel.t v = v := by
  constructor
  · intro hv
    constructor
    · simpa [SylowModel.planeWord, SylowModel.word] using hv
        ⟨SylowModel.planeWord (1, 0), ⟨(1, 0), rfl⟩⟩
    · simpa [SylowModel.planeWord, SylowModel.word] using hv
        ⟨SylowModel.planeWord (0, 1), ⟨(0, 1), rfl⟩⟩
  · rintro ⟨hz, ht⟩ ⟨g, ⟨a, b⟩, rfl⟩
    fin_cases a <;> fin_cases b <;>
      simp [SylowModel.planeWord, SylowModel.word, map_mul, Module.End.mul_apply, hz, ht]

theorem lineFixed_finrank :
    Module.finrank (ZMod 2) (fixedSpace evenAction SylowModel.lineGroup) = 2 := by
  have hcard : Nat.card (fixedSpace evenAction SylowModel.lineGroup) = 4 := by
    rw [Nat.card_congr (fixedEquiv SylowModel.s SylowModel.lineGroup mem_fixedSpace_line)]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace evenAction SylowModel.lineGroup)
  rw [Nat.card_zmod, hcard] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) h.symm

theorem planeFixed_finrank :
    Module.finrank (ZMod 2) (fixedSpace evenAction SylowModel.planeGroup) = 4 := by
  have hcard : Nat.card (fixedSpace evenAction SylowModel.planeGroup) = 16 := by
    rw [Nat.card_congr (fixedEquiv SylowModel.t SylowModel.planeGroup mem_fixedSpace_plane)]
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace evenAction SylowModel.planeGroup)
  rw [Nat.card_zmod, hcard] at h
  exact Nat.pow_right_injective (by decide : 1 < 2) h.symm

/-! ## Even offenders -/

private def letters : Fin 6 ↪ Fin 7 :=
  ⟨Fin.castSucc, Fin.castSucc_injective 6⟩

private noncomputable def permutation : HexEvenAutomorphisms →* Equiv.Perm (Fin 7) :=
  (Equiv.Perm.viaEmbeddingHom letters).comp
    (hexCoordinateSixHom.comp hexSign.ker.subtype)

theorem elementary_card_le_four (A : Subgroup HexEvenAutomorphisms)
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 4 := by
  let _ := hA
  have hf : Function.Injective (permutation.comp A.subtype) := by
    have h := injective_comp_subtype_of_coprime_ker hexEvenCoordinate
      (by rw [hexEven_kernel_card]; decide : Nat.Coprime 2 (Nat.card hexEvenCoordinate.ker))
      A (IsElementaryAbelian.isPGroup 2 A)
    intro a b he
    apply h
    apply Subtype.ext
    exact Equiv.Perm.viaEmbeddingHom_injective letters he
  have he : A.map permutation ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨g, _, rfl⟩
    change Equiv.Perm.sign (Equiv.Perm.viaEmbeddingHom letters
      (hexCoordinateSixHom g.val)) = 1
    rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding,
      Equiv.Perm.sign_extendDomain]
    exact g.property
  have hc :=
    Representation.AlternatingSevenConjugatePair.ElementaryGeometry.elementary_even_card_le
      (IsElementaryAbelian.map permutation (A := A)) he
  have hcard : Nat.card (A.map permutation) = Nat.card A := by
    conv_lhs => rw [← A.range_subtype, ← MonoidHom.range_comp]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  rwa [hcard] at hc

theorem elementary_rank_le_two (A : Subgroup HexEvenAutomorphisms)
    (hA : IsElementaryTwo A) : rank A ≤ 2 := by
  have h := elementary_card_le_four A hA.2
  rw [hA.card_eq_two_pow_rank] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h

theorem fixedSpace_scalar_stable (A : Subgroup HexEvenAutomorphisms) :
    hexZ ∈ subspaceStabilizer action (fixedSpace evenAction A) := by
  intro v
  constructor
  · intro hv a
    apply (hexAction hexZ).injective
    exact (action_commutes_scalar a.val.val a.val.property v).symm.trans (hv a)
  · intro hv a
    change action a.val.val (action hexZ v) = action hexZ v
    rw [scalar_eq_omega_smul, action_even_smul _ a.val.property]
    rw [show action a.val.val v = v from hv a]

theorem fixedCodim_ge_two (A : Subgroup HexEvenAutomorphisms) (hA : A ≠ ⊥) :
    2 ≤ fixedCodim evenAction A := by
  have hd := scalarSubmodule_finrank _ (fixedSpace_scalar_stable A)
  have hs := fixedCodim_add_finrank evenAction A
  rw [hexacode_finrank] at hs
  have hp := fixedCodim_pos_of_faithful evenAction
    (fun _ _ h => Subtype.ext (action_injective h)) hA
  change 2 * Module.finrank F (scalarSubmodule
    (fixedSpace evenAction A) (fixedSpace_scalar_stable A)) =
      Module.finrank (ZMod 2) (fixedSpace evenAction A) at hd
  omega

theorem no_strong : ¬ IsStrongFFModule evenAction := by
  rintro ⟨A, hA, hlt⟩
  have := fixedCodim_ge_two A hA.1
  have := elementary_rank_le_two A hA
  omega

theorem offender_dimensions (A : Subgroup HexEvenAutomorphisms)
    (hA : IsOffender evenAction A) :
    rank A = 2 ∧ Nat.card A = 4 ∧ fixedCodim evenAction A = 2 ∧
      Module.finrank (ZMod 2) (fixedSpace evenAction A) = 4 := by
  have hlo := fixedCodim_ge_two A hA.1.1
  have hhi := elementary_rank_le_two A hA.1
  have hoff := hA.2
  have hr : rank A = 2 := by omega
  have hc : Nat.card A = 4 := by rw [hA.1.card_eq_two_pow_rank, hr]; norm_num
  have hs := fixedCodim_add_finrank evenAction A
  rw [hexacode_finrank] at hs
  exact ⟨hr, hc, by omega, by omega⟩

theorem bestOffender_dimensions (A : Subgroup HexEvenAutomorphisms)
    (hA : IsBestOffender evenAction A) :
    rank A = 2 ∧ Nat.card A = 4 ∧ fixedCodim evenAction A = 2 ∧
      Module.finrank (ZMod 2) (fixedSpace evenAction A) = 4 :=
  offender_dimensions A (hA.isOffender _)

private theorem binary_add_self (v : hexacode) : v + v = 0 := by
  have h : (2 : ZMod 2) • v = 0 := by
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  simpa only [two_smul] using h

theorem plane_displacement (U : Submodule (ZMod 2) hexacode)
    (hs : hexZ ∈ subspaceStabilizer action U)
    (hd : Module.finrank (ZMod 2) U = 4)
    (g : HexEvenAutomorphisms) (hg : ∀ v ∈ U, evenAction g v = v)
    (v : hexacode) : evenAction g v - v ∈ U := by
  let W := scalarSubmodule U hs
  let _ : Module.Free F W := Module.Free.of_divisionRing F W
  let _ : Module.Free F (hexacode ⧸ W) := Module.Free.of_divisionRing F (hexacode ⧸ W)
  let f := (evenFieldAction g).toLinearMap
  have hW : W ≤ W.comap f := by
    intro w hw
    change f w ∈ W
    rw [show f w = w from hg w hw]
    exact hw
  have hr : f.restrict hW = LinearMap.id := by
    apply LinearMap.ext
    intro w
    exact Subtype.ext (hg w w.property)
  have hdW : Module.finrank F W = 2 := by
    have h := scalarSubmodule_finrank U hs
    change 2 * Module.finrank F W = Module.finrank (ZMod 2) U at h
    rw [hd] at h
    omega
  have hdQ : Module.finrank F (hexacode ⧸ W) = 1 := by
    have h := W.finrank_quotient_add_finrank
    rw [field_finrank, hdW] at h
    omega
  have hdg : LinearMap.det f = 1 := by
    dsimp only [f]
    rw [← LinearEquiv.coe_det, evenFieldAction_det]
    rfl
  have he := LinearMap.det_eq_det_mul_det W f hW
  rw [hdg, hr, LinearMap.det_id, one_mul] at he
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
    hdQ (W.mapQ W f hW)
  rw [hc, LinearMap.det_smul, LinearMap.det_id, hdQ, pow_one, mul_one] at he
  have hq : W.mapQ W f hW = LinearMap.id := by rw [hc, ← he, one_smul]
  exact (Submodule.Quotient.eq W).mp
    (LinearMap.congr_fun hq (Submodule.Quotient.mk v))

theorem planeKernel_quadratic (U : Submodule (ZMod 2) hexacode)
    (hs : hexZ ∈ subspaceStabilizer action U)
    (hd : Module.finrank (ZMod 2) U = 4) :
    IsQuadratic evenAction (subspaceKernel evenAction U ⊤) := by
  intro a ha b hb v
  exact ha.2 _ (plane_displacement U hs hd b hb.2 v)

theorem planeKernel_elementary (U : Submodule (ZMod 2) hexacode)
    (hs : hexZ ∈ subspaceStabilizer action U)
    (hd : Module.finrank (ZMod 2) U = 4) :
    IsElementaryAbelian 2 (subspaceKernel evenAction U ⊤) := by
  let K := subspaceKernel evenAction U ⊤
  have hq := planeKernel_quadratic U hs hd
  have hsq (g : K) : g * g = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply action_injective
    apply LinearMap.ext
    intro v
    change evenAction g.val (evenAction g.val v) = v
    have h := hq g.val g.property g.val g.property v
    rw [map_sub] at h
    have hz := binary_add_self (evenAction g.val v)
    have hzv := binary_add_self v
    apply sub_eq_zero.mp
    calc
      _ = (evenAction g.val (evenAction g.val v) - evenAction g.val v) -
          (evenAction g.val v - v) +
          (evenAction g.val v + evenAction g.val v) - (v + v) := by abel
      _ = 0 := by rw [h, sub_self, hz, hzv]; simp
  have hi (g : K) : g⁻¹ = g := inv_eq_of_mul_eq_one_left (hsq g)
  exact {
    toIsMulCommutative := ⟨⟨fun x y => by
      calc x * y = (x * y)⁻¹ := (hi _).symm
           _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
           _ = y * x := by rw [hi, hi]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun g => by simpa only [pow_two] using hsq g) }

theorem planeKernel_card_le_four (U : Submodule (ZMod 2) hexacode)
    (hs : hexZ ∈ subspaceStabilizer action U)
    (hd : Module.finrank (ZMod 2) U = 4) :
    Nat.card (subspaceKernel evenAction U ⊤) ≤ 4 :=
  elementary_card_le_four _ (planeKernel_elementary U hs hd)

theorem offender_eq_kernel (A : Subgroup HexEvenAutomorphisms)
    (hA : IsOffender evenAction A) :
    A = subspaceKernel evenAction (fixedSpace evenAction A) ⊤ := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro a ha
    exact ⟨mem_top _, fun v hv => hv ⟨a, ha⟩⟩
  · rw [(offender_dimensions A hA).2.1]
    exact planeKernel_card_le_four _ (fixedSpace_scalar_stable A)
      (offender_dimensions A hA).2.2.2

theorem bestOffender_eq_kernel (A : Subgroup HexEvenAutomorphisms)
    (hA : IsBestOffender evenAction A) :
    A = subspaceKernel evenAction (fixedSpace evenAction A) ⊤ :=
  offender_eq_kernel A (hA.isOffender _)

/-! ## The odd coset -/

private theorem fixedCodim_mono
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G} (hBA : B ≤ A) :
    fixedCodim ρ B ≤ fixedCodim ρ A := by
  have hdim := Submodule.finrank_mono (fixedSpace_antitone ρ hBA)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  omega

private theorem fixedSpace_eq_of_fixedCodim_eq
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {A B : Subgroup G} (hBA : B ≤ A)
    (hcodim : fixedCodim ρ A = fixedCodim ρ B) :
    fixedSpace ρ A = fixedSpace ρ B := by
  apply Submodule.eq_of_le_of_finrank_eq (fixedSpace_antitone ρ hBA)
  have hA := fixedCodim_add_finrank ρ A
  have hB := fixedCodim_add_finrank ρ B
  omega

private noncomputable def sixToSeven : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 7) :=
  Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb

private theorem sixToSeven_injective : Function.Injective sixToSeven :=
  Equiv.Perm.viaEmbeddingHom_injective Fin.castSuccEmb

private theorem full_rank_le_three (A : Subgroup HexAutomorphisms)
    (hA : IsElementaryTwo A) : rank A ≤ 3 := by
  let f : HexAutomorphisms →* Equiv.Perm (Fin 6) := hexCoordinateSixHom
  let E : Subgroup (Equiv.Perm (Fin 6)) := A.map f
  have hE : IsElementaryAbelian 2 E :=
    @IsElementaryAbelian.map 2 (by infer_instance) HexAutomorphisms
      (Equiv.Perm (Fin 6)) inferInstance inferInstance A hA.2 f
  let fA0 : A →* Equiv.Perm (Fin 6) := f.comp A.subtype
  let fA : A →* E := fA0.codRestrict E (by
    intro x
    exact ⟨x, x.property, rfl⟩)
  have hfA : Function.Injective fA := by
    intro x y h
    apply Subtype.ext
    exact congrArg Subtype.val
      (coordinate_injective_on_two_subgroup A hA.2.isPGroup
        (congrArg Subtype.val h))
  have hfAsurj : Function.Surjective fA := by
    intro y
    rcases y.property with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hxy
  have hcardE : Nat.card E = Nat.card A := by
    exact (Nat.card_congr (MulEquiv.ofBijective fA ⟨hfA, hfAsurj⟩).toEquiv).symm
  let E' : Subgroup (Equiv.Perm (Fin 7)) := E.map sixToSeven
  have hE' : IsElementaryAbelian 2 E' :=
    @IsElementaryAbelian.map 2 (by infer_instance) (Equiv.Perm (Fin 6))
      (Equiv.Perm (Fin 7)) inferInstance inferInstance E hE sixToSeven
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective sixToSeven_injective
  have hbound : Nat.card E' ≤ 8 :=
    Representation.AlternatingSevenConjugatePair.ElementaryGeometry.elementary_card_le hE'
  have hpow : Nat.card A = 2 ^ rank A := hA.card_eq_two_pow_rank
  rw [hcardE', hcardE] at hbound
  rw [hpow] at hbound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound

private theorem frobenius_order : orderOf SL2FourNatural.fieldFrobenius = 2 := by
  have hs : SL2FourNatural.fieldFrobenius ^ 2 = 1 := by
    apply RingEquiv.ext
    intro c
    exact SL2FourNatural.fieldFrobenius_involutive c
  exact orderOf_eq_prime hs fieldFrobenius_ne_id

/-- An odd involution is a field involution and fixes exactly three binary dimensions. -/
theorem odd_involution_fixedCodim (g : HexAutomorphisms)
    (hg : hexSign g = -1) (h2 : g ^ 2 = 1) :
    fixedCodim action (zpowers g) = 3 := by
  have hn : g ≠ 1 := by
    intro h
    have he := hg
    rw [h] at he
    simp at he
  have h := Representation.FiniteFieldSemilinearDisplacement.fixedCodim_formula
    action (p := 2) (by decide) g (orderOf_eq_prime h2 hn)
    SL2FourNatural.fieldFrobenius frobenius_order (action_odd_smul g hg)
  have hF : Module.finrank (ZMod 2) F = 2 := QuadraticAlgebra.finrank_eq_two _ _
  rw [field_finrank, hF] at h
  omega

theorem bestOffender_le_even (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender action A) : A ≤ hexSign.ker := by
  by_contra hle
  have hexists : ∃ g, g ∈ A ∧ g ∉ hexSign.ker := by
    by_contra h
    apply hle
    intro g hgA
    by_contra hgn
    exact h ⟨g, hgA, hgn⟩
  obtain ⟨g, hgA, hgne⟩ := hexists
  change hexSign g ≠ 1 at hgne
  have hgod : hexSign g = -1 := by
    rcases Int.units_eq_one_or (hexSign g) with h | h
    · exact (hgne h).elim
    · exact h
  have hg1 : g ≠ 1 := by
    intro hg
    rw [hg] at hgod
    simp at hgod
  have hgpow : g ^ 2 = 1 :=
    @elemPow_eq_one_of_isElementaryAbelian 2 HexAutomorphisms inferInstance A hA.1.2 g hgA
  have hgord : orderOf g = 2 := orderOf_eq_prime hgpow hg1
  have hσord := frobenius_order
  have hsemi (c : F) (v : hexacode) :
      action g (c • v) = SL2FourNatural.fieldFrobenius c • action g v :=
    action_odd_smul g hgod c v
  have hfixedg : fixedCodim action (Subgroup.zpowers g) = 3 :=
    odd_involution_fixedCodim g hgod hgpow
  have hrank : rank A = 3 := by
    have hupper : fixedCodim action A ≤ rank A := hA.isOffender action |>.2
    have hlow : 3 ≤ fixedCodim action A := by
      calc
        3 = fixedCodim action (Subgroup.zpowers g) := hfixedg.symm
        _ ≤ fixedCodim action A := fixedCodim_mono action (Subgroup.zpowers_le.mpr hgA)
    exact le_antisymm (full_rank_le_three A hA.1) (by omega)
  have hcodimA : fixedCodim action A = 3 := by
    have hupper : fixedCodim action A ≤ rank A := hA.isOffender action |>.2
    have hlow : 3 ≤ fixedCodim action A := by
      calc
        3 = fixedCodim action (Subgroup.zpowers g) := hfixedg.symm
        _ ≤ fixedCodim action A := fixedCodim_mono action (Subgroup.zpowers_le.mpr hgA)
    omega
  have hfixed : fixedSpace action A = fixedSpace action (Subgroup.zpowers g) :=
    fixedSpace_eq_of_fixedCodim_eq action (Subgroup.zpowers_le.mpr hgA)
      (hcodimA.trans hfixedg.symm)
  have hnotle : ¬ A ≤ Subgroup.zpowers g := by
    intro hleA
    have hc := Subgroup.card_le_of_le hleA
    rw [hA.1.card_eq_two_pow_rank, hrank, Nat.card_zpowers, hgord] at hc
    norm_num at hc
  have hexistsb : ∃ b, b ∈ A ∧ b ∉ Subgroup.zpowers g := by
    by_contra h
    apply hnotle
    intro b hbA
    by_contra hbnot
    exact h ⟨b, hbA, hbnot⟩
  obtain ⟨b, hbA, hbnot⟩ := hexistsb
  have hb1 : b ≠ 1 := by
    intro hb
    apply hbnot
    rw [hb]
    exact Subgroup.one_mem (Subgroup.zpowers g)
  have hginv : g⁻¹ = g := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using hgpow
  have heven : ∃ a ∈ A, a ≠ 1 ∧ hexSign a = 1 := by
    rcases Int.units_eq_one_or (hexSign b) with hbEven | hbOdd
    · exact ⟨b, hbA, hb1, hbEven⟩
    · let a := b * g
      have haA : a ∈ A := A.mul_mem hbA hgA
      have haEven : hexSign a = 1 := by simp [a, hbOdd, hgod]
      have ha1 : a ≠ 1 := by
        intro ha
        have hbg : b = g := by
          calc
            b = g⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [a] using ha)
            _ = g := hginv
        apply hbnot
        rw [hbg]
        exact Subgroup.mem_zpowers g
      exact ⟨a, haA, ha1, haEven⟩
  obtain ⟨a, haA, ha1, haEven⟩ := heven
  let H : Subgroup HexAutomorphisms := Subgroup.zpowers g
  let γ : H := ⟨g, Subgroup.mem_zpowers g⟩
  have hγ : ∀ y : H, y ∈ Subgroup.zpowers γ := by
    intro y
    obtain ⟨n, hn⟩ := y.property
    exact ⟨n, Subtype.ext hn⟩
  have hδ : ∀ y : Subgroup.zpowers SL2FourNatural.fieldFrobenius, y ∈
      Subgroup.zpowers (⟨SL2FourNatural.fieldFrobenius, Subgroup.mem_zpowers _⟩) := by
    intro y
    obtain ⟨n, hn⟩ := y.property
    exact ⟨n, Subtype.ext hn⟩
  have hγord : orderOf γ = orderOf g := by
    rw [← Subgroup.orderOf_coe γ, ← Subgroup.orderOf_coe γ.val]
  have hδord : orderOf (⟨SL2FourNatural.fieldFrobenius, Subgroup.mem_zpowers _⟩ :
      Subgroup.zpowers SL2FourNatural.fieldFrobenius) = orderOf SL2FourNatural.fieldFrobenius := by
    exact (Subgroup.orderOf_coe _).symm
  have hord : orderOf γ = orderOf (⟨SL2FourNatural.fieldFrobenius,
      Subgroup.mem_zpowers _⟩ : Subgroup.zpowers SL2FourNatural.fieldFrobenius) := by
    calc
      orderOf γ = orderOf g := hγord
      _ = orderOf SL2FourNatural.fieldFrobenius := hgord.trans hσord.symm
      _ = orderOf (⟨SL2FourNatural.fieldFrobenius, Subgroup.mem_zpowers _⟩ :
        Subgroup.zpowers SL2FourNatural.fieldFrobenius) := hδord.symm
  let e : H ≃* Subgroup.zpowers SL2FourNatural.fieldFrobenius :=
    mulEquivOfOrderOfEq hγ hδ hord
  let τ : H →* (F ≃+* F) :=
    (Subgroup.zpowers SL2FourNatural.fieldFrobenius).subtype.comp e.toMonoidHom
  have hτ : Function.Injective τ := Subtype.val_injective.comp e.injective
  have hτγ : τ γ = SL2FourNatural.fieldFrobenius := by
    change ((mulEquivOfOrderOfEq hγ hδ hord γ :
        Subgroup.zpowers SL2FourNatural.fieldFrobenius) : F ≃+* F) = _
    rw [mulEquivOfOrderOfEq_apply_gen]
  have hsemiH : ∀ (x : H) (c : F) (v : hexacode),
      action x.val (c • v) = τ x c • action x.val v := by
    intro x
    obtain ⟨n, hn⟩ := mem_powers_iff_mem_zpowers.mpr (hγ x)
    subst x
    induction n with
    | zero => intro c v; simp [τ]
    | succ n ih =>
      intro c v
      simp only [pow_succ', map_mul]
      change action γ.val (action (γ ^ n).val (c • v)) =
        (τ γ) ((τ (γ ^ n)) c) • action γ.val (action (γ ^ n).val v)
      rw [ih, hτγ]
      exact hsemi _ _
  have hspan : Submodule.span F {v : hexacode |
      ∀ x : H, action x.val v = v} = ⊤ := by
    let : Fintype H := Fintype.ofFinite H
    exact Representation.FiniteFieldSemilinearDisplacement.Descent.span_fixed_eq_top
      (action.comp H.subtype) τ hτ (by
        intro x c v
        exact hsemiH x c v)
  let U : Submodule F hexacode :=
    { carrier := {v | action a v = v}
      zero_mem' := by simp
      add_mem' := by
        intro v w hv hw
        change action a (v + w) = v + w
        change action a v = v at hv
        change action a w = w at hw
        rw [map_add, hv, hw]
      smul_mem' := by
        intro c v hv
        change action a (c • v) = c • v
        change action a v = v at hv
        rw [action_even_smul a haEven, hv] }
  have hspanU : Submodule.span F {v : hexacode |
      ∀ x : H, action x.val v = v} ≤ U := by
    apply Submodule.span_le.mpr
    intro v hv
    have hvH : v ∈ fixedSpace action (Subgroup.zpowers g) := by
      change ∀ x : H, action x.val v = v
      exact hv
    have hvA : v ∈ fixedSpace action A := by
      rw [hfixed]
      exact hvH
    exact hvA ⟨a, haA⟩
  have hU : U = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact hspanU
  have ha_id : ∀ v : hexacode, action a v = v := by
    intro v
    have hvU : v ∈ U := by rw [hU]; exact Submodule.mem_top
    exact hvU
  have : a = 1 := by
    apply action_injective
    apply LinearMap.ext
    intro v
    exact ha_id v
  exact ha1 this

theorem eq_zero_of_odd_fixes_scalar (g : HexAutomorphisms) (hg : hexSign g = -1)
    (v : hexacode) (hv : action g v = v)
    (hs : action g (omega • v) = omega • v) : v = 0 := by
  have h := action_odd_smul g hg omega v
  rw [hs, hv] at h
  have hz : (omega - SL2FourNatural.fieldFrobenius omega) • v = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr (by decide : omega ≠ SL2FourNatural.fieldFrobenius omega))

private theorem bestOffender_even_subgroup
    {A : Subgroup HexAutomorphisms} (hA : IsBestOffender action A)
    (hAe : A ≤ hexSign.ker) :
    IsBestOffender evenAction (A.subgroupOf hexSign.ker) := by
  have h := hA.subgroupOf action hAe
  change IsBestOffender
    (action.comp hexSign.ker.subtype) (A.subgroupOf hexSign.ker) at h
  exact h

private theorem full_planeKernel_le_even (A : Subgroup HexAutomorphisms)
    (hA : A ≤ hexSign.ker) (hfin :
      Module.finrank (ZMod 2) (fixedSpace action A) = 4) :
    subspaceKernel action (fixedSpace action A) ⊤ ≤ hexSign.ker := by
  have hne : fixedSpace action A ≠ ⊥ := by
    intro h
    have hpos := hfin
    rw [h] at hpos
    simp at hpos
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let Ae : Subgroup HexEvenAutomorphisms := A.subgroupOf hexSign.ker
  have hfix : fixedSpace action A = fixedSpace evenAction Ae := by
    symm
    change fixedSpace (action.comp hexSign.ker.subtype) Ae = _
    rw [fixedSpace_comp_map, Subgroup.map_subgroupOf_eq_of_le hA]
  intro g hg
  rcases Int.units_eq_one_or (hexSign g) with he | ho
  · exact he
  · exfalso
    have hvA : action g v = v := hg.2 v hv
    have hvAe : v ∈ fixedSpace evenAction Ae := by rw [← hfix]; exact hv
    have hsAe : action hexZ v ∈ fixedSpace evenAction Ae :=
      (fixedSpace_scalar_stable Ae v).mpr hvAe
    have hs : action g (omega • v) = omega • v := by
      apply hg.2
      rw [← scalar_eq_omega_smul]
      rw [hfix]
      exact hsAe
    exact hv0 (eq_zero_of_odd_fixes_scalar g ho v hvA hs)

theorem full_bestOffender_card (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender action A) : Nat.card A = 4 := by
  have hAe := bestOffender_le_even A hA
  let Ae := A.subgroupOf hexSign.ker
  have hcard : Nat.card Ae = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAe).toEquiv
  exact hcard.symm.trans (bestOffender_dimensions Ae
    (bestOffender_even_subgroup hA hAe)).2.1

theorem full_bestOffender_fixedSpace_finrank (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender action A) :
    Module.finrank (ZMod 2) (fixedSpace action A) = 4 := by
  have hAe := bestOffender_le_even A hA
  let Ae := A.subgroupOf hexSign.ker
  have hfix : fixedSpace action A = fixedSpace evenAction Ae := by
    symm
    change fixedSpace (action.comp hexSign.ker.subtype) Ae = _
    rw [fixedSpace_comp_map, Subgroup.map_subgroupOf_eq_of_le hAe]
  rw [hfix]
  exact (bestOffender_dimensions Ae (bestOffender_even_subgroup hA hAe)).2.2.2

theorem full_bestOffender_eq_kernel (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender action A) :
    A = subspaceKernel action (fixedSpace action A) ⊤ := by
  have hAe := bestOffender_le_even A hA
  let Ae := A.subgroupOf hexSign.ker
  have hfix : fixedSpace action A = fixedSpace evenAction Ae := by
    symm
    change fixedSpace (action.comp hexSign.ker.subtype) Ae = _
    rw [fixedSpace_comp_map, Subgroup.map_subgroupOf_eq_of_le hAe]
  have hKle := full_planeKernel_le_even A hAe (full_bestOffender_fixedSpace_finrank A hA)
  have hKcard : Nat.card (subspaceKernel action (fixedSpace action A) ⊤) ≤ 4 := by
    let K := subspaceKernel action (fixedSpace action A) ⊤
    have hKe : K.subgroupOf hexSign.ker ≤
        subspaceKernel evenAction (fixedSpace evenAction Ae) ⊤ := by
      intro g hg
      refine ⟨Subgroup.mem_top _, ?_⟩
      intro v hv
      exact hg.2 v (hfix.symm ▸ hv)
    have hc : Nat.card K = Nat.card (K.subgroupOf hexSign.ker) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv).symm
    rw [hc]
    exact (Subgroup.card_le_of_le hKe).trans
      (planeKernel_card_le_four _ (fixedSpace_scalar_stable Ae)
        (bestOffender_dimensions Ae (bestOffender_even_subgroup hA hAe)).2.2.2)
  apply Subgroup.eq_of_le_of_card_ge
  · intro a ha
    exact ⟨mem_top _, fun v hv => hv ⟨a, ha⟩⟩
  · rw [full_bestOffender_card A hA]
    exact hKcard

/-! ## The two inner four-groups and uniqueness -/

theorem lineGroup_rank : rank SylowModel.lineGroup = 2 := by
  rw [rank, SylowModel.lineGroup_card]
  decide

theorem planeGroup_rank : rank SylowModel.planeGroup = 2 := by
  rw [rank, SylowModel.planeGroup_card]
  decide

theorem lineGroup_not_offender : ¬ IsOffender evenAction SylowModel.lineGroup := by
  intro h
  have hs := fixedCodim_add_finrank evenAction SylowModel.lineGroup
  rw [hexacode_finrank, lineFixed_finrank] at hs
  have ho := h.2
  rw [lineGroup_rank] at ho
  omega

theorem planeGroup_best : IsBestOffender evenAction SylowModel.planeGroup := by
  apply (isBestOffender_iff_of_not_strong evenAction no_strong _).2
  refine ⟨⟨?_, SylowModel.planeGroup_elementary⟩, ?_⟩
  · intro h
    have hc := SylowModel.planeGroup_card
    rw [h, Subgroup.card_bot] at hc
    omega
  · have hs := fixedCodim_add_finrank evenAction SylowModel.planeGroup
    rw [hexacode_finrank, planeFixed_finrank] at hs
    rw [planeGroup_rank]
    omega

/-- The concrete plane-fixing four-group is also best in the full action. -/
theorem full_planeGroup_best :
    IsBestOffender action (SylowModel.planeGroup.map hexSign.ker.subtype) :=
  planeGroup_best.map_subtype action

/-- The first inner four-group has the source ratio two. -/
theorem lineGroup_actionRatio : actionRatio evenAction SylowModel.lineGroup = 2 := by
  have h := fixedCodim_add_finrank evenAction SylowModel.lineGroup
  rw [hexacode_finrank, lineFixed_finrank] at h
  have hc : fixedCodim evenAction SylowModel.lineGroup = 4 := by omega
  rw [actionRatio, hc, lineGroup_rank]
  apply Eq.symm
  apply (ENNReal.eq_div_iff (by norm_num) (by simp)).2
  norm_num

/-- The plane-fixing four-group has the source ratio one. -/
theorem planeGroup_actionRatio : actionRatio evenAction SylowModel.planeGroup = 1 := by
  have h := fixedCodim_add_finrank evenAction SylowModel.planeGroup
  rw [hexacode_finrank, planeFixed_finrank] at h
  have hc : fixedCodim evenAction SylowModel.planeGroup = 2 := by omega
  rw [actionRatio, hc, planeGroup_rank]
  exact ENNReal.div_self (by norm_num) (by simp)

/-- The second inner four-group acts quadratically on the original binary code. -/
theorem planeGroup_quadratic : IsQuadratic evenAction SylowModel.planeGroup := by
  nth_rw 1 [bestOffender_eq_kernel _ planeGroup_best]
  exact planeKernel_quadratic _ (fixedSpace_scalar_stable _) planeFixed_finrank

private theorem subgroupOf_le_inter
    {A P : Subgroup HexAutomorphisms} (hAP : A ≤ P) :
    A.subgroupOf hexSign.ker ≤ (P ⊓ hexSign.ker).subgroupOf hexSign.ker := by
  intro a ha
  change a.val ∈ P ⊓ hexSign.ker
  exact ⟨hAP ha, a.property⟩

theorem bestOffender_unique_in_pgroup
    (P : Subgroup HexAutomorphisms) (hP : IsPGroup 2 P)
    {A B : Subgroup HexAutomorphisms}
    (hAP : A ≤ P) (hBP : B ≤ P)
    (hA : IsBestOffender action A) (hB : IsBestOffender action B) :
    A = B := by
  have hAe : A ≤ hexSign.ker := bestOffender_le_even A hA
  have hBe : B ≤ hexSign.ker := bestOffender_le_even B hB
  let R : Subgroup HexAutomorphisms := P ⊓ hexSign.ker
  let Ae : Subgroup HexEvenAutomorphisms := A.subgroupOf hexSign.ker
  let Be : Subgroup HexEvenAutomorphisms := B.subgroupOf hexSign.ker
  let Re : Subgroup HexEvenAutomorphisms := R.subgroupOf hexSign.ker
  have hRA : Ae ≤ Re := by
    exact subgroupOf_le_inter hAP
  have hRB : Be ≤ Re := by
    exact subgroupOf_le_inter hBP
  have hReP : IsPGroup 2 Re := by
    apply hP.of_injective
      ((hexSign.ker.subtype.comp Re.subtype).codRestrict P (by
        intro x
        exact x.property.1))
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : P => (z : HexAutomorphisms)) hxy
  obtain ⟨S, hReS⟩ := hReP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq HexEvenAutomorphisms S standardSylow
  have hS : (S : Subgroup HexEvenAutomorphisms).map
      (MulAut.conj g).toMonoidHom = SylowModel.sylowGroup := by
    exact congrArg Sylow.toSubgroup hg
  have hAe_best : IsBestOffender evenAction Ae :=
    bestOffender_even_subgroup hA hAe
  have hBe_best : IsBestOffender evenAction Be :=
    bestOffender_even_subgroup hB hBe
  let Ae' := Ae.map (MulAut.conj g).toMonoidHom
  let Be' := Be.map (MulAut.conj g).toMonoidHom
  have hAe'_best : IsBestOffender evenAction Ae' := hAe_best.map_conj evenAction g
  have hBe'_best : IsBestOffender evenAction Be' := hBe_best.map_conj evenAction g
  have hAe'_S : Ae' ≤ SylowModel.sylowGroup := by
    rw [← hS]
    exact Subgroup.map_mono (hRA.trans hReS)
  have hBe'_S : Be' ≤ SylowModel.sylowGroup := by
    rw [← hS]
    exact Subgroup.map_mono (hRB.trans hReS)
  have hAe'_card : Nat.card Ae' = 4 :=
    (bestOffender_dimensions Ae' hAe'_best).2.1
  have hBe'_card : Nat.card Be' = 4 :=
    (bestOffender_dimensions Be' hBe'_best).2.1
  have hAe'_plane : Ae' = SylowModel.planeGroup := by
    rcases SylowModel.fourGroup_exhaustion Ae' hAe'_best.1.2 hAe'_S hAe'_card with h | h
    · exact (lineGroup_not_offender ((h ▸ hAe'_best).isOffender _)).elim
    · exact h
  have hBe'_plane : Be' = SylowModel.planeGroup := by
    rcases SylowModel.fourGroup_exhaustion Be' hBe'_best.1.2 hBe'_S hBe'_card with h | h
    · exact (lineGroup_not_offender ((h ▸ hBe'_best).isOffender _)).elim
    · exact h
  have hmap : Ae = Be := by
    exact (Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective) (by
        exact hAe'_plane.trans hBe'_plane.symm)
  calc
    A = Ae.map hexSign.ker.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hAe).symm
    _ = Be.map hexSign.ker.subtype := congrArg
      (Subgroup.map hexSign.ker.subtype) hmap
    _ = B := Subgroup.map_subgroupOf_eq_of_le hBe

end Representation.Hexacode.ThompsonOffenders

namespace Representation.Hexacode

/-- Every best offender in the full action is contained in the even cover. -/
theorem bestOffender_le_even (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender action A) : A ≤ hexSign.ker :=
  ThompsonOffenders.bestOffender_le_even A hA

/-- All best offenders in the full action are four-groups. -/
theorem bestOffender_card (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender action A) : Nat.card A = 4 :=
  ThompsonOffenders.full_bestOffender_card A hA

/-- The fixed projective line has binary dimension four. -/
theorem bestOffender_fixedSpace_finrank (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender action A) :
    Module.finrank (ZMod 2) (BinaryOffender.fixedSpace action A) = 4 :=
  ThompsonOffenders.full_bestOffender_fixedSpace_finrank A hA

/-- The offender is the full pointwise kernel, including the odd coset. -/
theorem bestOffender_eq_kernel (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender action A) :
    A = BinaryOffender.subspaceKernel action (BinaryOffender.fixedSpace action A) ⊤ :=
  ThompsonOffenders.full_bestOffender_eq_kernel A hA

/-- Scalar stability of the actual fixed space of a full-group best offender. -/
theorem bestOffender_fixedSpace_scalar_stable (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender action A) :
    hexZ ∈ subspaceStabilizer action (fixedSpace action A) := by
  have he := bestOffender_le_even A hA
  have hf : fixedSpace evenAction (A.subgroupOf hexSign.ker) = fixedSpace action A := by
    change fixedSpace (action.comp hexSign.ker.subtype) (A.subgroupOf hexSign.ker) = _
    rw [fixedSpace_comp_map, Subgroup.map_subgroupOf_eq_of_le he]
  rw [← hf]
  exact ThompsonOffenders.fixedSpace_scalar_stable _

/-- The same fixed space is a vector plane over the actual four-element field. -/
theorem bestOffender_fixedSpace_field_finrank (A : Subgroup HexAutomorphisms)
    (hA : IsBestOffender action A) :
    Module.finrank F (scalarSubmodule (fixedSpace action A)
      (bestOffender_fixedSpace_scalar_stable A hA)) = 2 := by
  have h := scalarSubmodule_finrank (fixedSpace action A)
    (bestOffender_fixedSpace_scalar_stable A hA)
  rw [bestOffender_fixedSpace_finrank A hA] at h
  omega

/-- There is at most one best offender inside any common two-subgroup. -/
theorem bestOffender_unique_in_pgroup
    (P : Subgroup HexAutomorphisms) (hP : IsPGroup 2 P)
    {A B : Subgroup HexAutomorphisms}
    (hAP : A ≤ P) (hBP : B ≤ P)
    (hA : IsBestOffender action A) (hB : IsBestOffender action B) :
    A = B :=
  ThompsonOffenders.bestOffender_unique_in_pgroup P hP hAP hBP hA hB

/-- Application to the offender-generated image used in the Thompson marking:
one nontrivial best-offender image identifies the whole generated subgroup. -/
theorem generatedBy_bestOffenders_eq
    (P : Subgroup HexAutomorphisms) (hP : IsPGroup 2 P)
    (A : Subgroup HexAutomorphisms) (hAP : A ≤ P) (hA : IsBestOffender action A) :
    generatedBy {B | IsBestOffender action B} P = A := by
  apply le_antisymm
  · apply iSup_le
    intro B
    apply iSup_le
    rintro ⟨hB, hBP⟩
    exact le_of_eq (bestOffender_unique_in_pgroup P hP hBP hAP hB hA)
  · exact le_iSup_of_le A (le_iSup_of_le ⟨hA, hAP⟩ le_rfl)

end Representation.Hexacode

