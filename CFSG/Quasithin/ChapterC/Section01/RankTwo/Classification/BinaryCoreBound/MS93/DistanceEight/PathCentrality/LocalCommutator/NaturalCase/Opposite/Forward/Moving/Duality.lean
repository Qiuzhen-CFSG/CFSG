module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source
public import Theory.Representation.QuadraticDuality
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.GroupTheory.Index
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.PGroup

/-!
# Fixed points of the marked opposite factor

Natural and inverse-transpose coordinates use one projection and the same
marking. The natural group commutator embeds in the linear displacement space.
When that group has order four, its linear span has dimension at least two.
Dual fixed vectors annihilate that span, so there are at most two fixed vectors
on the opposite factor. The coordinate kernel gives the relative-index bound.

For a two-group actor, orbit counting makes the number of fixed points on the
literal order-eight quotient even. Thus its fixed subgroup has order exactly
two. This proves the needed Klein-four calculation by duality, without changing
the actor marking or classifying it up to an unrelated automorphism.
The concrete selected-path applications are in Moving.Fixed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

public section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Moving
open RankOnePairing
variable {G : Type*} [Group G] [Finite G]
private noncomputable def markedRepresentation (π : G →* SL) (σ : SL ≃* SL) :
    Representation (ZMod 2) G (Fin 3 → ZMod 2) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    (Matrix.SpecialLinearGroup.toLin'.comp (σ.toMonoidHom.comp π))

omit [Finite G] in
private theorem dual_coordinates_action (π : G →* SL) (σ : SL ≃* SL)
    (g : G) (v : Fin 3 → ZMod 2) :
    dotProductEquiv (ZMod 2) (Fin 3) (((σ (π g))⁻¹).val.transpose.mulVec v) =
      (markedRepresentation π σ).dual g (dotProductEquiv (ZMod 2) (Fin 3) v) := by
  apply LinearMap.ext
  intro w
  change dotProduct (((σ (π g))⁻¹).val.transpose.mulVec v) w =
    dotProduct v ((σ (π g⁻¹)).val.mulVec w)
  rw [map_inv, map_inv, dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

private theorem fixed_image_card_and_index {π : G →* SL} {H N Z : Subgroup G} [N.Normal]
    (n : NaturalFactor π ⊤ Z ⊥) (d : DualFactor π ⊤ H N Z n)
    (A : Subgroup G) (hcomm : Nat.card (⁅Z, A⁆ : Subgroup G) = 4) :
    Nat.card (((centralizerModulo H A N).subgroupOf H).map d.coordinates) ≤ 2 ∧
      4 ≤ (centralizerModulo H A N).relIndex H := by
  let : Z.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp n.normalized)
  let : H.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp d.normalized)
  let : Finite (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) :=
    Finite.of_equiv (Fin 3 → ZMod 2) (dotProductEquiv (ZMod 2) (Fin 3)).toEquiv
  let ρ := markedRepresentation π n.marking
  let C := Coinvariants.ker (ρ.comp A.subtype)
  let K : Subgroup (Multiplicative (Fin 3 → ZMod 2)) := C.toAddSubgroup.toSubgroup
  have hn (g : G) (x : Z) :
      (n.coordinates (MulAut.conjNormal g x)).toAdd = ρ g (n.coordinates x).toAdd :=
    n.action g (mem_top g) x (MulAut.conjNormal g x) rfl
  have hdis : ⁅Z, A⁆ ≤ (K.comap n.coordinates).map Z.subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha x hx
    let u : Z := ⟨x, hx⟩
    let y : Z := MulAut.conjNormal a u * u⁻¹
    refine ⟨y, ?_, rfl⟩
    change (n.coordinates y).toAdd ∈ C
    change (n.coordinates (MulAut.conjNormal a u * u⁻¹)).toAdd ∈ C
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg, hn]
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) ⟨a, ha⟩ _
  have hC : 4 ≤ Nat.card C := by
    have hle := Nat.card_le_card_of_injective (inclusion hdis) (inclusion_injective hdis)
    rw [hcomm, card_map_of_injective Z.subtype_injective] at hle
    have hcard : Nat.card (K.comap n.coordinates) ≤ Nat.card K := by
      exact Nat.card_le_card_of_injective
        (fun x : K.comap n.coordinates => (⟨n.coordinates x, x.property⟩ : K))
        (fun x y h => Subtype.ext (n.equivOfBot.injective (congrArg Subtype.val h)))
    exact hle.trans hcard
  have hrank : 2 ≤ Module.finrank (ZMod 2) C := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hC
    by_contra h
    have hl : Module.finrank (ZMod 2) C ≤ 1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hl
    omega
  have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq C
  rw [Representation.dualAnnihilator_coinvariantsKer] at hsum
  have hthree : Module.finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := by simp
  rw [hthree] at hsum
  have hfixrank : Module.finrank (ZMod 2) (invariants (ρ.dual.comp A.subtype)) ≤ 1 := by
    change Module.finrank (ZMod 2) (invariants (dual (ρ.comp A.subtype))) ≤ 1
    omega
  have hfixcard : Nat.card (invariants (ρ.dual.comp A.subtype)) ≤ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hfixrank).trans_eq (by norm_num)
  let e := (dotProductEquiv (ZMod 2) (Fin 3)).toAddEquiv.toMultiplicative
  let f := e.toMonoidHom.comp d.coordinates
  let F := (centralizerModulo H A N).subgroupOf H
  have hf : Function.Surjective f := e.surjective.comp d.surjective
  have hfixed (x : F.map f) : (x : Multiplicative (Module.Dual (ZMod 2) (Fin 3 → ZMod 2))).toAdd ∈
      (invariants (ρ.dual.comp A.subtype)) := by
    obtain ⟨y, hy, he⟩ := x.property
    rw [← he]
    intro a
    let z : H := MulAut.conjNormal a.val y
    have hk : z * y⁻¹ ∈ d.coordinates.ker := by
      rw [d.kernel]
      exact (mem_centralizerModulo_iff.mp hy).2 a.val a.property
    have heq : d.coordinates z = d.coordinates y := by
      apply mul_inv_eq_one.mp
      simpa only [MonoidHom.mem_ker, map_mul, map_inv] using hk
    have ha := d.action a.val (mem_top _) y z rfl
    rw [heq] at ha
    change ρ.dual a.val (dotProductEquiv (ZMod 2) (Fin 3) (d.coordinates y).toAdd) = _
    rw [← dual_coordinates_action, ← ha]
    rfl
  have hFcard : Nat.card (F.map f) ≤ 2 := by
    apply le_trans _ hfixcard
    exact Nat.card_le_card_of_injective
      (fun x : F.map f => (⟨(x : Multiplicative (Module.Dual (ZMod 2) (Fin 3 → ZMod 2))).toAdd,
        hfixed x⟩ : (invariants (ρ.dual.comp A.subtype))))
      (fun x y h => Subtype.ext (congrArg
        (fun z : invariants (ρ.dual.comp A.subtype) => Multiplicative.ofAdd z.val) h))
  have hmul := (F.map f).card_mul_index
  have hecard : Nat.card (Multiplicative (Module.Dual (ZMod 2) (Fin 3 → ZMod 2))) = 8 := by
    rw [← Nat.card_congr e.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp
  rw [hecard] at hmul
  have himage : 4 ≤ (F.map f).index := by nlinarith
  have hi := (F.index_map_dvd hf)
  refine ⟨?_, himage.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero F.index_ne_zero_of_finite) hi)⟩
  change Nat.card (F.map d.coordinates) ≤ 2
  have he := card_map_of_injective (K := F.map d.coordinates) (f := e.toMonoidHom) e.injective
  rw [map_map] at he
  exact he.symm.le.trans hFcard

/-- Order-four natural displacement gives index at least four for the opposite fixed preimage. -/
theorem fixed_index_ge_four {π : G →* SL} {H N Z : Subgroup G} [N.Normal]
    (n : NaturalFactor π ⊤ Z ⊥) (d : DualFactor π ⊤ H N Z n)
    (A : Subgroup G) (hcomm : Nat.card (⁅Z, A⁆ : Subgroup G) = 4) :
    4 ≤ (centralizerModulo H A N).relIndex H :=
  (fixed_image_card_and_index n d A hcomm).2

/-- A two-group with order-four natural displacement fixes exactly two elements on the literal opposite quotient. -/
theorem fixed_quotient_card_eq_two {π : G →* SL} {H N Z : Subgroup G} [N.Normal]
    (n : NaturalFactor π ⊤ Z ⊥) (d : DualFactor π ⊤ H N Z n)
    (A : Subgroup G) (hA : IsPGroup 2 A)
    (hcomm : Nat.card (⁅Z, A⁆ : Subgroup G) = 4) :
    Nat.card (H.map (QuotientGroup.mk' N) ⊓ centralizer
      (A.map (QuotientGroup.mk' N) : Set (G ⧸ N)) : Subgroup (G ⧸ N)) = 2 := by
  let q := QuotientGroup.mk' N
  let K := H.map q
  let T := A.map q
  let F := centralizerModulo H A N
  let F₀ := F.subgroupOf H
  let f := q.comp H.subtype
  let C := K ⊓ centralizer (T : Set (G ⧸ N))
  have hmap : F.map q = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_map_of_mem q hy.1, hy.2⟩
    · rintro ⟨⟨y, hy, rfl⟩, hfix⟩
      exact ⟨y, ⟨hy, hfix⟩, rfl⟩
  have hFmap : F₀.map f = C := by
    rw [show f = q.comp H.subtype from rfl, ← map_map,
      map_subgroupOf_eq_of_le (centralizerModulo_le H A N), hmap]
  have hk : f.ker = d.coordinates.ker := by
    rw [d.kernel]
    ext x
    change (QuotientGroup.mk' N) (x : G) = 1 ↔ (x : G) ∈ N
    exact QuotientGroup.eq_one_iff (x : G)
  have hcardC : Nat.card C ≤ 2 := by
    rw [← hFmap, ← relIndex_ker, hk, relIndex_ker]
    exact (fixed_image_card_and_index n d A hcomm).1
  have hcardK : Nat.card K = 8 := by
    rw [show K = H.map q from rfl, ← relIndex_ker, QuotientGroup.ker_mk']
    change (N.subgroupOf H).index = 8
    rw [← d.kernel, index_ker, d.coordinates.range_eq_top.mpr d.surjective, card_top]
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp
  let : H.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp d.normalized)
  let : K.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  let : MulDistribMulAction T K := conjMulDistribMulActionOfLeNormalizer T K
    le_normalizer_of_normal
  let D := FixedPoints.subgroup T K
  have hD : D = C.subgroupOf K := by
    ext x
    change (∀ t : T, t • x = x) ↔ x.val ∈ C
    constructor
    · intro h
      refine ⟨x.property, ?_⟩
      intro t ht
      have hh := congrArg Subtype.val (h ⟨t, ht⟩)
      change t * x.val * t⁻¹ = x.val at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hx t
      apply Subtype.ext
      change t.val * x.val * t.val⁻¹ = x.val
      rw [hx.2 t.val t.property, mul_inv_cancel_right]
  have hDc : Nat.card D = Nat.card C := by
    rw [hD]
    exact Nat.card_congr (subgroupOfEquivOfLe (show C ≤ K from inf_le_left)).toEquiv
  have hpg : IsPGroup 2 T := hA.map q
  have hm := hpg.card_modEq_card_fixedPoints K
  change Nat.card K % 2 = Nat.card D % 2 at hm
  rw [hcardK, hDc] at hm
  have hp : 0 < Nat.card C := Nat.card_pos
  change Nat.card C = 2
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Moving
