module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.Basic
public import Theory.Representation.PSL3Two.SingerRestriction
public import Theory.GroupAction.SubgroupConjugation

/-!
# The literal Singer fixed four-group in a group of type Ru

Both the Singer and cubic subgroups are mapped by the original Ru1 quotient
map. Coprimality with the two-core makes these restrictions injective and
retains their orders and normalization relation.

The natural coordinates give C_V(B₇) = 1 and Singer transitivity on V minus
its identity. Each fixed Steinberg vector has eight preimages. The order-seven
group acts on that fiber, so the p-group fixed-point theorem supplies a fixed
preimage. The zero natural fixed space makes that lift unique. Restriction
of the actual coordinate homomorphism therefore identifies C_S(B₇) with the
two-dimensional fixed plane, giving the fixed-four-group part of J.2.3(1).

The explicit coordinate formula is retained for transporting the cubic orbit
calculation. The cubic order hypothesis is needed only for `cubicImage_card`;
the fixed-four-group and natural transitivity results do not require it.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma J.2.3, printed pp.433–434 (PDF pp.444–445).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- Restriction of the original common Ru1 quotient map to a subgroup of L. -/
noncomputable def modelMap (d : TypeRuSetup G) (K : Subgroup G) (hK : K ≤ d.L) :
    K →* BinaryLinearThree.Group := d.ru1.quotientMap.comp (inclusion hK)

lemma modelMap_injective (d : TypeRuSetup G) (K : Subgroup G) (hK : K ≤ d.L)
    (hcop : Nat.Coprime (Nat.card K) 2048) : Function.Injective (modelMap d K hK) := by
  have hdis : Disjoint K d.S := disjoint_of_coprime_natCard (d.ru1.card_S ▸ hcop)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [eq_bot_iff_forall]
  intro k hk
  apply Subtype.ext
  apply hdis.le_bot
  refine ⟨k.property, ?_⟩
  have hker : inclusion hK k ∈ d.ru1.quotientMap.ker := hk
  rw [d.ru1.quotient_kernel] at hker
  exact hker

lemma modelMap_range_card (d : TypeRuSetup G) (K : Subgroup G) (hK : K ≤ d.L)
    (hcop : Nat.Coprime (Nat.card K) 2048) :
    Nat.card (modelMap d K hK).range = Nat.card K :=
  (Nat.card_congr (Equiv.ofInjective _ (modelMap_injective d K hK hcop))).symm

/-- The image of the chosen Singer subgroup under the common quotient map. -/
noncomputable def singerImage (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) : Subgroup BinaryLinearThree.Group :=
  (modelMap d c.B7 c.le_L).range

lemma singerImage_card (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) : Nat.card (singerImage d B c) = 7 := by
  rw [singerImage, modelMap_range_card, c.card_seven]
  rw [c.card_seven]
  decide


/-- The image of the actual cubic subgroup under the same Ru1 quotient map. -/
noncomputable def cubicImage (d : TypeRuSetup G) (B : Sylow 3 d.L₁) :
    Subgroup BinaryLinearThree.Group := (modelMap d (cubicSubgroup d B)
      (cubicSubgroup_le_L d B)).range

lemma cubicImage_card (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (hB : Nat.card (cubicSubgroup d B) = 3) : Nat.card (cubicImage d B) = 3 := by
  rw [cubicImage, modelMap_range_card, hB]
  rw [hB]
  decide

lemma modelMap_range (d : TypeRuSetup G) (K : Subgroup G) (hK : K ≤ d.L) :
    (modelMap d K hK).range = (K.subgroupOf d.L).map d.ru1.quotientMap := by
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨inclusion hK k, k.property, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

lemma cubicImage_normalizes_singerImage (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) : cubicImage d B ≤ normalizer (singerImage d B c) := by
  have hn : (cubicSubgroup d B).subgroupOf d.L ≤
      normalizer (c.B7.subgroupOf d.L) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro h
    exact mem_normalizer_iff.mp (c.normalized hb) (h : G)
  rw [cubicImage, singerImage, modelMap_range, modelMap_range]
  exact (map_mono hn).trans (le_normalizer_map d.ru1.quotientMap)

private lemma natural_coordinates_injective (d : TypeRuSetup G) :
    Function.Injective d.ru1.natural.coordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [d.ru1.natural.kernel_eq, bot_subgroupOf]

/-- The Singer fixed subgroup meets the natural kernel trivially. -/
lemma SingerChoice.fixedCore_disjoint_V (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) : Disjoint (fixedCore d c.B7) d.V := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro v hv
  let x : d.V := ⟨v, hv.2⟩
  have hf : (d.ru1.natural.coordinates x).toAdd ∈
      fixedSpace BinaryLinearThree.W (singerImage d B c) := by
    intro h
    obtain ⟨b, hb⟩ := h.property
    change BinaryLinearThree.W h.val (d.ru1.natural.coordinates x).toAdd = _
    rw [← hb]
    have he := d.ru1.natural.equivariant (inclusion c.le_L b) x
    have hc : (b : G) * v * (b : G)⁻¹ = v :=
      mul_inv_eq_iff_eq_mul.mpr (hv.1.2 b b.property)
    have hx : (⟨(b : G) * v * (b : G)⁻¹, by rw [hc]; exact hv.2⟩ : d.V) = x := Subtype.ext hc
    exact he.symm.trans (congrArg (fun y => (d.ru1.natural.coordinates y).toAdd) hx)
  rw [BinaryLinearThree.SingerRestriction.natural_fixedSpace_order_seven _
    (singerImage_card d B c)] at hf
  exact (d.ru1.natural.coordinates_eq_one_iff x).mp hf

/-- Singer conjugation is transitive on the literal natural kernel minus its identity. -/
lemma SingerChoice.transitive_V (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) (v w : G) (hv : v ∈ d.V) (hw : w ∈ d.V)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) : ∃ b ∈ c.B7, b * v * b⁻¹ = w := by
  let v' : d.V := ⟨v, hv⟩
  let w' : d.V := ⟨w, hw⟩
  have hv0 : (d.ru1.natural.coordinates v').toAdd ≠ 0 := by
    intro h
    exact hv1 ((d.ru1.natural.coordinates_eq_one_iff v').mp h)
  have hw0 : (d.ru1.natural.coordinates w').toAdd ≠ 0 := by
    intro h
    exact hw1 ((d.ru1.natural.coordinates_eq_one_iff w').mp h)
  obtain ⟨g, hg, he⟩ := BinaryLinearThree.SingerRestriction.natural_transitive_order_seven
    (singerImage d B c) (singerImage_card d B c) _ _ hv0 hw0
  obtain ⟨b, hb⟩ := hg
  refine ⟨b, b.property, ?_⟩
  have heq := d.ru1.natural.equivariant (inclusion c.le_L b) v'
  change _ = BinaryLinearThree.W (modelMap d c.B7 c.le_L b) _ at heq
  rw [hb] at heq
  exact congrArg Subtype.val (natural_coordinates_injective d (heq.trans he))

/-- Restriction of the literal Steinberg coordinates to the fixed subgroup. -/
noncomputable def fixedCoreCoordinates (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) :
    fixedCore d c.B7 →* Multiplicative (fixedSpace BinaryLinearThree.S (singerImage d B c)) where
  toFun x := Multiplicative.ofAdd ⟨(d.ru1.steinberg.coordinates ⟨x, x.property.1⟩).toAdd, by
    intro h
    obtain ⟨b, hb⟩ := h.property
    change BinaryLinearThree.S h.val _ = _
    rw [← hb]
    have he := d.ru1.steinberg.equivariant (inclusion c.le_L b) ⟨x, x.property.1⟩
    have hc : (b : G) * (x : G) * (b : G)⁻¹ = x :=
      mul_inv_eq_iff_eq_mul.mpr (x.property.2 b b.property)
    exact he.symm.trans (congrArg (fun y : d.S =>
      (d.ru1.steinberg.coordinates y).toAdd) (Subtype.ext hc))⟩
  map_one' := by apply Multiplicative.toAdd.injective; apply Subtype.ext; exact map_one d.ru1.steinberg.coordinates
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact map_mul d.ru1.steinberg.coordinates ⟨x, x.property.1⟩ ⟨y, y.property.1⟩

lemma fixedCoreCoordinates_injective (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) : Function.Injective (fixedCoreCoordinates d B c) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [eq_bot_iff_forall]
  intro x hx
  apply Subtype.ext
  apply (c.fixedCore_disjoint_V d B).le_bot
  refine ⟨x.property, ?_⟩
  apply (d.ru1.steinberg.coordinates_eq_one_iff ⟨x, x.property.1⟩).mp
  exact congrArg (fun y => ((Multiplicative.toAdd y).val)) hx

/-- A group of order seven fixes a point in each invariant eight-element fiber. -/
lemma fixedCoreCoordinates_surjective (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) : Function.Surjective (fixedCoreCoordinates d B c) := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : MulDistribMulAction c.B7 d.S :=
    conjMulDistribMulActionOfLeNormalizer c.B7 d.S
      (c.le_L.trans d.ru1.steinberg.normalized)
  let f := d.ru1.steinberg.coordinates
  intro v
  let F := {s : d.S // f s = Multiplicative.ofAdd v.toAdd.val}
  let _ : MulAction c.B7 F := {
    smul b s := ⟨b • s.val, by
      apply Multiplicative.toAdd.injective
      have he := d.ru1.steinberg.equivariant (inclusion c.le_L b) s.val
      change (f (b • s.val)).toAdd =
        BinaryLinearThree.S (modelMap d c.B7 c.le_L b) (f s.val).toAdd at he
      rw [s.property] at he
      exact he.trans (v.toAdd.property ⟨modelMap d c.B7 c.le_L b, ⟨b, rfl⟩⟩)⟩
    one_smul s := Subtype.ext (one_smul c.B7 s.val)
    mul_smul b b' s := Subtype.ext (mul_smul b b' s.val) }
  have hcard : Nat.card F = 8 := by
    calc
      Nat.card F = Nat.card f.ker := Nat.card_congr
        (MonoidHom.fiberEquivKerOfSurjective (f := f) d.ru1.steinberg.onto
          (Multiplicative.ofAdd v.toAdd.val))
      _ = 8 := by
        rw [show f.ker = d.V.subgroupOf d.S from d.ru1.steinberg.kernel_eq,
          Nat.card_congr (subgroupOfEquivOfLe d.ru1.steinberg.kernel_le).toEquiv,
          d.ru1.card_V]
  have hp : IsPGroup 7 c.B7 := IsPGroup.of_card (n := 1) (by simpa using c.card_seven)
  obtain ⟨s, hs⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card F
    (by rw [hcard]; decide)
  have hfix : (s.val : G) ∈ fixedCore d c.B7 := by
    refine ⟨s.val.property, ?_⟩
    intro b hb
    have he := congrArg (fun t : F => (t.val : G)) (hs ⟨b, hb⟩)
    exact mul_inv_eq_iff_eq_mul.mp he
  refine ⟨⟨s.val, hfix⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact s.property

/-- The actual fixed subgroup is isomorphic to the fixed plane by its coordinates. -/
noncomputable def SingerChoice.fixedCoreEquiv (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) :
    fixedCore d c.B7 ≃* Multiplicative (fixedSpace BinaryLinearThree.S (singerImage d B c)) :=
  MulEquiv.ofBijective (fixedCoreCoordinates d B c)
    ⟨fixedCoreCoordinates_injective d B c, fixedCoreCoordinates_surjective d B c⟩

/-- The fixed-plane equivalence retains the literal Steinberg coordinate map. -/
lemma SingerChoice.fixedCoreEquiv_apply (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) (x : fixedCore d c.B7) :
    ((c.fixedCoreEquiv d B x).toAdd : BinaryLinearThree.Steinberg) =
      (d.ru1.steinberg.coordinates ⟨x, x.property.1⟩).toAdd := rfl

/-- The fixed subgroup is the standard elementary abelian group of order four. -/
noncomputable def SingerChoice.fixedCoreEquivFour (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) : fixedCore d c.B7 ≃* Multiplicative (ZMod 2 × ZMod 2) :=
  (c.fixedCoreEquiv d B).trans
    (BinaryLinearThree.SingerRestriction.fixedPlaneEquivOfCard _
      (singerImage_card d B c)).toMultiplicative

/-- In particular the literal fixed subgroup has order four. -/
lemma SingerChoice.fixedCore_card (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) : Nat.card (fixedCore d c.B7) = 4 := by
  rw [Nat.card_congr (c.fixedCoreEquivFour d B).toEquiv]
  change Nat.card (ZMod 2 × ZMod 2) = 4
  simp

/-- The fixed four-group is abelian; this discharges the coprime splitting premise. -/
lemma SingerChoice.fixedCore_commutative (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) : IsMulCommutative (fixedCore d c.B7) := by
  constructor
  constructor
  intro x y
  apply (c.fixedCoreEquivFour d B).injective
  rw [map_mul, map_mul, mul_comm]
end CFSG.Quasithin.ChapterJ.SpecialCore
