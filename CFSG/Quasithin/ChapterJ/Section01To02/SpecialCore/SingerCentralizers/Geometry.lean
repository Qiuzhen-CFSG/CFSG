module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Restriction.Assembly

/-!
# Transport of the Singer five-space to the actual centralizer

The original Steinberg coordinate map sends C_S(s) onto a five-dimensional
subspace. The checked Singer restriction therefore makes it cubic invariant.
Since the centralizer contains the coordinate kernel V, this proves actual
normalization. Commutator coordinates lie in the literal displacement span;
its trivial intersection with the fixed plane proves disjointness of the two
group factors, and its Singer orbit gives transitivity modulo V.

The full-commutator hypothesis is the independent J.2.3(6) input, discharged
by the SpecialCore assembly. No splitting or orbit premise is retained.

Source: Aschbacher–Smith, Lemma J.2.3(3)–(5), printed pp.433–434
(PDF pp.444–445, combined manuscript of 1 March 2004).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Representation.RegularCyclicNormalClosure
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]
noncomputable section
local instance geometrySteinbergAddCommGroup : AddCommGroup BinaryLinearThree.Steinberg := inferInstance
local instance geometrySteinbergModule : Module (ZMod 2) BinaryLinearThree.Steinberg := inferInstance

/-- The image of a subgroup in the original Steinberg coordinates. -/
def sectionImage (d : TypeRuSetup G) (K : Subgroup G) :
    Submodule (ZMod 2) BinaryLinearThree.Steinberg :=
  AddSubgroup.toZModSubmodule 2
    (((K.subgroupOf d.S).map d.ru1.steinberg.coordinates).toAddSubgroup')

lemma mem_sectionImage_iff (d : TypeRuSetup G) (K : Subgroup G)
    (hVK : d.V ≤ K) (x : d.S) :
    (d.ru1.steinberg.coordinates x).toAdd ∈ sectionImage d K ↔ (x : G) ∈ K := by
  constructor
  · rintro ⟨y, hy, he⟩
    change d.ru1.steinberg.coordinates y = d.ru1.steinberg.coordinates x at he
    have hv : ((x * y⁻¹ : d.S) : G) ∈ d.V := by
      apply (d.ru1.steinberg.coordinates_eq_one_iff _).mp
      rw [map_mul, map_inv, he]
      exact mul_inv_cancel _
    simpa using K.mul_mem (hVK hv) hy
  · intro hx
    exact ⟨x,hx,rfl⟩

lemma sectionImage_invariant (d : TypeRuSetup G) (K : Subgroup G)
    (l : d.L) (hl : (l : G) ∈ normalizer K) :
    ∀ v ∈ sectionImage d K, BinaryLinearThree.S (d.ru1.quotientMap l) v ∈ sectionImage d K := by
  rintro v ⟨x,hx,rfl⟩
  refine ⟨⟨l * x * (l : G)⁻¹,
    (mem_normalizer_iff.mp (d.ru1.steinberg.normalized l.property) x).mp x.property⟩,
    (mem_normalizer_iff.mp hl x).mp hx, ?_⟩
  exact d.ru1.steinberg.equivariant l x

lemma sectionImage_card (d : TypeRuSetup G) (K : Subgroup G)
    (hVK : d.V ≤ K) (hKS : K ≤ d.S) :
    Nat.card (sectionImage d K) * 8 = Nat.card K := by
  let f := d.ru1.steinberg.coordinates.comp (inclusion hKS)
  have hker : f.ker = d.V.subgroupOf K := by
    ext x
    exact d.ru1.steinberg.coordinates_eq_one_iff (inclusion hKS x)
  have hrange : f.range = (K.subgroupOf d.S).map d.ru1.steinberg.coordinates := by
    ext v
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨inclusion hKS x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  have hcard : Nat.card (sectionImage d K) = Nat.card f.range := by
    rw [hrange]
    rfl
  rw [hcard, ← d.ru1.card_V, ← Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv,
    ← hker, ← index_ker]
  exact f.ker.index_mul_card

lemma SingerChoice.centralizerImage_fiveSpace (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hB : Nat.card (cubicSubgroup d B) = 3)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G), d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    let A := sectionImage d (d.S ⊓ centralizer ({s} : Set G))
    let M := displacementSpan BinaryLinearThree.S (singerImage d B c) A
    Module.finrank (ZMod 2) M = 3 ∧
    A = fixedSpace BinaryLinearThree.S (singerImage d B c) ⊔ M ∧
    fixedSpace BinaryLinearThree.S (singerImage d B c) ⊓ M = ⊥ ∧
    (∀ g ∈ cubicImage d B, A.map (BinaryLinearThree.S g) = A ∧ M.map (BinaryLinearThree.S g) = M) ∧
    (∀ v ∈ M, v ≠ 0 → ∀ w ∈ M, w ≠ 0 →
      ∃ h ∈ singerImage d B c, BinaryLinearThree.S h v = w) := by
  let C := d.S ⊓ centralizer ({s} : Set G)
  let A := sectionImage d C
  have hVC : d.V ≤ C := d.ru1.V_le_coreCentralizer ⟨s,hs.1⟩
  have hfc : fixedCore d c.B7 ≤ C := by
    change fixedCore d c.B7 ≤ d.S ⊓ centralizer ({s} : Set G)
    rw [c.coreCentralizer_eq_sup_from_restriction d B s hs]
    exact le_sup_left
  apply c.fiveSpace d B hB A
  · have hcard := sectionImage_card d C hVC inf_le_left
    rw [(c.coreCentralizer_order_exponent_from_restriction d B hfull s hs hs1).1] at hcard
    have hp : 2 ^ Module.finrank (ZMod 2) A = 2 ^ 5 := by
      have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A)
      rw [Nat.card_zmod] at hc
      change Nat.card A * 8 = 256 at hcard
      omega
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hp
  · intro v hv
    obtain ⟨x,hx⟩ := (c.fixedCoreEquiv d B).surjective (Multiplicative.ofAdd ⟨v,hv⟩)
    have he : (d.ru1.steinberg.coordinates ⟨x,x.property.1⟩).toAdd = v := by
      rw [← c.fixedCoreEquiv_apply d B x, hx]
      rfl
    exact he ▸ (show (d.ru1.steinberg.coordinates ⟨x,x.property.1⟩).toAdd ∈ A from
      ⟨⟨x,x.property.1⟩,hfc x.property,rfl⟩)
  · intro h hh
    obtain ⟨b,rfl⟩ := hh
    exact sectionImage_invariant d C (inclusion c.le_L b)
      (c.normalizes_coreCentralizer d B s hs b.property)

lemma SingerChoice.cubic_normalizes_coreCentralizer (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hB : Nat.card (cubicSubgroup d B) = 3)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G), d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    cubicSubgroup d B ≤ normalizer (d.S ⊓ centralizer ({s} : Set G) : Subgroup G) := by
  let C := d.S ⊓ centralizer ({s} : Set G)
  have hi := (c.centralizerImage_fiveSpace d B hB hfull s hs hs1).2.2.2.1
  have hVC : d.V ≤ C := d.ru1.V_le_coreCentralizer ⟨s,hs.1⟩
  have forward (b : cubicSubgroup d B) (x : G) (hx : x ∈ C) :
      (b : G) * x * (b : G)⁻¹ ∈ C := by
    let l := inclusion (cubicSubgroup_le_L d B) b
    let y : d.S := ⟨(b : G) * x * (b : G)⁻¹,
      (mem_normalizer_iff.mp (d.ru1.steinberg.normalized l.property) x).mp hx.1⟩
    apply (mem_sectionImage_iff d C hVC y).mp
    have he := (hi (modelMap d (cubicSubgroup d B) (cubicSubgroup_le_L d B) b) ⟨b,rfl⟩).1
    rw [← he]
    exact ⟨(d.ru1.steinberg.coordinates ⟨x,hx.1⟩).toAdd,
      ⟨⟨x,hx.1⟩,hx,rfl⟩, (d.ru1.steinberg.equivariant l ⟨x,hx.1⟩).symm⟩
  intro b hb
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact forward ⟨b,hb⟩ x
  · intro hx
    change x ∈ C
    simpa [mul_assoc] using
      forward ⟨b⁻¹,(cubicSubgroup d B).inv_mem hb⟩ (b*x*b⁻¹) hx

/-- Every moving-factor coordinate is a Singer displacement in the actual
centralizer image. -/
lemma SingerChoice.movingCore_coordinates_mem (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (s : G) (x : d.S) (hx : (x : G) ∈ movingCore d c.B7 s) :
    (d.ru1.steinberg.coordinates x).toAdd ∈
      displacementSpan BinaryLinearThree.S (singerImage d B c)
        (sectionImage d (d.S ⊓ centralizer ({s} : Set G))) := by
  let C := d.S ⊓ centralizer ({s} : Set G)
  let M := displacementSpan BinaryLinearThree.S (singerImage d B c) (sectionImage d C)
  let D := (M.toAddSubgroup.toSubgroup.comap d.ru1.steinberg.coordinates).map d.S.subtype
  have hMD : movingCore d c.B7 s ≤ D := by
    change ⁅C,c.B7⁆ ≤ D
    rw [commutator_comm]
    apply commutator_le.mpr
    intro b hb a ha
    let l : d.L := ⟨b,c.le_L hb⟩
    let aS : d.S := ⟨a,ha.1⟩
    let y : d.S := ⟨b * a * b⁻¹,
      (mem_normalizer_iff.mp (d.ru1.steinberg.normalized l.property) a).mp ha.1⟩
    refine ⟨y * aS⁻¹, ?_, rfl⟩
    change (d.ru1.steinberg.coordinates (y * aS⁻¹)).toAdd ∈ M
    rw [map_mul, map_inv]
    change (d.ru1.steinberg.coordinates y).toAdd + -(d.ru1.steinberg.coordinates aS).toAdd ∈ M
    rw [← sub_eq_add_neg]
    rw [show (d.ru1.steinberg.coordinates y).toAdd =
      BinaryLinearThree.S (modelMap d c.B7 c.le_L ⟨b,hb⟩)
        (d.ru1.steinberg.coordinates aS).toAdd from d.ru1.steinberg.equivariant l aS]
    exact Submodule.subset_span ⟨_,⟨⟨b,hb⟩,rfl⟩,_,⟨aS,ha,rfl⟩,rfl⟩
  obtain ⟨y,hy,he⟩ := hMD hx
  have hxy : y = x := Subtype.ext he
  exact hxy ▸ hy

/-- The fixed and moving factors have trivial intersection in the original group. -/
lemma SingerChoice.fixedCore_disjoint_movingCore (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hB : Nat.card (cubicSubgroup d B) = 3)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G), d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    Disjoint (fixedCore d c.B7) (movingCore d c.B7 s) := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro x hx
  have hm := c.movingCore_coordinates_mem d B s ⟨x,hx.1.1⟩ hx.2
  have hf : (d.ru1.steinberg.coordinates ⟨x,hx.1.1⟩).toAdd ∈
      fixedSpace BinaryLinearThree.S (singerImage d B c) := by
    rw [← c.fixedCoreEquiv_apply d B ⟨x,hx.1⟩]
    exact (c.fixedCoreEquiv d B ⟨x,hx.1⟩).toAdd.property
  have hz : (d.ru1.steinberg.coordinates ⟨x,hx.1.1⟩).toAdd = 0 := by
    have hh := (c.centralizerImage_fiveSpace d B hB hfull s hs hs1).2.2.1
    have hmem := show (d.ru1.steinberg.coordinates ⟨x,hx.1.1⟩).toAdd ∈
      fixedSpace BinaryLinearThree.S (singerImage d B c) ⊓
        displacementSpan BinaryLinearThree.S (singerImage d B c)
          (sectionImage d (d.S ⊓ centralizer ({s} : Set G))) from ⟨hf,hm⟩
    rw [hh] at hmem
    exact hmem
  exact (c.fixedCore_disjoint_V d B).le_bot
    ⟨hx.1,(d.ru1.steinberg.coordinates_eq_one_iff ⟨x,hx.1.1⟩).mp hz⟩

/-- Singer conjugation is transitive on the nonidentity cosets of the actual
moving factor modulo V. -/
lemma SingerChoice.transitive_movingCore_mod_V (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hB : Nat.card (cubicSubgroup d B) = 3)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G), d.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    ∀ x ∈ movingCore d c.B7 s, ∀ y ∈ movingCore d c.B7 s,
      x ∉ d.V → y ∉ d.V → ∃ a ∈ c.B7, (a * x * a⁻¹)⁻¹ * y ∈ d.V := by
  have hMS : movingCore d c.B7 s ≤ d.S :=
    (le_normalizer_iff_commutator_le_left.mp (c.normalizes_coreCentralizer d B s hs)).trans inf_le_left
  intro x hx y hy hxV hyV
  let xS : d.S := ⟨x,hMS hx⟩
  let yS : d.S := ⟨y,hMS hy⟩
  have hx0 : (d.ru1.steinberg.coordinates xS).toAdd ≠ 0 :=
    fun he => hxV ((d.ru1.steinberg.coordinates_eq_one_iff xS).mp he)
  have hy0 : (d.ru1.steinberg.coordinates yS).toAdd ≠ 0 :=
    fun he => hyV ((d.ru1.steinberg.coordinates_eq_one_iff yS).mp he)
  obtain ⟨h,hh,he⟩ := (c.centralizerImage_fiveSpace d B hB hfull s hs hs1).2.2.2.2
    _ (c.movingCore_coordinates_mem d B s xS hx) hx0
    _ (c.movingCore_coordinates_mem d B s yS hy) hy0
  obtain ⟨a,ha⟩ := hh
  let l := inclusion c.le_L a
  let z : d.S := ⟨(a : G) * x * (a : G)⁻¹,
    (mem_normalizer_iff.mp (d.ru1.steinberg.normalized l.property) x).mp xS.property⟩
  have hc : d.ru1.steinberg.coordinates z = d.ru1.steinberg.coordinates yS := by
    apply Multiplicative.toAdd.injective
    apply (d.ru1.steinberg.equivariant l xS).trans
    change BinaryLinearThree.S (modelMap d c.B7 c.le_L a) _ = _
    rw [ha]
    exact he
  refine ⟨a,a.property,?_⟩
  apply (d.ru1.steinberg.coordinates_eq_one_iff (z⁻¹ * yS)).mp
  rw [map_mul, map_inv, hc]
  exact inv_mul_cancel _

end
end CFSG.Quasithin.ChapterJ.SpecialCore
