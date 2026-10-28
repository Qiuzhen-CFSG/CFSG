module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourExtraspecial
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import Theory.GroupTheory.TwoCoreOddSylowSupplement
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.Frattini.PGroupMap
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.FixedPlaneExponent
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.OddExponent.LinearReduction

/-!
# Extraspecial centers and prime centralizers at the Hermitian four-space

B.6.8 places the Frattini image of every odd p-group in the maximal
subgroup of a solvable minimal parabolic. This applies to the actual
extraspecial center, since its center equals its Frattini subgroup.

For the Hermitian module over F₄, an odd pointwise stabilizer of the
canonical four-space is a GL₃ congruence of order dividing three.
Consequently a p-group for p > 3 normalizing the original module and
centralizing that four-space centralizes the full module. The transport
retains the literal conjugate-plane marking and conjugation action.

The companion Chapter 12 extension applies these facts to both original
weak-closure branches. Extraspecial radical H-star placement and ambient
odd-normalizer control remain separate premises; these deductions do not
assert quasisimplicity of the containing component.

Source: Aschbacher--Smith B.6.8(2), H.4.6(3), and the extraspecial paragraph
of 8.2.7, printed pp.113--114,382,718, refs/quasithin.pdf (1 March 2004).
The proof-only Structure import exposes its existing core definition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB Chapter1 ChapterE Offenders.Parabolic.Construction

/-- Frattini images of odd p-groups lie in the actual maximal subgroup of a
solvable minimal parabolic. The map need not be injective or surjective. -/
theorem solvable_parabolic_odd_frattini_image
    {H Y : Type*} [Group H] [Finite H] [Group Y] [Finite Y]
    (S : Sylow 2 H) (hP : IsMinimalParabolicOver S ⊤)
    (hsol : Group.IsSolvable H) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hY : IsPGroup p Y) (f : Y →* H) :
    (frattini Y).map f ≤ minimalParabolicMax S hP := by
  let q := QuotientGroup.mk' (pCore 2 H)
  obtain ⟨r,hr,_,hR,_,hF,_⟩ := minimalParabolic_solvable_structure S hP hsol
  let : Fact r.Prime := ⟨hr⟩
  have hle : (q.comp f).range ≤ pCore r (H ⧸ pCore 2 H) := by
    rw [←hR]
    exact odd_prime_subgroup_le_twoResidual ho _ (hY.of_surjective _ (q.comp f).rangeRestrict_surjective)
  have hphi : (frattini Y).map (q.comp f) ≤ minimalParabolicCoreImage S hP := by
    by_cases hpr : p = r
    · subst r
      let g : Y →* pCore p (H ⧸ pCore 2 H) := (q.comp f).codRestrict _
        (fun y => hle ⟨y,rfl⟩)
      let : Fact (IsPGroup p Y) := ⟨hY⟩
      let : Fact (IsPGroup p (pCore p (H ⧸ pCore 2 H))) := ⟨pCore_isPGroup⟩
      have hh := map_mono (f := (pCore p (H ⧸ pCore 2 H)).subtype)
        (frattini_map_le_of_isPGroup (p := p) g)
      rw [map_map] at hh
      rw [hF]
      exact hh
    · have hdis := IsPGroup.disjoint_of_ne p r hpr (q.comp f).range
        (pCore r (H ⧸ pCore 2 H))
        (hY.of_surjective _ (q.comp f).rangeRestrict_surjective) pCore_isPGroup
      have hh : (q.comp f).range = ⊥ := bot_unique (fun x hx => hdis.le_bot ⟨hx,hle hx⟩)
      exact (map_le_range _ _).trans (hh.le.trans bot_le)
  have hcore : (frattini Y).map f ≤ minimalParabolicCore S hP := by
    have hh := map_le_iff_le_comap.mp (show ((frattini Y).map f).map q ≤
      (minimalParabolicCore S hP).map q by rw [map_map]; exact hphi)
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',
      sup_eq_left.mpr (minimalParabolicTwoCore_le_core S hP)] using hh
  exact hcore.trans (normalCore_le _)

/-- B.6.8 places the actual extraspecial center in M, with the literal
minimal-parabolic marking of H retained. -/
theorem extraspecial_center_le_of_solvable_parabolic
    {G : Type*} [Group G] [Finite G] {κ : GroupClass}
    {H T M V Y : Subgroup G} (h28 : HypothesisE28 κ H T M V)
    (hsol : Group.IsSolvable H) (hYH : Y ≤ H)
    {p : ℕ} [Fact p.Prime] [IsExtraspecial p Y] (ho : Odd p) :
    (center Y).map Y.subtype ≤ M := by
  obtain ⟨S,_,hP,hM⟩ := h28.minimal
  have hh := solvable_parabolic_odd_frattini_image S hP hsol ho
    (IsExtraspecial.isPGroup p Y) (inclusion hYH)
  rw [←hM,IsExtraspecial.frattini_eq_center (p := p)] at hh
  rintro y ⟨z,hz,rfl⟩
  exact hh (mem_map_of_mem (inclusion hYH) hz)

private theorem field_one_scalar (a : F 1) : a = 0 ∨ a = 1 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    let : Fintype (F 1) := Fintype.ofFinite _
    have hh := FiniteField.pow_card_sub_one_eq_one a ha
    have hc : Fintype.card (F 1) = 2 := by
      rw [←Nat.card_eq_fintype_card,card_F]
      rfl
    simpa only [hc,show 2-1 = 1 by decide,pow_one] using hh

/-- Every odd pointwise stabilizer of the marked four-space in the full
binary normalizer has order dividing three. -/
theorem field_four_plane_odd_order_dvd_three
    (a : binaryNormalizer 1) (ho : Odd (orderOf a))
    (hf : ∀ v ∈ fixedSpace (UnipotentRadicals.ambientAction 1)
      (UnipotentRadicals.plane 1), a.val v = v) : orderOf a ∣ 3 := by
  have ho' : Odd (orderOf a.val) := by rwa [Subgroup.orderOf_coe]
  have hl : ParabolicTorus.IsFixedFieldLinear 1 a.val := by
    intro c v
    rcases field_one_scalar c with rfl | rfl <;> simp
  obtain ⟨g,hg⟩ := ParabolicTorus.OddExponent.mem_congruenceImage_of_odd_of_isFixedFieldLinear
    1 a.val a.property ho' hl
  have hd := ParabolicTorus.plane_fixed_odd_order_dvd 1 g (hg.symm ▸ hf) (hg.symm ▸ ho')
  rw [hg,Subgroup.orderOf_coe] at hd
  norm_num at hd ⊢
  exact hd

/-- An odd p-subgroup, p > 3, fixing the marked four-space and normalizing
V fixes all of V. This is a statement about the original conjugation action. -/
theorem field_four_prime_centralizer
    {G : Type*} [Group G] [Finite G] (V U Z : Subgroup G)
    [IsElementaryAbelian 2 V]
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (j : Automizer V →* binaryNormalizer 1) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction 1 (binaryNormalizer 1) (j a) (e v))
    (hmark : ∀ v : Additive V, (v.toMul : G) ∈ U ↔
      e v ∈ fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hZ : IsPGroup p Z)
    (hZN : Z ≤ normalizer (V : Set G)) (hZU : Z ≤ centralizer (U : Set G)) :
    Z ≤ centralizer (V : Set G) := by
  let f : Z →* Automizer V := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hZN)
  have hodd : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hcop : Nat.Coprime p 3 := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by decide) hp)
  intro z hz
  let z' : Z := ⟨z,hz⟩
  have hord : orderOf (j (f z')) ∣ orderOf z' := orderOf_map_dvd (j.comp f) z'
  have ho : Odd (orderOf (j (f z'))) :=
    (hZ.orderOf_coprime hodd.coprime_two_right z').odd_of_right.of_dvd_nat hord
  have hf : ∀ w ∈ fixedSpace (UnipotentRadicals.ambientAction 1)
      (UnipotentRadicals.plane 1), (j (f z')).val w = w := by
    intro w hw
    obtain ⟨v,rfl⟩ := e.surjective w
    change overgroupAction 1 (binaryNormalizer 1) (j (f z')) (e v) = e v
    rw [←he]
    apply congrArg e
    apply Additive.toMul.injective
    apply Subtype.ext
    change z * (v.toMul : G) * z⁻¹ = (v.toMul : G)
    rw [←(hZU hz) _ ((hmark v).mpr hw),mul_assoc,mul_inv_cancel,mul_one]
  have hja : j (f z') = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hZ.orderOf_coprime hcop z') hord
      (field_four_plane_odd_order_dvd_three _ ho hf))
  have hfa : f z' = 1 := hj (hja.trans (map_one j).symm)
  intro v hv
  have hh := congrArg (fun a : Automizer V => (a.val ⟨v,hv⟩ : G)) hfa
  change z*v*z⁻¹=v at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The prime centralizer bound transported through the actual conjugate
plane marking of an actor on V. -/
theorem field_four_prime_centralizer_at_actor
    {G : Type*} [Group G] [Finite G] (V P Z : Subgroup G)
    [IsElementaryAbelian 2 V]
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (j : Automizer V →* binaryNormalizer 1) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction 1 (binaryNormalizer 1) (j a) (e v))
    (hP : P ≤ normalizer (V : Set G))
    (c : Cover 1) (hc : ((inducedAutomizer V P).map
      ((binaryNormalizer 1).subtype.comp j)).map
        (MulAut.conj (binaryActionHom 1 c)).toMonoidHom = UnipotentRadicals.plane 1)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hZ : IsPGroup p Z)
    (hZN : Z ≤ normalizer (V : Set G))
    (hZU : Z ≤ centralizer (V ⊓ centralizer (P : Set G) : Set G)) :
    Z ≤ centralizer (V : Set G) := by
  let z := binaryActionHom 1 c
  let zN : binaryNormalizer 1 := ⟨z,(binaryImage 1).le_normalizer ⟨c,rfl⟩⟩
  let j' := (MulAut.conj zN).toMonoidHom.comp j
  let e' := e.trans z
  let l := (binaryNormalizer 1).subtype.comp j'
  have hl (a : Automizer V) (v : Additive V) :
      e' (automizerRepresentation V a v) = l a (e' v) := by
    change z (e (automizerRepresentation V a v)) = z ((j a).val (z.symm (z (e v))))
    rw [z.symm_apply_apply]
    exact congrArg z (he a v)
  have him : (inducedAutomizer V P).map l = UnipotentRadicals.plane 1 := by
    change (inducedAutomizer V P).map
      ((MulAut.conj z).toMonoidHom.comp ((binaryNormalizer 1).subtype.comp j)) = _
    rw [←map_map]
    exact hc
  apply field_four_prime_centralizer V (V ⊓ centralizer (P : Set G)) Z
    e' j' ((MulAut.conj zN).injective.comp hj) hl ?_ hp hZ hZN hZU
  intro v
  constructor
  · intro hv
    have hfix := (mem_fixedSpace_inducedAutomizer V P hP v).mpr hv.2
    intro a
    have ha : a.val ∈ (inducedAutomizer V P).map l := by rw [him]; exact a.property
    obtain ⟨x,hx,hxa⟩ := ha
    change a.val (e' v) = e' v
    rw [←hxa,←hl]
    exact congrArg e' (hfix ⟨x,hx⟩)
  · intro hv
    refine ⟨v.toMul.property,?_⟩
    apply (mem_fixedSpace_inducedAutomizer V P hP v).mp
    intro a
    apply e'.injective
    change e' (automizerRepresentation V a.val v) = e' v
    rw [hl]
    exact hv ⟨l a.val,him ▸ mem_map_of_mem l a.property⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
