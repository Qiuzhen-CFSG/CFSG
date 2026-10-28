module

public import Theory.Representation.GoldschmidtONan.Consequences
public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Transport
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.GroupTheory.Sylow

/-!
# The Sylow kernel in the O'Nan reduction

Choose a Sylow two-subgroup of the actual stabilizer of the fixed space F.
The odd fixed-space orbit makes it Sylow in the ambient group. If the kernel
of its action on the moved space D were nontrivial, it would contain an
involution t. A nonzero fixed vector on F makes the fixed space of t strictly
larger than D. Conjugating an orbit member W ≤ D to F makes the conjugate of t
fix F pointwise and act nontrivially on D. The regular cyclic image of Y is
normalized by this action. The involution bound in its normalizer, together
with |F|² ≤ |D|, contradicts the strict fixed-space inequality.

Thus the Sylow action on D is faithful. Cyclicity of two-subgroups in the
normalizer of a regular cyclic linear group now makes the Sylow subgroup
cyclic. Both general linear-group facts remain explicit hypotheses; the
source-step assembly must discharge them.

Source: GLS, Number 2, Chapter C, Proposition 14.2, Step 3, first paragraph
and the first sentence of the second paragraph
(`refs/KGroup/GLS2/ChapterC.tex`).
-/

public section

open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
open Module Subgroup
namespace Representation.GoldschmidtONan.OddReduction
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}
local notation "F" => fixedSpace ρ Y
local notation "D" => displacementSpan ρ Y ⊤
local notation "H" => subspaceStabilizer ρ F
local notation "A" => LinearMap.GeneralLinearGroup (ZMod 2) D

private theorem stabilizer_le_moved (h : Input ρ Y) :
    H ≤ subspaceStabilizer ρ D := by
  intro x hx
  exact (mem_subspaceStabilizer_iff_map _ x).mpr
    (h.moved_map_of_fixed_map x ((mem_subspaceStabilizer_iff_map _ x).mp hx))

private noncomputable def movedAction (h : Input ρ Y) : H →* A :=
  (stabilizerRepresentation ρ D).asGroupHom.comp
    (Subgroup.inclusion (stabilizer_le_moved h))

private theorem movedAction_apply (h : Input ρ Y) (x : H) (v : D) :
    ((movedAction h x : Module.End (ZMod 2) D) v : V) = ρ x v := rfl

private theorem actor_le_stabilizer : Y ≤ H := by
  intro y hy
  exact (mem_subspaceStabilizer_iff_map _ y).mpr (fixed_map_actor ⟨y, hy⟩)

private noncomputable def cyclicImage (h : Input ρ Y) : Subgroup A :=
  (Y.subgroupOf H).map (movedAction h)

private theorem cyclicImage_cyclic (h : Input ρ Y) : IsCyclic (cyclicImage h) := by
  let : IsCyclic Y := h.cyclic
  let : IsCyclic (Y.subgroupOf H) :=
    isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe (actor_le_stabilizer (ρ := ρ) (Y := Y))).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe actor_le_stabilizer).injective
  exact isCyclic_of_surjective _ ((movedAction h).subgroupMap_surjective (Y.subgroupOf H))

private theorem cyclicImage_regular [Finite X] (h : Input ρ Y)
    (v : D) (hv : v ≠ 0) (w : D) (hw : w ≠ 0) :
    ∃! c : cyclicImage h, (c.val : Module.End (ZMod 2) D) v = w := by
  have hv0 : (v : V) ≠ 0 := fun he => hv (Subtype.ext he)
  have hw0 : (w : V) ≠ 0 := fun he => hw (Subtype.ext he)
  obtain ⟨y, hy, hu⟩ := h.regular v v.property hv0 w w.property hw0
  let yH : H := ⟨y, actor_le_stabilizer y.property⟩
  refine ⟨⟨movedAction h yH, ⟨yH, y.property, rfl⟩⟩, Subtype.ext hy, ?_⟩
  rintro ⟨c, x, hx, rfl⟩ hc
  have hx' : ρ (x : X) v = w := congrArg Subtype.val hc
  have he : (⟨x, hx⟩ : Y) = y := hu ⟨x, hx⟩ hx'
  apply Subtype.ext
  change movedAction h x = movedAction h yH
  exact congrArg (movedAction h) (Subtype.ext (congrArg (fun z : Y => (z : X)) he))

private theorem movedAction_normalizes (h : Input ρ Y) (x : H) :
    movedAction h x ∈ normalizer (cyclicImage h : Set A) := by
  let : (Y.subgroupOf H).Normal := normal_in_stabilizer_iff.mp h.normal_in_stabilizer
  apply (Y.subgroupOf H).le_normalizer_map (movedAction h)
  exact ⟨x, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩

private theorem exists_orbit_le_moved [Finite X] (h : Input ρ Y)
    (hsub : SuborbitGeometry ρ Y) (htrans : NonzeroTransitive ρ) :
    ∃ W ∈ fixedOrbit ρ Y, W ≤ D := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.fixed_nontrivial
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.moved_ne_bot
  obtain ⟨x, hx⟩ := htrans f hf0 d hd0
  have hdx : d ∈ (F).map (ρ x) := ⟨f, hf, hx⟩
  have hne : (F).map (ρ x) ≠ F := by
    intro he
    exact hd0 (Submodule.disjoint_def.mp h.split.disjoint d (he ▸ hdx) hd)
  rcases hsub _ ⟨x, rfl⟩ hne with hW | hW
  · exact ⟨_, ⟨x, rfl⟩, hW.1⟩
  · exact False.elim (hd0 (Submodule.disjoint_def.mp hW.1 d hdx hd))

private instance orbitAction : MulAction X (fixedOrbit ρ Y) where
  smul x W := ⟨W.val.map (ρ x), map_mem_fixedOrbit W.property x⟩
  one_smul W := Subtype.ext (orbit_map_one W.val)
  mul_smul x y W := Subtype.ext (orbit_map_mul W.val x y)

private theorem stabilizer_index : (H).index = Nat.card (fixedOrbit ρ Y) := by
  let : MulAction.IsPretransitive X (fixedOrbit ρ Y) := ⟨fun U W => by
    obtain ⟨x, hx⟩ := exists_map_eq_of_mem_fixedOrbit U.property W.property
    exact ⟨x, Subtype.ext hx⟩⟩
  have he : H = MulAction.stabilizer X (⟨F, fixed_mem_fixedOrbit⟩ : fixedOrbit ρ Y) := by
    ext x
    rw [mem_subspaceStabilizer_iff_map]
    change _ ↔ (⟨(F).map (ρ x), _⟩ : fixedOrbit ρ Y) = ⟨F, _⟩
    constructor
    · intro he
      apply Subtype.ext
      exact he
    · intro he
      exact congrArg (fun W : fixedOrbit ρ Y => W.val) he
  rw [he]
  exact MulAction.index_stabilizer_of_transitive X _

private theorem fixed_nonzero_of_involution (t : X) (ht : t ^ 2 = 1)
    (htF : t ∈ H) (hF : F ≠ ⊥) :
    ∃ v ∈ F, v ≠ 0 ∧ ρ t v = v := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF
  by_cases hfix : ρ t v = v
  · exact ⟨v, hv, hv0, hfix⟩
  refine ⟨ρ t v + v, (F).add_mem ((htF v).mpr hv) hv, ?_, ?_⟩
  · intro he
    apply hfix
    have hneg : -v = v := by
      have hvv : v + v = 0 := by
        simpa only [add_smul, one_smul, zero_smul] using
          congrArg (fun c : ZMod 2 => c • v) (by decide : (1 : ZMod 2) + 1 = 0)
      exact neg_eq_of_add_eq_zero_left hvv
    exact (eq_neg_of_add_eq_zero_left he).trans hneg
  · rw [map_add, ← Module.End.mul_apply, ← map_mul, ← pow_two, ht, map_one,
      Module.End.one_apply, add_comm]

private theorem eq_one_of_fixes_both [Finite X] (h : Input ρ Y) (t : X)
    (hF : ∀ v ∈ F, ρ t v = v) (hD : ∀ v ∈ D, ρ t v = v) : t = 1 := by
  apply h.faithful
  ext v
  obtain ⟨f, hf, d, hd, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ F ⊔ D by rw [h.split.sup_eq_top]; trivial)
  simp only [map_add, hF f hf, hD d hd, map_one, Module.End.one_apply]

private theorem fixed_finrank [Finite X] [Finite V] (h : Input ρ Y) (t : H)
    (hF : ∀ v ∈ F, ρ (t : X) v = v) :
    finrank (ZMod 2) (fixedSpace ρ (zpowers (t : X))) =
      finrank (ZMod 2) F + finrank (ZMod 2)
        (fixedSpace (Units.coeHom (Module.End (ZMod 2) D)) (zpowers (movedAction h t))) := by
  let E := fixedSpace (Units.coeHom (Module.End (ZMod 2) D)) (zpowers (movedAction h t))
  let K := fixedSpace ρ (zpowers (t : X))
  have hE (v : E) : ρ (t : X) (v.val : V) = v.val := by
    exact congrArg (fun w : D => (w : V))
      ((mem_fixedSpace_zpowers_iff _ _ _).mp v.property)
  let f : F × E →ₗ[ZMod 2] K :=
    { toFun := fun p => ⟨(p.1 : V) + (p.2.val : V),
        (mem_fixedSpace_zpowers_iff _ _ _).mpr (by
          rw [map_add, hF p.1 p.1.property, hE p.2])⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        change (a.1 : V) + b.1 + ((a.2.val : V) + b.2.val) =
          ((a.1 : V) + a.2.val) + ((b.1 : V) + b.2.val)
        abel
      map_smul' := by
        intro c a
        apply Subtype.ext
        exact (smul_add c (a.1 : V) (a.2.val : V)).symm }
  have hinj : Function.Injective f := by
    intro a b he
    have hab : (a.1 : V) + (a.2.val : V) = (b.1 : V) + (b.2.val : V) :=
      congrArg Subtype.val he
    have heq : (a.1 : V) - b.1 = (b.2.val : V) - a.2.val := by
      apply sub_eq_sub_iff_add_eq_add.mpr
      simpa only [add_comm] using hab
    have hz := Submodule.disjoint_def.mp h.split.disjoint _
      ((F).sub_mem a.1.property b.1.property)
      (heq ▸ (D).sub_mem b.2.val.property a.2.val.property)
    have h1 : a.1 = b.1 := Subtype.ext (sub_eq_zero.mp hz)
    have h2 : a.2 = b.2 := Subtype.ext (Subtype.ext (by
      simpa only [h1, add_right_inj] using hab))
    exact Prod.ext h1 h2
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      (show (v : V) ∈ F ⊔ D by rw [h.split.sup_eq_top]; trivial)
    have hbfix : ρ (t : X) b = b := by
      have hv := (mem_fixedSpace_zpowers_iff ρ (t : X) v).mp v.property
      rw [← hab, map_add, hF a ha, add_right_inj] at hv
      exact hv
    refine ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, ?_⟩), Subtype.ext hab⟩
    exact (mem_fixedSpace_zpowers_iff _ _ _).mpr (Subtype.ext hbfix)
  have he := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_prod] at he
  exact he.symm

private theorem involution_not_in_kernel [Finite X] [Finite V] (h : Input ρ Y)
    (hsub : SuborbitGeometry ρ Y) (hgeom : TransitiveGeometry ρ Y)
    (hbound : ∀ (C : Subgroup A) (t : A), IsCyclic C →
      (∀ v : D, v ≠ 0 → ∀ w : D, w ≠ 0 →
        ∃! c : C, (c.val : Module.End (ZMod 2) D) v = w) →
      t ≠ 1 → t ^ 2 = 1 → t ∈ normalizer (C : Set A) →
      Nat.card (fixedSpace (Units.coeHom (Module.End (ZMod 2) D)) (zpowers t)) ^ 2 ≤
        Nat.card D)
    (t : X) (htF : t ∈ H) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (htD : ∀ v ∈ D, ρ t v = v) : False := by
  obtain ⟨W, hW, hWD⟩ := exists_orbit_le_moved h hsub hgeom.1
  obtain ⟨x, hx⟩ := exists_map_eq_of_mem_fixedOrbit hW (fixed_mem_fixedOrbit (ρ := ρ) (Y := Y))
  let q : X := (MulAut.conj x) t
  have hqfix : ∀ v ∈ F, ρ q v = v := by
    intro v hv
    rw [← hx] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    change ρ (x * t * x⁻¹) (ρ x w) = ρ x w
    have hinv : ρ x⁻¹ (ρ x w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    simp only [map_mul, Module.End.mul_apply, hinv, htD w (hWD hw)]
  have hqH : q ∈ H := by
    apply (mem_subspaceStabilizer_iff_map F q).mpr
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      rwa [hqfix v hv]
    · intro v hv
      exact ⟨v, hv, hqfix v hv⟩
  let qH : H := ⟨q, hqH⟩
  have hq1 : q ≠ 1 := by
    intro he
    apply ht1
    exact (MulAut.conj x).injective (he.trans (map_one _).symm)
  have hq2 : qH ^ 2 = 1 := Subtype.ext (by
    change (MulAut.conj x t) ^ 2 = 1
    rw [← map_pow, ht2, map_one])
  have hu1 : movedAction h qH ≠ 1 := by
    intro he
    apply hq1
    apply eq_one_of_fixes_both h q hqfix
    intro v hv
    have hh := congrArg (fun u : A => ((u : Module.End (ZMod 2) D) ⟨v, hv⟩ : V)) he
    exact hh
  have hb := hbound (cyclicImage h) (movedAction h qH) (cyclicImage_cyclic h)
    (cyclicImage_regular h) hu1 (by rw [← map_pow, hq2, map_one])
    (movedAction_normalizes h qH)
  -- Convert the two square cardinality bounds to dimension bounds.
  have hbdim : 2 * finrank (ZMod 2)
      (fixedSpace (Units.coeHom (Module.End (ZMod 2) D)) (zpowers (movedAction h qH))) ≤
      finrank (ZMod 2) D := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      ← pow_mul, Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at hb
    omega
  have hFdim : 2 * finrank (ZMod 2) F ≤ finrank (ZMod 2) D := by
    have hc := hgeom.2.2
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      ← pow_mul, Nat.pow_le_pow_iff_right (by decide : 1 < 2)] at hc
    omega
  have hdim := fixed_finrank h qH hqfix
  have hconj : finrank (ZMod 2) (fixedSpace ρ (zpowers t)) =
      finrank (ZMod 2) (fixedSpace ρ (zpowers q)) := by
    have he := (fixedSpaceConjEquiv ρ (zpowers t) x).finrank_eq
    rwa [MonoidHom.map_zpowers] at he
  -- Before conjugation, the kernel involution fixes D and a nonzero vector of F.
  have hlt : D < fixedSpace ρ (zpowers t) := by
    refine lt_of_le_of_ne ?_ ?_
    · intro v hv
      exact (mem_fixedSpace_zpowers_iff _ _ _).mpr (htD v hv)
    · intro he
      obtain ⟨v, hvF, hv0, hvfix⟩ := fixed_nonzero_of_involution t ht2 htF h.fixed_nontrivial
      have hvD : v ∈ D := by
        rw [he]
        exact (mem_fixedSpace_zpowers_iff _ _ _).mpr hvfix
      exact hv0 (Submodule.disjoint_def.mp h.split.disjoint v hvF hvD)
  have hstrict := Submodule.finrank_lt_finrank_of_lt hlt
  change finrank (ZMod 2) (fixedSpace ρ (zpowers q)) = _ at hdim
  omega


/-- The cyclic Sylow conclusion of Step 3, conditional only on two facts about
normalizers of regular cyclic linear groups on the actual moved space. -/
theorem exists_cyclic_sylow_of_normalizer_facts [Finite X] [Finite V]
    (h : Input ρ Y) (hsub : SuborbitGeometry ρ Y) (hgeom : TransitiveGeometry ρ Y)
    (hcyclic : ∀ C P : Subgroup A, IsCyclic C →
      (∀ v : D, v ≠ 0 → ∀ w : D, w ≠ 0 →
        ∃! c : C, (c.val : Module.End (ZMod 2) D) v = w) →
      IsPGroup 2 P → P ≤ normalizer (C : Set A) → IsCyclic P)
    (hbound : ∀ (C : Subgroup A) (t : A), IsCyclic C →
      (∀ v : D, v ≠ 0 → ∀ w : D, w ≠ 0 →
        ∃! c : C, (c.val : Module.End (ZMod 2) D) v = w) →
      t ≠ 1 → t ^ 2 = 1 → t ∈ normalizer (C : Set A) →
      Nat.card (fixedSpace (Units.coeHom (Module.End (ZMod 2) D)) (zpowers t)) ^ 2 ≤
        Nat.card D) :
    ∃ S : Sylow 2 X, IsCyclic S := by
  classical
  let S : Sylow 2 H := Sylow.nonempty.some
  let f : S →* A := (movedAction h).comp (S : Subgroup H).subtype
  -- The relative action kernel is a two-group, so a nontrivial kernel has an involution.
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    by_contra hk
    obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hk
    have hp : IsPGroup 2 f.ker := S.isPGroup'.of_injective f.ker.subtype
      f.ker.subtype_injective
    have hdvd : 2 ∣ Nat.card f.ker :=
      (hp.dvd_orderOf hs1).trans (orderOf_dvd_natCard s)
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 hdvd
    have ht1 : t ≠ 1 := by
      intro he
      simp only [he, orderOf_one] at ht
      omega
    let tx : X := t.val.val.val
    have htx1 : tx ≠ 1 := by
      intro he
      exact ht1 (Subtype.ext (Subtype.ext (Subtype.ext he)))
    have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
    have htx2 : tx ^ 2 = 1 := congrArg (fun a : f.ker => (a.val.val.val : X)) ht2
    have htD : ∀ v ∈ D, ρ tx v = v := by
      intro v hv
      have he : f t.val = 1 := t.property
      exact congrArg (fun a : A => ((a : Module.End (ZMod 2) D) ⟨v, hv⟩ : V)) he
    exact involution_not_in_kernel h hsub hgeom hbound tx t.val.val.property htx1 htx2 htD
  -- Use the actual image of Y and the actual faithful Sylow image on D.
  have hpimage : IsPGroup 2 f.range :=
    S.isPGroup'.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hnimage : f.range ≤ normalizer (cyclicImage h : Set A) := by
    rintro _ ⟨s, rfl⟩
    exact movedAction_normalizes h s.val
  let : IsCyclic f.range := hcyclic (cyclicImage h) f.range (cyclicImage_cyclic h)
    (cyclicImage_regular h) hpimage hnimage
  let : IsCyclic S := isCyclic_of_injective f.rangeRestrict (by
    intro a b he
    exact hf (congrArg Subtype.val he))
  -- Odd orbit cardinality transfers the stabilizer Sylow subgroup to X.
  let T : Subgroup X := (S : Subgroup H).map (H).subtype
  have hT : IsPGroup 2 T := S.isPGroup'.map (H).subtype
  have hindex : ¬ 2 ∣ T.index := by
    change ¬ 2 ∣ ((S : Subgroup H).map (H).subtype).index
    rw [Subgroup.index_map_subtype, stabilizer_index]
    intro hdvd
    rcases Nat.prime_two.dvd_mul.mp hdvd with hs | ho
    · exact S.not_dvd_index hs
    · exact hgeom.2.1.not_two_dvd_nat ho
  refine ⟨hT.toSylow hindex, ?_⟩
  change IsCyclic T
  exact isCyclic_of_surjective _ ((H).subtype.subgroupMap_surjective (S : Subgroup H))

end Representation.GoldschmidtONan.OddReduction
