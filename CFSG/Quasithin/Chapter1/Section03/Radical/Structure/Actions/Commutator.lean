module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Assembly
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection

/-!
# A nonsolvable subgroup generates each radical factor by commutators

Let I belong to the local component family for R, and let a nonsolvable
subgroup B of I be normalized by R. For every odd Fitting prime in the
nonquasisimple A.3.6 alternatives, [Ξ_p(I),B] = Ξ_p(I).

The faithful quaternion action from R ∩ I makes the I-action on the
radical Frattini quotient nontrivial. Its proper kernel is solvable by
C-component minimality, so B acts nontrivially. The image of [Ξ_p(I),B]
is R-invariant and therefore fills the irreducible Frattini quotient.
Frattini nongeneration and two-perfectness remove the remaining two-core.

Source: Aschbacher–Smith, A.3.3(1), pp.41–42, the radical actions in 1.3.3,
p.509, and the concluding commutator assertion in 9.4.1, p.736.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter1.Section02

namespace CFSG.Quasithin.Chapter1.RadicalActions

private theorem action_subgroup
    {G : Type*} [Group G] {U V X : Subgroup G}
    (hUV : U ≤ V) (hV : V ≤ normalizer X) (u : U) (x : XiFrattiniQuotient X) :
    xiFrattiniAction U X (hUV.trans hV) u x =
      xiFrattiniAction V X hV (inclusion hUV u) x := by
  induction x using QuotientGroup.induction_on with | H x =>
    induction x using QuotientGroup.induction_on with | H x => rfl

private theorem commutator_eq_of_irreducible_normalizer
    {G : Type*} [Group G] [Finite G] (X R B : Subgroup G)
    (hRX : R ≤ normalizer X) (hRB : R ≤ normalizer B)
    (hBX : B ≤ normalizer X) (hX : IsPPerfect 2 X)
    (hmove : xiFrattiniAction B X hBX ≠ 1)
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient X),
      (∀ r : R, ∀ a ∈ A, xiFrattiniAction R X hRX r a ∈ A) →
        A = ⊥ ∨ A = ⊤) : ⁅X, B⁆ = X := by
  let D := ⁅X, B⁆.subgroupOf X
  let q := QuotientGroup.mk' (pCore 2 X)
  let f := (QuotientGroup.mk' (frattini (XiQuotient X))).comp q
  have hRD : R ≤ normalizer (⁅X, B⁆ : Subgroup G) := by
    intro r hr
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hRX hr),
      mem_normalizer_iff_map_conj_eq.mp (hRB hr)]
  have he {S : Subgroup G} (hS : S ≤ normalizer X) (s : S) (x : X) :
      let _ := conjMulDistribMulActionOfLeNormalizer S X hS
      xiFrattiniAction S X hS s (f x) =
        f (s • x) := by
    let _ := conjMulDistribMulActionOfLeNormalizer S X hS
    simp only [xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk, f, q]
    rfl
  let _ := conjMulDistribMulActionOfLeNormalizer R X hRX
  have hstable : ∀ r : R, ∀ a ∈ D.map f,
      xiFrattiniAction R X hRX r a ∈ D.map f := by
    rintro r a ⟨x, hx, rfl⟩
    refine ⟨r • x, ?_, (he hRX r x).symm⟩
    exact (mem_normalizer_iff.mp (hRD r.property) x).mp hx
  have himage : D.map f = ⊤ := by
    rcases hirr (D.map f) hstable with hb | ht
    · exfalso
      apply hmove
      ext b : 1
      apply MulEquiv.ext
      intro a
      obtain ⟨x, rfl⟩ := ((QuotientGroup.mk'_surjective _).comp
        (QuotientGroup.mk'_surjective _)) a
      let _ := conjMulDistribMulActionOfLeNormalizer B X hBX
      change xiFrattiniAction B X hBX b (f x) = f x
      rw [he hBX]
      have hd : (b • x) * x⁻¹ ∈ D := by
        change ⁅(b : G), (x : G)⁆ ∈ ⁅X, B⁆
        rw [commutator_comm]
        exact commutator_mem_commutator b.property x.property
      have hz : f ((b • x) * x⁻¹) = 1 :=
        Subgroup.mem_bot.mp (hb ▸ mem_map_of_mem f hd)
      rw [map_mul, map_inv] at hz
      exact mul_inv_eq_one.mp hz
    · exact ht
  have hqimage : D.map q = ⊤ := by
    apply frattini_nongenerating
    have hm := congrArg (comap (QuotientGroup.mk' (frattini (XiQuotient X)))) himage
    rw [← map_map, comap_map_eq, QuotientGroup.ker_mk', comap_top] at hm
    exact hm
  have hsup : D ⊔ pCore 2 X = ⊤ := by
    have hm := congrArg (comap q) hqimage
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hm
  let : D.Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_left X B)
  have hD : D = ⊤ := hX D inferInstance
    (isPGroup_quotient_of_sup_eq_top D (pCore 2 X) pCore_isPGroup hsup)
  have hm := congrArg (map X.subtype) hD
  simpa only [D, map_subgroupOf_eq_of_le
    (le_normalizer_iff_commutator_le_left.mp hBX),
    ← MonoidHom.range_eq_map, range_subtype] using hm

universe u
variable {G : Type u} [Group G] [Finite G]

/-- An R-invariant nonsolvable subgroup of a local C-component generates
every relevant radical factor by commutators. -/
theorem XiP_commutator_eq_of_nonsolvable_subgroup_of_A36 {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    {R I B : Subgroup G} (hL : I ∈ L G R)
    (hQ : IsSQTK 𝒦 ((I ⊔ R : Subgroup G) ⧸ pCore 2 (I ⊔ R : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient I))
    (hRI : R ≤ normalizer I) (hRB : R ≤ normalizer B)
    (hBI : B ≤ I) (hB : ¬ Group.IsSolvable B)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient I))) :
    ⁅XiP p I, B⁆ = XiP p I := by
  let X := XiP p I
  have hIX : I ≤ normalizer X := XiP_invariant p I.le_normalizer
  let ρ := xiFrattiniAction I X hIX
  have hρ : ρ ≠ 1 := by
    intro ht
    obtain ⟨f, hf⟩ := (XiP_intersection_actions_of_A36 hA36 hL hQ hn ho hd).2
    have hone (x : QuaternionGroup 2) : f x = 1 := by
      apply Subtype.ext
      obtain ⟨r, hr⟩ := (f x).property
      rw [← hr]
      apply MulEquiv.ext
      intro a
      change xiFrattiniAction (R ⊓ I) X (inf_le_right.trans hIX) r a = a
      rw [action_subgroup inf_le_right hIX]
      exact congrArg (fun α : I →* MulAut (XiFrattiniQuotient X) =>
        α (inclusion inf_le_right r) a) ht
    have he := hf ((hone (QuaternionGroup.a 0)).trans (hone (QuaternionGroup.xa 0)).symm)
    exact (show (QuaternionGroup.a 0 : QuaternionGroup 2) ≠ QuaternionGroup.xa 0 by decide) he
  have hI : (⊤ : Subgroup I).IsCComponent := by
    have h := hL.1.subgroupOf le_rfl
    rw [subgroupOf_self] at h
    let e := subgroupOfEquivOfLe (show I ≤ I ⊔ R from le_sup_left)
    have hm := h.map_equiv e
    rwa [map_top_of_surjective e.toMonoidHom e.surjective] at hm
  have hmove : xiFrattiniAction B X (hBI.trans hIX) ≠ 1 := by
    intro hb
    have hB' : ¬ Group.IsSolvable (B.subgroupOf I) := by
      intro hs
      let := hs
      exact hB (Group.isSolvable_of_surjective
        (f := (subgroupOfEquivOfLe hBI).toMonoidHom)
        (subgroupOfEquivOfLe hBI).surjective)
    have hBK : B.subgroupOf I ≤ ρ.ker := by
      intro b hbmem
      apply MonoidHom.mem_ker.mpr
      apply MulEquiv.ext
      intro a
      have he := congrArg (fun α : B →* MulAut (XiFrattiniQuotient X) =>
        α ⟨b, hbmem⟩ a) hb
      rw [action_subgroup hBI hIX] at he
      exact he
    have htop : (⊤ : Subgroup I) ≤ ρ.ker :=
      hI.le_normal_of_nonsolvable_subgroup hB' le_top hBK
    exact hρ (MonoidHom.ker_eq_top_iff.mp (top_unique htop))
  exact commutator_eq_of_irreducible_normalizer X R B
    (XiP_invariant p hRI) hRB (hBI.trans hIX) (XiP_isPPerfect p I)
    hmove (XiP_irreducible_of_A36 hA36 hL hQ hn hRI ho hd)

end CFSG.Quasithin.Chapter1.RadicalActions
