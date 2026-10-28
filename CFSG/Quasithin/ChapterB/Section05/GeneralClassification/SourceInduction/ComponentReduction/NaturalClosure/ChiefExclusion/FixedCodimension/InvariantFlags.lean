module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FixedCodimension.Basic
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.SimpleHeadQuotient
public import Mathlib.Order.OrderIsoNat

/-!
# Adapted invariant chief flags in the natural-component configuration

The two actual component projections express every element of A as a product
of its L-coordinate and a central involution of LA. A normal cyclic two-subgroup
acts trivially on any simple binary LA-module. Consequently A acts there as its
L-projection, so every simple LA-section remains simple upon restriction to L.

Finite-dimensionality gives saturated chains in the lattice of actual
LA-subrepresentations. Restricting their terms to L therefore gives the required
A-stable L-chief flags, with the literal successive quotient actions. Joining
chains below and above a prescribed LA-subrepresentation gives a flag of V
through that subrepresentation. Both constructions are applied to the actual
fixed space C_V(A ∩ C_G(L)). No constituent classification or codimension estimate
is required; the given second component already supplies the projections.

The cover-to-quotient argument is adapted from
`MathieuCode.Hexad.ChiefFlag.Actions.irreducible_section_of_covBy` in
`Theory/Representation/MathieuCodeRestriction/M22/LocalStructure/Hexad/ChiefFlag/Actions/Sections.lean`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, the chief series used in (!) and (!!).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem simple_action_eq_left [Finite G]
    {A L M : Subgroup G} (p : ComponentProjections A L M)
    (hc : L ≤ centralizer (M : Set G)) (hA : IsElementaryAbelian 2 A)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (τ : Representation (ZMod 2) ↥(L ⊔ A) W) [IsIrreducible τ] (a : A) :
    τ (Subgroup.inclusion le_sup_right a) = τ (Subgroup.inclusion le_sup_left (p.left a)) := by
  let : IsElementaryAbelian 2 A := hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  let j : L →* ↥(L ⊔ A) := Subgroup.inclusion le_sup_left
  let k : A →* ↥(L ⊔ A) := Subgroup.inclusion le_sup_right
  let c := (j (p.left a))⁻¹ * k a
  have hcval : (c : G) = p.right a := by
    change (p.left a : G)⁻¹ * a = p.right a
    rw [← p.multiply a, inv_mul_cancel_left]
  have hcpow : c ^ 2 = 1 := by
    apply Subtype.ext
    change (c : G) ^ 2 = 1
    rw [hcval]
    have ha : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a
    have hr : (p.right a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
    exact congrArg (fun x : M => (x : G)) hr
  have hcent : c ∈ center ↥(L ⊔ A) := by
    have hl : L ≤ centralizer ({(p.right a : G)} : Set G) := by
      intro l hl r hr
      rw [Set.mem_singleton_iff.mp hr]
      exact hc hl (p.right a) (p.right a).property
    have ha : A ≤ centralizer ({(p.right a : G)} : Set G) := by
      intro b hb r hr
      have hbval : (p.left ⟨b, hb⟩ : G) * (p.right ⟨b, hb⟩ : G) = b := p.multiply ⟨b, hb⟩
      rw [Set.mem_singleton_iff.mp hr, ← hbval]
      have hleft : Commute (p.right a : G) (p.left ⟨b, hb⟩ : G) :=
        hc (p.left ⟨b, hb⟩).property (p.right a) (p.right a).property
      have hright : Commute (p.right a : G) (p.right ⟨b, hb⟩ : G) := by
        change (p.right a : G) * (p.right ⟨b, hb⟩ : G) = _
        have he := congrArg (fun x : A => (p.right x : G)) (mul_comm a ⟨b, hb⟩)
        simpa only [map_mul, Subgroup.coe_mul] using he
      exact (hleft.mul_right hright).eq
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    change (x : G) * c = (c : G) * x
    rw [hcval]
    exact ((sup_le hl ha) x.property _ (Set.mem_singleton _)).symm
  let : (zpowers c).Normal := ⟨fun z hz x => by
    have hzcent := (zpowers_le.mpr hcent) hz
    have he := mem_center_iff.mp hzcent x
    simpa only [he, mul_inv_cancel_right] using hz⟩
  have hp : IsPGroup 2 (zpowers c) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one hcpow).isPGroup 2 _
  have hker := normal_p_subgroup_le_ker τ (zpowers c) hp (mem_zpowers c)
  have he : τ c = 1 := hker
  have ha : k a = j (p.left a) * c := by dsimp [c]; group
  change τ (k a) = τ (j (p.left a))
  rw [ha, map_mul, he, mul_one]


private theorem simple_restrict_component [Finite G]
    {A L M : Subgroup G} (p : ComponentProjections A L M)
    (hc : L ≤ centralizer (M : Set G)) (hA : IsElementaryAbelian 2 A)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (τ : Representation (ZMod 2) ↥(L ⊔ A) W) [IsIrreducible τ] :
    IsIrreducible (τ.comp (Subgroup.inclusion (show L ≤ L ⊔ A from le_sup_left))) := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial τ
  refine ⟨?_⟩
  intro S
  have hl : L.subgroupOf (L ⊔ A) ≤ subspaceStabilizer τ S.toSubmodule := by
    apply le_subspaceStabilizer
    intro l hl v hv
    exact S.apply_mem_toSubmodule ⟨l.val, hl⟩ hv
  have ha : A.subgroupOf (L ⊔ A) ≤ subspaceStabilizer τ S.toSubmodule := by
    apply le_subspaceStabilizer
    intro a ha v hv
    have he := simple_action_eq_left p hc hA τ ⟨a.val, ha⟩
    change τ a v ∈ S.toSubmodule
    rw [show τ a = τ (Subgroup.inclusion le_sup_left (p.left ⟨a.val, ha⟩)) from he]
    exact S.apply_mem_toSubmodule (p.left ⟨a.val, ha⟩) hv
  have hgen : L.subgroupOf (L ⊔ A) ⊔ A.subgroupOf (L ⊔ A) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (show L ≤ L ⊔ A from le_sup_left)
      (show A ≤ L ⊔ A from le_sup_right), Subgroup.subgroupOf_self]
  let T : Subrepresentation τ := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule g v hv := by
      have ht := sup_le hl ha
      rw [hgen] at ht
      exact (ht (Subgroup.mem_top g) v).2 hv }
  rcases eq_bot_or_eq_top T with he | he
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation τ => U.toSubmodule) he))
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation τ => U.toSubmodule) he))

-- Adapted from MathieuCode.Hexad.ChiefFlag.Actions.irreducible_section_of_covBy,
-- with the BinaryOffender literal section convention.
private theorem chief_section {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    (τ : Representation (ZMod 2) H X) {U W : Subrepresentation τ} (h : U ⋖ W) :
    IsIrreducible (sectionRepresentation τ U W) := by
  apply SimpleHeadQuotient.irreducible_quotient_of_isCoatom
  refine ⟨?_, ?_⟩
  · intro he
    have hWU : W ≤ U := by
      intro v hv
      have hm : (⟨v, hv⟩ : W.toSubmodule) ∈ sectionLower τ U W := by rw [he]; trivial
      exact hm
    exact (not_le_of_gt h.lt) hWU
  · intro P hP
    let T : Subrepresentation τ := {
      toSubmodule := P.toSubmodule.map W.toSubmodule.subtype
      apply_mem_toSubmodule g := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨W.toRepresentation g v, P.apply_mem_toSubmodule g hv, rfl⟩ }
    have hUT : U ≤ T := by
      intro v hv
      exact ⟨⟨v, h.le hv⟩, hP.le hv, rfl⟩
    have hTW : T ≤ W := Submodule.map_subtype_le _ _
    rcases h.eq_or_eq hUT hTW with ht | ht
    · have hPN : P ≤ sectionLower τ U W := by
        intro v hv
        have : v.val ∈ T := ⟨v, hv, rfl⟩
        rw [ht] at this
        exact this
      exact ((not_le_of_gt hP) hPN).elim
    · apply Subrepresentation.toSubmodule_injective
      apply top_unique
      intro v _
      have : v.val ∈ T := by rw [ht]; exact v.property
      obtain ⟨w, hw, he⟩ := this
      exact (Subtype.ext he : w = v) ▸ hw


private theorem saturated_chain {α : Type*} [PartialOrder α] [Finite α]
    {x y : α} (hxy : x ≤ y) :
    ∃ (n : ℕ) (c : ℕ → α), Monotone c ∧ c 0 = x ∧ c n = y ∧
      ∀ i < n, c i ⋖ c (i + 1) := by
  obtain ⟨a, ha, n, hn, hc⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le hxy
  let c : ℕ → α := fun i => a (min i n)
  have hmono : Monotone c := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases hi : i < n
    · simpa only [c, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left hi]
        using (hc i hi).le
    · have hni : n ≤ i := by omega
      simp only [c, Nat.min_eq_right hni, Nat.min_eq_right (hni.trans (Nat.le_succ i))]
      exact le_rfl
  refine ⟨n, c, hmono, ?_, ?_, ?_⟩
  · simpa [c] using ha
  · simpa [c] using hn
  · intro i hi
    simpa only [c, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left hi] using hc i hi

private theorem saturated_chain_through {α : Type*} [PartialOrder α] [Finite α]
    {x z y : α} (hxz : x ≤ z) (hzy : z ≤ y) :
    ∃ (n : ℕ) (c : ℕ → α), Monotone c ∧ c 0 = x ∧ c n = y ∧
      (∀ i < n, c i ⋖ c (i + 1)) ∧ ∃ r ≤ n, c r = z := by
  classical
  obtain ⟨n, a, hma, ha0, han, hca⟩ := saturated_chain hxz
  obtain ⟨m, b, hmb, hb0, hbm, hcb⟩ := saturated_chain hzy
  let c : ℕ → α := fun i => if i ≤ n then a i else b (i - n)
  have hleft (i) (hi : i ≤ n) : c i = a i := if_pos hi
  have hright (i) (hi : n ≤ i) : c i = b (i - n) := by
    by_cases he : i = n
    · subst i
      simp [c, han, hb0]
    · exact if_neg (by omega)
  have hmono : Monotone c := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases hi : i < n
    · rw [hleft i (by omega), hleft (i + 1) hi]
      exact hma (Nat.le_succ i)
    · rw [hright i (by omega), hright (i + 1) (by omega)]
      exact hmb (Nat.sub_le_sub_right (Nat.le_succ i) n)
  refine ⟨n + m, c, hmono, ?_, ?_, ?_, n, by omega, hleft n le_rfl |>.trans han⟩
  · rw [hleft 0 (Nat.zero_le n), ha0]
  · rw [hright (n + m) (by omega), Nat.add_sub_cancel_left, hbm]
  · intro i hi
    by_cases hin : i < n
    · rw [hleft i (by omega), hleft (i + 1) hin]
      exact hca i hin
    · rw [hright i (by omega), hright (i + 1) (by omega),
        show i + 1 - n = (i - n) + 1 by omega]
      exact hcb (i - n) (by omega)

private def restrictToComponent {A L : Subgroup G}
    (S : Subrepresentation (ρ.comp (L ⊔ A).subtype)) :
    Subrepresentation (ρ.comp L.subtype) where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule l _ hv := S.apply_mem_toSubmodule (Subgroup.inclusion le_sup_left l) hv

private noncomputable def flagOfChain [Finite G] [Module.Finite (ZMod 2) V]
    {A L M : Subgroup G} (p : ComponentProjections A L M)
    (hc : L ≤ centralizer (M : Set G)) (hA : IsElementaryAbelian 2 A)
    (n : ℕ) (c : ℕ → Subrepresentation (ρ.comp (L ⊔ A).subtype))
    (hm : Monotone c) (h0 : c 0 = ⊥)
    (hcov : ∀ i < n, c i ⋖ c (i + 1))
    (S : Submodule (ZMod 2) V) (hn : (c n).toSubmodule = S) :
    InvariantChiefFlag ρ A L S where
  length := n
  term i := restrictToComponent ρ (c i)
  monotone := fun _ _ hij => hm hij
  start := Subrepresentation.toSubmodule_injective
    (congrArg (fun T : Subrepresentation (ρ.comp (L ⊔ A).subtype) => T.toSubmodule) h0)
  stop := hn
  stable i := le_subspaceStabilizer ρ _ (fun a ha _ hv =>
    (c i).apply_mem_toSubmodule ⟨a, (show A ≤ L ⊔ A from le_sup_right) ha⟩ hv)
  chief i hi := by
    let τ := sectionRepresentation (ρ.comp (L ⊔ A).subtype) (c i) (c (i + 1))
    let : IsIrreducible τ := chief_section _ (hcov i hi)
    exact simple_restrict_component p hc hA τ

/-- Every LA-subrepresentation has an exhaustive A-stable L-chief flag. -/
theorem exists_invariantChiefFlag [Finite G]
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (hL : IsComponent G L) (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    (S : Subrepresentation (ρ.comp (L ⊔ A).subtype)) :
    Nonempty (InvariantChiefFlag ρ A L S.toSubmodule) := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Subrepresentation (ρ.comp (L ⊔ A).subtype)) := Finite.of_injective
    (fun T : Subrepresentation (ρ.comp (L ⊔ A).subtype) => (T : Set V)) SetLike.coe_injective
  obtain ⟨n, c, hm, h0, hn, hcov⟩ := saturated_chain (show ⊥ ≤ S from bot_le)
  have hc : L ≤ centralizer (d.second : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (hL.commutator_eq_bot_of_ne d.isComponent d.distinct)
  exact ⟨flagOfChain ρ (d.projections ρ s hL) hc setup.minimal.1.1.2 n c hm h0 hcov
    S.toSubmodule (congrArg Subrepresentation.toSubmodule hn)⟩

/-- The exhaustive flag of V can be chosen to pass through any given LA-subrepresentation. -/
theorem exists_invariantChiefFlag_through [Finite G]
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (hL : IsComponent G L) (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L)
    (S : Subrepresentation (ρ.comp (L ⊔ A).subtype)) :
    ∃ f : InvariantChiefFlag ρ A L ⊤, ∃ r ≤ f.length,
      (f.term r).toSubmodule = S.toSubmodule := by
  let : Module.Finite (ZMod 2) V := setup.hypothesis.finite_module
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Subrepresentation (ρ.comp (L ⊔ A).subtype)) := Finite.of_injective
    (fun T : Subrepresentation (ρ.comp (L ⊔ A).subtype) => (T : Set V)) SetLike.coe_injective
  obtain ⟨n, c, hm, h0, hn, hcov, r, hr, hSr⟩ :=
    saturated_chain_through (show ⊥ ≤ S from bot_le) (show S ≤ ⊤ from le_top)
  have hc : L ≤ centralizer (d.second : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (hL.commutator_eq_bot_of_ne d.isComponent d.distinct)
  let f := flagOfChain ρ (d.projections ρ s hL) hc setup.minimal.1.1.2 n c hm h0 hcov
    ⊤ (congrArg Subrepresentation.toSubmodule hn)
  exact ⟨f, r, hr, congrArg Subrepresentation.toSubmodule hSr⟩

/-- The actual fixed space C_V(A ∩ C_G(L)) has an exhaustive invariant chief flag. -/
theorem exists_offenderCentralizerFixed_invariantChiefFlag [Finite G]
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (hL : IsComponent G L) (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L) :
    Nonempty (InvariantChiefFlag ρ A L (fixedSpace ρ (A ⊓ centralizer (L : Set G)))) :=
  exists_invariantChiefFlag ρ setup hL s d
    (offenderCentralizerFixedOver ρ setup.minimal.1.1.2)

/-- Choose the exhaustive invariant chief flag of V through C_V(A ∩ C_G(L)). -/
theorem exists_invariantChiefFlag_through_offenderCentralizerFixed [Finite G]
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (hL : IsComponent G L) (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L) :
    ∃ f : InvariantChiefFlag ρ A L ⊤, ∃ r ≤ f.length,
      (f.term r).toSubmodule = fixedSpace ρ (A ⊓ centralizer (L : Set G)) :=
  exists_invariantChiefFlag_through ρ setup hL s d
    (offenderCentralizerFixedOver ρ setup.minimal.1.1.2)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
