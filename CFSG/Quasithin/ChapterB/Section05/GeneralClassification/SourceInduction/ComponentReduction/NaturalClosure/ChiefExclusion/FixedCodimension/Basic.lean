module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FixedQuotient
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.Flags
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The actual offender action and the natural-seed codimension

On any L-irreducible binary LA-section, the centralizer coordinate of the
original elementary offender acts trivially: its displacement commutes with
L and has square zero, so Schur's lemma kills it. Thus the literal A-fixed
codimension equals that of the first projection, on the same quotient.

The natural seed has its given marking over the field of order 2^m. Every
nonzero field-linear displacement has binary rank at least m. The actual
first projection is nontrivial since [L,A]=L, proving the seed estimate with
no extra numerical, representation-classification or generation premise.

The final declarations also supply the actual LA-action on C_V(C_A(L)).
They do not assert existence of invariant chief flags.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, the seed summand of (!!) and the actions needed for (!).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false

private theorem centralizing_involution_action
    {H D W : Type*} [Group H] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) H W) (j : D →* H) [IsIrreducible (τ.comp j)]
    (c : H) (hc : c ^ 2 = 1) (hcomm : ∀ l, Commute c (j l)) : τ c = 1 := by
  let σ := τ.comp j
  let f : IntertwiningMap σ σ := {
    toLinearMap := τ c - 1
    isIntertwining' := by
      intro l
      ext v
      change τ c (τ (j l) v) - τ (j l) v = τ (j l) (τ c v - v)
      rw [map_sub]
      have he := congrArg (fun g => τ g v) (hcomm l).eq
      exact congrArg (fun w => w - τ (j l) v)
        (by simpa only [map_mul, Module.End.mul_apply] using he) }
  have htwice (v : W) : τ c (τ c v) = v := by
    have he := congrArg (fun g => τ g v) hc
    simpa only [map_pow, pow_two, map_mul, Module.End.mul_apply, map_one,
      Module.End.one_apply] using he
  have hzero (v : W) : f (f v) = 0 := by
    change τ c (τ c v - v) - (τ c v - v) = 0
    rw [map_sub, htwice]
    have htwo (w : W) : w + w = 0 := by
      have he := @two_smul (ZMod 2) W _ _ _ w
      rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at he
      exact he.symm
    have hn (w : W) : -w = w := neg_eq_iff_add_eq_zero.mpr (htwo w)
    simp only [sub_eq_add_neg, hn]
    rw [add_assoc, ← add_assoc (τ c v), htwo, zero_add, htwo]
  have hf : f = 0 := by
    rcases IsIrreducible.injective_or_eq_zero f with hi | hz
    · ext v
      apply hi
      simpa using hzero v
    · exact hz
  ext v
  exact sub_eq_zero.mp (congrArg (fun u : IntertwiningMap σ σ => u v) hf)

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

/-- On an L-irreducible LA-section, A acts as its actual first projection. -/
theorem ComponentProjections.action_eq_left
    {A L M : Subgroup G} (p : ComponentProjections A L M)
    (hc : L ≤ centralizer (M : Set G)) (hA : IsElementaryAbelian 2 A)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) ↥(L ⊔ A) W)
    [IsIrreducible (τ.comp (Subgroup.inclusion (show L ≤ L ⊔ A from le_sup_left)))]
    (a : A) :
    τ ⟨a, (show A ≤ L ⊔ A from le_sup_right) a.property⟩ = τ (Subgroup.inclusion le_sup_left (p.left a)) := by
  let j : L →* ↥(L ⊔ A) := Subgroup.inclusion le_sup_left
  let a' : ↥(L ⊔ A) := ⟨a, (show A ≤ L ⊔ A from le_sup_right) a.property⟩
  let l := j (p.left a)
  let c := l⁻¹ * a'
  have hcval : (c : G) = p.right a := by
    change (p.left a : G)⁻¹ * a = p.right a
    rw [← p.multiply a, inv_mul_cancel_left]
  have hcpow : c ^ 2 = 1 := by
    apply Subtype.ext
    change (c : G) ^ 2 = 1
    rw [hcval]
    let : IsElementaryAbelian 2 A := hA
    have ha : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a
    have hr : (p.right a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
    exact congrArg (fun x : M => (x : G)) hr
  have hcc (x : L) : Commute c (j x) := by
    apply Subtype.ext
    change (c : G) * x = (x : G) * c
    rw [hcval]
    exact hc x.property (p.right a) (p.right a).property
  have he := centralizing_involution_action τ j c hcpow hcc
  have ha : a' = l * c := by dsimp [c]; group
  change τ a' = τ l
  rw [ha, map_mul, he, mul_one]

/-- Restriction of scalars multiplies every nonzero natural displacement by m. -/
theorem natural_fixedCodim_lower (F : BinaryField) (n : ℕ)
    (B : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)) (hne : B ≠ ⊥) :
    F.degree ≤ fixedCodim (linearNatural F n) B := by
  classical
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hbne : b ≠ 1 := fun he => hb1 (Subtype.ext he)
  let T : Module.End F.Carrier (Fin n → F.Carrier) :=
    specialLinearNatural n b - 1
  have hT : T ≠ 0 := by
    intro hz
    apply hbne
    apply specialLinearNatural_injective n
    rw [map_one]
    exact sub_eq_zero.mp hz
  have hR : LinearMap.range T ≠ ⊥ := by
    intro hz
    exact hT (LinearMap.range_eq_bot.mp hz)
  have hd : 0 < Module.finrank F.Carrier (LinearMap.range T) := by
    exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hR)
  have hfield : Module.finrank (ZMod 2) F.Carrier = F.degree := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    calc
      2 ^ Module.finrank (ZMod 2) F.Carrier = Nat.card F.Carrier := by
        simpa using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)).symm
      _ = _ := F.card_eq
  have he : fixedCodim (linearNatural F n) (zpowers b) =
      F.degree * Module.finrank F.Carrier (LinearMap.range T) := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    have hT' : linearNatural F n b - LinearMap.id = T.restrictScalars (ZMod 2) := rfl
    rw [hT', LinearMap.range_restrictScalars]
    change Module.finrank (ZMod 2) (LinearMap.range T) = _
    rw [← Module.finrank_mul_finrank (ZMod 2) F.Carrier, hfield]
  have hm := NaturalTensor.fixedCodim_mono (linearNatural F n) (zpowers_le.mpr hb)
  rw [he] at hm
  exact (Nat.le_mul_of_pos_right _ hd).trans hm

/-- Moving L ensures that the first coordinate of the offender is nontrivial. -/
theorem ComponentProjections.leftRange_ne_bot
    {A L M : Subgroup G} (p : ComponentProjections A L M)
    (hc : L ≤ centralizer (M : Set G)) (hne : L ≠ ⊥) (hLA : ⁅L,A⁆ = L) :
    p.left.range ≠ ⊥ := by
  intro hz
  have hcent : A ≤ centralizer (L : Set G) := by
    intro a ha
    have hl : p.left ⟨a, ha⟩ = 1 := by
      have hm : p.left ⟨a, ha⟩ ∈ p.left.range := ⟨⟨a, ha⟩, rfl⟩
      simpa only [hz, mem_bot] using hm
    have he := p.multiply ⟨a, ha⟩
    rw [hl, OneMemClass.coe_one, one_mul] at he
    change (p.right ⟨a, ha⟩ : G) = a at he
    rw [← he]
    exact (le_centralizer_iff.mp hc) (p.right ⟨a, ha⟩).property
  apply hne
  rw [← hLA]
  exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr hcent)

/-- Fixed codimension on an irreducible LA-section is measured by the actual
first-coordinate subgroup, not by an assumed marking of that section. -/
theorem ComponentProjections.fixedCodim_eq_left
    {A L M : Subgroup G} (p : ComponentProjections A L M)
    (hc : L ≤ centralizer (M : Set G)) (hA : IsElementaryAbelian 2 A)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) ↥(L ⊔ A) W)
    [IsIrreducible (τ.comp (Subgroup.inclusion (show L ≤ L ⊔ A from le_sup_left)))] :
    fixedCodim τ (A.subgroupOf (L ⊔ A)) =
      fixedCodim (τ.comp (Subgroup.inclusion (show L ≤ L ⊔ A from le_sup_left)))
        p.left.range := by
  let j : L →* ↥(L ⊔ A) := Subgroup.inclusion le_sup_left
  let k : A →* ↥(L ⊔ A) := Subgroup.inclusion le_sup_right
  have he : τ.comp k = (τ.comp j).comp p.left := by
    ext a w
    exact LinearMap.congr_fun (p.action_eq_left hc hA τ a) w
  have hx := fixedSpace_comp_map τ k (⊤ : Subgroup A)
  rw [← MonoidHom.range_eq_map, Subgroup.inclusion_range] at hx
  have hy := fixedSpace_comp_map (τ.comp j) p.left (⊤ : Subgroup A)
  rw [← MonoidHom.range_eq_map] at hy
  unfold fixedCodim
  rw [← hx, he, hy]

/-- The sharp m estimate on the literal natural seed U, with its LA-action. -/
theorem seed_fixedCodim_lower [Finite G]
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (hL : IsComponent G L) (hLA : ⁅L,A⁆ = L)
    (s : NaturalSeed ρ A L) (d : SecondComponent ρ A L) :
    s.field.degree ≤ fixedCodim s.space.toRepresentation (A.subgroupOf (L ⊔ A)) := by
  let p := d.projections ρ s hL
  have hc : L ≤ centralizer (d.second : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (hL.commutator_eq_bot_of_ne d.isComponent d.distinct)
  let : IsIrreducible (s.space.toRepresentation.comp
      (Subgroup.inclusion (show L ≤ L ⊔ A from le_sup_left))) :=
    ExtensionConsequences.irreducible_of_equiv s.natural
      (ExtensionConsequences.linearNatural_irreducible s.field (by decide))
  rw [p.fixedCodim_eq_left hc setup.minimal.1.1.2]
  rw [fixedCodim_map_equivariant _ (linearNatural s.field 3)
    s.natural.groupEquiv.toMonoidHom s.natural.linearEquiv s.natural.intertwines]
  apply natural_fixedCodim_lower
  apply fun hz => (p.leftRange_ne_bot hc ?_ hLA)
    ((p.left.range.map_eq_bot_iff_of_injective s.natural.groupEquiv.injective).mp hz)
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance

/-- The fixed space C_V(C_A(L)) is A-stable because A is abelian. -/
theorem offenderCentralizerFixed_stable {A L : Subgroup G}
    (hA : IsElementaryAbelian 2 A) :
    A ≤ subspaceStabilizer ρ (offenderCentralizerFixed ρ A L).toSubmodule := by
  let : IsElementaryAbelian 2 A := hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply fixedSpace_invariant_normalizer ρ
  apply le_trans _ (Subgroup.centralizer_le_normalizer _)
  intro a ha b hb
  exact congrArg (fun x : A => (x : G))
    (mul_comm (⟨b, hb.1⟩ : A) ⟨a, ha⟩)

/-- The literal fixed space, carrying the full LA-action needed for a flag. -/
noncomputable def offenderCentralizerFixedOver {A L : Subgroup G}
    (hA : IsElementaryAbelian 2 A) : Subrepresentation (ρ.comp (L ⊔ A).subtype) where
  toSubmodule := fixedSpace ρ (A ⊓ centralizer (L : Set G))
  apply_mem_toSubmodule g v hv := by
    have hl : L ≤ subspaceStabilizer ρ (offenderCentralizerFixed ρ A L).toSubmodule :=
      le_subspaceStabilizer ρ _ (fun l hl v hv =>
        (offenderCentralizerFixed ρ A L).apply_mem_toSubmodule ⟨l, hl⟩ hv)
    exact (sup_le hl (offenderCentralizerFixed_stable ρ hA) g.property v).2 hv


/-- Restriction of the actual LA-quotient action recovers the literal L-section.
The lower subspaces and quotient maps agree definitionally. -/
theorem InvariantChiefFlag.factorAction_comp_component
    {A L : Subgroup G} {S : Submodule (ZMod 2) V}
    (f : InvariantChiefFlag ρ A L S) (i : ℕ) :
    (f.factorAction i).comp
        (Subgroup.inclusion (show L ≤ L ⊔ A from le_sup_left)) =
      sectionRepresentation (ρ.comp L.subtype) (f.term i) (f.term (i + 1)) := rfl

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
