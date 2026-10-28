module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.SeedPair
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.CriticalSeeds
public import Theory.Representation.SemilinearFixedIndex

/-!
# Small pointwise actions and the original seed kernel

A pointwise actor fixing more than half the doubled space has no field twist.
A nonidentity multiplicity actor moves at least 3n dimensions. The component
kernel comparison therefore makes restriction to the original seed faithful
on every local pointwise automizer of corank at most 2n. Both conclusions use
the same field and full-module marking as the source normalizer bound.

Source: Aschbacher--Smith, 11.3.6, printed p.772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.SL3DoubledNaturalOffenders
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace SmallCentralizer
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- More than half the doubled space fixed pointwise removes every field twist,
without an assumption on the order of the actor. -/
theorem linear_of_small_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n)
    (A : Subgroup (Ambient F)) (hAN : A ≤ SL3DoubledNaturalOffenders.normalizer F)
    (hc : fixedCodim (action F) A < 3*n)
    (a : A) (r : F) (v : Space F) :
    action F a.val (r • v) = r • action F a.val v := by
  obtain ⟨σ,hσ⟩ := normalizer_semilinear a.val (hAN a.property)
  have he : σ = RingEquiv.refl F := by
    by_contra hne
    have hh := fixed_card_sq_le_of_nontrivial_twist (action F) A a.property hne hσ
    have hf := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace (action F) A)
    have hw := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space F)
    rw [Nat.card_zmod] at hf hw
    rw [hf,hw,←pow_mul] at hh
    have hd := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
    have hs := fixedCodim_add_finrank (action F) A
    rw [finrank_space hF] at hs hd
    omega
  change (a.val : Module.End (ZMod 2) (Space F)) (r • v) =
    r • (a.val : Module.End (ZMod 2) (Space F)) v
  simpa only [he,RingEquiv.refl_apply] using hσ r v

/-- A nonidentity multiplicity actor moves at least three field degrees.
The proof embeds one whole natural copy in its displacement space. -/
theorem centralizer_fixedCodim_lower {n : ℕ} (hF : Nat.card F = 2^n)
    (b : Ambient F) (hb : b ∈ centralizer (component F : Set (Ambient F)))
    (hne : b ≠ 1) : 3*n ≤ fixedCodim (action F) (zpowers b) := by
  obtain ⟨c,hc⟩ := centralizer_units b hb
  let δ : Module.End (ZMod 2) (Space F) := action F b - 1
  have hδ : δ = multiplicity F (c.val-1) := by
    change b.val - 1 = _
    rw [hc]
    have hh := (map_sub (multiplicityHom F) c.val 1).symm
    change multiplicity F c.val - multiplicity F 1 = multiplicity F (c.val-1) at hh
    rwa [multiplicity_one] at hh
  have hcne : c.val - 1 ≠ 0 := by
    intro hz
    apply hne
    apply Units.ext
    rw [hc,sub_eq_zero.mp hz,multiplicity_one]
    rfl
  obtain ⟨i,j,hij⟩ : ∃ i j : Fin 2, (c.val-1) i j ≠ 0 := by
    by_contra! hz
    apply hcne
    ext i j
    exact hz i j
  have he (v : Natural F) : δ (Pi.single j v) i = (c.val-1) i j • v := by
    rw [hδ]
    fin_cases j <;> simp [multiplicity_apply]
  let f : Natural F →ₗ[ZMod 2] δ.range :=
    { toFun v := ⟨δ (Pi.single j v),⟨Pi.single j v,rfl⟩⟩
      map_add' v w := by apply Subtype.ext; simp [Pi.single_add]
      map_smul' r v := by apply Subtype.ext; simp [Pi.single_smul] }
  have hf : Function.Injective f := by
    intro v w hvw
    have hh := congrArg (fun z : δ.range => z.val i) hvw
    change δ (Pi.single j v) i = δ (Pi.single j w) i at hh
    rw [he,he] at hh
    exact (smul_right_injective _ hij) hh
  have hd := LinearMap.finrank_le_finrank_of_injective hf
  rw [fixedCodim_zpowers_eq_displacement_rank]
  have hn : Module.finrank (ZMod 2) (Natural F) = 3*n := by
    simp [Module.finrank_pi_fintype, NaturalTensor.finrank_field F hF]
  exact hn ▸ hd

/-- Consequently a small pointwise actor centralizing the marked component
is the identity. -/
theorem centralizer_eq_one_of_small_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n)
    (A : Subgroup (Ambient F)) (hc : fixedCodim (action F) A < 3*n)
    (b : A) (hb : b.val ∈ centralizer (component F : Set (Ambient F))) : b.val = 1 := by
  by_contra hne
  have hl := (centralizer_fixedCodim_lower hF b.val hb hne).trans
    (NaturalTensor.fixedCodim_mono (action F) (zpowers_le.mpr b.property))
  omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- The original pointwise local centralizer has fixed codimension at most
the actual source corank. -/
theorem local_fixedCodim (d : Coordinates D S) {U : Subgroup G}
    (hU : U ≤ fullModule L V) :
    letI := fullModule_elementary d
    fixedCodim (automizerRepresentation (fullModule L V))
      (inducedAutomizer (fullModule L V)
        (normalizer (L : Set G) ⊓ centralizer (U : Set G))) ≤
      subgroupCorank (fullModule L V) U := by
  let := fullModule_elementary d
  rw [fixedCodim_inducedAutomizer _ _ (inf_le_left.trans normalizes_fullModule)]
  apply ChapterE.Section06.subgroupCorank_antitone
  exact le_inf hU (le_centralizer_iff.mpr inf_le_right)

/-- The literal doubled marking makes every element of the source pointwise
local centralizer field-linear at corank at most 2n. -/
theorem source_local_centralizer_linear (d : Coordinates D S) {U : Subgroup G}
    (hU : U ≤ fullModule L V)
    (hc : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree) :
    letI := fullModule_elementary d
    ∃ (E : Additive (fullModule L V) ≃ₗ[ZMod 2] Space S.field.Carrier)
      (f : Automizer (fullModule L V) →* Ambient S.field.Carrier),
      Function.Injective f ∧
      (∀ a v, E (automizerRepresentation (fullModule L V) a v) =
        action S.field.Carrier (f a) (E v)) ∧
      f.range ≤ SL3DoubledNaturalOffenders.normalizer S.field.Carrier ∧
      (inducedAutomizer (fullModule L V) L).map f = component S.field.Carrier ∧
      (∀ a ∈ inducedAutomizer (fullModule L V)
        (normalizer (L : Set G) ⊓ centralizer (U : Set G)),
        ∀ (r : S.field.Carrier) (v : Space S.field.Carrier),
          action S.field.Carrier (f a) (r • v) = r • action S.field.Carrier (f a) v) := by
  let := fullModule_elementary d
  obtain ⟨E,f,hf,hE,hN,_,hL⟩ := LocalMinimum.automizer_marking_component d
  refine ⟨E,f,hf,hE,hN,hL,?_⟩
  let A := inducedAutomizer (fullModule L V)
    (normalizer (L : Set G) ⊓ centralizer (U : Set G))
  have hfix := fixedCodim_map_equivariant
    (automizerRepresentation (fullModule L V)) (action S.field.Carrier) f E hE A
  have hb : fixedCodim (action S.field.Carrier) (A.map f) < 3*S.field.degree := by
    rw [←hfix]
    exact (local_fixedCodim d hU).trans_lt (hc.trans_lt (by have := S.field.degree_pos; omega))
  intro a ha r v
  exact linear_of_small_fixedCodim S.field.card_eq (A.map f)
    (by rintro _ ⟨b,hb,rfl⟩; exact hN ⟨b,rfl⟩) hb
    ⟨f a,mem_map_of_mem f ha⟩ r v

/-- On a local centralizer fixing a small-corank subgroup, the kernel on the
original seed equals the kernel on the whole doubled module. The component
kernel comparison makes its image a multiplicity actor; the 3n lower bound
then forces that image to be trivial. -/
theorem source_seed_kernel (d : Coordinates D S) {U : Subgroup G}
    (hU : U ≤ fullModule L V)
    (hc : subgroupCorank (fullModule L V) U ≤ 2*S.field.degree) :
    (normalizer (L : Set G) ⊓ centralizer (U : Set G)) ⊓ centralizer (V : Set G) =
      (normalizer (L : Set G) ⊓ centralizer (U : Set G)) ⊓ centralizer (fullModule L V : Set G) := by
  let := fullModule_elementary d
  let W := fullModule L V
  let C := normalizer (L : Set G) ⊓ centralizer (U : Set G)
  let K := normalizer (L : Set G) ⊓ centralizer (V : Set G)
  have hKL : ⁅K,L⁆ ≤ L ⊓ centralizer (V : Set G) := by
    refine le_inf (le_normalizer_iff_commutator_le_right.mp inf_le_left) ?_
    exact (commutator_mono inf_le_right le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        (D.normalizes.trans (normalizer_le_normalizer_centralizer _)))
  have hKW : ⁅K,L⁆ ≤ centralizer (W : Set G) :=
    (hKL.trans (CriticalAction.component_seed_centralizer d).le).trans inf_le_right
  obtain ⟨E,f,hf,hE,hN,_,hL⟩ := LocalMinimum.automizer_marking_component d
  let A := (inducedAutomizer W C).map f
  have hfix := fixedCodim_map_equivariant (automizerRepresentation W)
    (action S.field.Carrier) f E hE (inducedAutomizer W C)
  have hsmall : fixedCodim (action S.field.Carrier) A < 3*S.field.degree := by
    rw [←hfix]
    exact (local_fixedCodim d hU).trans_lt (hc.trans_lt (by have := S.field.degree_pos; omega))
  apply le_antisymm ?_ (inf_le_inf_left _ (centralizer_le seed_le_fullModule))
  rintro x ⟨hx,hxV⟩
  refine ⟨hx,?_⟩
  let xN : normalizer (W : Set G) := ⟨x,normalizes_fullModule hx.1⟩
  let ψ := f.comp W.normalizerMonoidHom.rangeRestrict
  have hxA : ψ xN ∈ A := mem_map_of_mem f (mem_map_of_mem _ hx)
  have hxC : ψ xN ∈ centralizer (component S.field.Carrier : Set (Ambient S.field.Carrier)) := by
    rw [←hL,mem_centralizer_iff]
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨l,hl,rfl⟩ := ha
    have hz : ⁅x,(l:G)⁆ ∈ centralizer (W : Set G) :=
      hKW (commutator_mem_commutator (show x ∈ K from ⟨hx.1,hxV⟩) hl)
    have hk : ⁅xN,l⁆ ∈ W.normalizerMonoidHom.ker := by
      rw [W.normalizerMonoidHom_ker]
      exact hz
    have he : ψ ⁅xN,l⁆ = 1 := by
      change f (W.normalizerMonoidHom.rangeRestrict ⁅xN,l⁆) = 1
      have hh : W.normalizerMonoidHom.rangeRestrict ⁅xN,l⁆ = 1 := Subtype.ext hk
      rw [hh,map_one]
    rw [map_commutatorElement] at he
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  have hx1 : ψ xN = 1 := centralizer_eq_one_of_small_fixedCodim S.field.card_eq A hsmall ⟨ψ xN,hxA⟩ hxC
  have ha1 : W.normalizerMonoidHom.rangeRestrict xN = 1 := hf (hx1.trans (map_one f).symm)
  have hk : xN ∈ W.normalizerMonoidHom.ker := congrArg Subtype.val ha1
  rwa [W.normalizerMonoidHom_ker] at hk

end SmallCentralizer
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled

