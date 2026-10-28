module
public import Theory.Representation.SL2.SharpNaturalQuotient
public import Theory.Representation.BinaryConjugationSection.QuotientActor
public import Theory.Representation.BinaryConjugationSection.FixedIndex
public import Theory.Representation.BinaryConjugationSection.FixedSplitting
public import Theory.ElementaryAbelian.Injective
public import Theory.Representation.SpecialLinearNatural

/-!
# Natural recognition for a literal binary SL₂ section

A nontrivial binary SL₂(2ⁿ) module of order q² with two generating Sylows
of fixed codimension n is the original natural module. For a normal group
section M/N, fixed subgroups of index q give the required codimensions.
The action descends through its exact kernel, and the returned coordinate
map keeps the original numerator, denominator and quotient marking.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 5.5(b),
pp.51--52, and Aschbacher--Smith G.1.6--7. The literal gap-factor consumer
is `Glauberman.PushingUpSL2DegreeNaturalLayers`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace Representation.SL2
variable {F W : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Sharp fixed spaces and order q² identify the whole marked module. -/
theorem natural_of_order_and_sharp_fixed
    (ρ : Representation (ZMod 2) SL(2,F) W) (hnt : ∃ g, ρ g ≠ 1)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (R T : Sylow 2 SL(2,F)) (hgen : (R : Subgroup SL(2,F)) ⊔ T = ⊤)
    (hR : fixedCodim ρ R = n) (hT : fixedCodim ρ T = n)
    (hcard : Nat.card W = Nat.card F ^ 2) :
    ∃ E : W ≃ₗ[ZMod 2] (Fin 2 → F),
      ∀ g v, E (ρ g v) = Matrix.mulVec g.val (E v) := by
  have hdim : Module.finrank (ZMod 2) W = 2*n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hF,←pow_mul] at hcard
    have he := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hcard
    omega
  have hz : fixedSpace ρ ⊤ = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have hl := fixedCodim_top_lower ρ hnt hn hF
    have he := fixedCodim_add_finrank ρ ⊤
    omega
  obtain ⟨E,hE⟩ := sharp_sylow_natural_quotient ρ hnt hn hF R T hgen hR hT
  let q := (fixedSpace ρ ⊤).mkQ
  have hqi : Function.Injective q := LinearMap.ker_eq_bot.mp (by rw [Submodule.ker_mkQ,hz])
  refine ⟨(LinearEquiv.ofBijective q ⟨hqi,(fixedSpace ρ ⊤).mkQ_surjective⟩).trans E,?_⟩
  intro g v
  exact hE g (q v)

variable {G : Type*} [Group G] [Finite G]

/-- Recognize the actual M/N conjugation section from its two fixed halves. -/
theorem natural_section_of_fixed_halves
    (e : (G ⧸ pCore 2 G) ≃* SL(2,F)) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S T : Sylow 2 G) (hgen : (S : Subgroup G) ⊔ T = ⊤)
    (hidxS : (pCore 2 G).relIndex (S : Subgroup G) = Nat.card F)
    (M N A B : Subgroup G) [M.Normal] [N.Normal] (hNM : N ≤ M)
    [IsElementaryAbelian 2 (M.map (QuotientGroup.mk' N))]
    (hkernel : commutatorPreimage ⊤ M N = pCore 2 G)
    (hcard : N.relIndex M = Nat.card F ^ 2)
    (hAM : A ≤ M) (hBM : B ≤ M)
    (hA : ⁅(S : Subgroup G),A⁆ ≤ N) (hB : ⁅(T : Subgroup G),B⁆ ≤ N)
    (hiA : A.relIndex M = Nat.card F) (hiB : B.relIndex M = Nat.card F) :
    Nonempty (BinaryConjugationSection (⊤ : Subgroup G) M N
      (((specialLinearNatural 2).restrictScalars (k := ZMod 2)).comp
        (e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 G)).comp (⊤ : Subgroup G).subtype)))) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkf : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let π := f.comp (⊤ : Subgroup G).subtype
  have hπ : Function.Surjective π := hf.comp (fun x => ⟨⟨x,mem_top x⟩,rfl⟩)
  let qM := (QuotientGroup.mk' N).comp M.subtype
  have hkM : qM.ker = N.subgroupOf M := by
    ext x
    exact QuotientGroup.eq_one_iff x.val
  have hrM : qM.range = M.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp,range_subtype]
  let E₀ : (M ⧸ N.subgroupOf M) ≃* M.map (QuotientGroup.mk' N) :=
    (QuotientGroup.quotientMulEquivOfEq hkM.symm).trans
      ((QuotientGroup.quotientKerEquivRange qM).trans (MulEquiv.subgroupCongr hrM))
  let : IsElementaryAbelian 2 (M ⧸ N.subgroupOf M) :=
    IsElementaryAbelian.of_injective E₀.toMonoidHom E₀.injective
  have hk (a : (⊤ : Subgroup G)) : π a = 1 ↔ ∀ m ∈ M, ⁅(a : G),m⁆ ∈ N := by
    change (a : G) ∈ f.ker ↔ _
    rw [hkf,←hkernel,mem_commutatorPreimage_iff _ _ _ le_normalizer_of_normal]
    exact and_iff_right (mem_top _)
  obtain ⟨ρ,c,hfaith,hcoord⟩ := BinaryConjugationSection.exists_faithful_quotient_actor
    (⊤ : Subgroup G) M N le_top hNM le_normalizer_of_normal le_normalizer_of_normal π hπ hk
  let R' := S.mapSurjective hf
  let T' := T.mapSurjective hf
  have hgen' : (R' : Subgroup SL(2,F)) ⊔ T' = ⊤ := by
    change (S : Subgroup G).map f ⊔ (T : Subgroup G).map f = ⊤
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ hf]
  have hne : (R' : Subgroup SL(2,F)) ≠ ⊥ := by
    intro he
    have hle : (S : Subgroup G) ≤ pCore 2 G := by
      rw [←hkf]
      exact (Subgroup.map_eq_bot_iff _).mp he
    have hi := relIndex_eq_one.mpr hle
    rw [hidxS,hF] at hi
    exact (ne_of_gt (one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : n ≠ 0))) hi
  obtain ⟨r,hr,hr1⟩ := (R' : Subgroup SL(2,F)).bot_or_exists_ne_one.resolve_left hne
  have hnt : ∃ g, ρ g ≠ 1 := ⟨r,fun hh => hr1 (hfaith (hh.trans ρ.map_one.symm))⟩
  have hneT : (T' : Subgroup SL(2,F)) ≠ ⊥ := by
    intro he
    have hc : Nat.card T' = Nat.card F :=
      Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T').symm.toEquiv
    have hb : Nat.card T' = 1 := by
      rw [he]
      simp
    rw [hc,hF] at hb
    exact (ne_of_gt (one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : n ≠ 0))) hb
  have hfixed (P : Subgroup G) (L : Subgroup G)
      (hLM : L ≤ M) (hc : ⁅P,L⁆ ≤ N) (hi : L.relIndex M = Nat.card F) :
      fixedCodim ρ (P.map f) ≤ n := by
    have hle : L ≤ commutatorPreimage M P N := le_commutatorPreimage hLM (by rwa [commutator_comm])
    have hb := relIndex_le_of_le_left hle (show L.relIndex M ≠ 0 from index_ne_zero_of_finite)
    have he := BinaryConjugationSection.fixed_index_image ρ π c P le_top
    have hm : (P.subgroupOf (⊤ : Subgroup G)).map π = P.map f := by
      rw [show π = f.comp (⊤ : Subgroup G).subtype from rfl,←map_map,map_subgroupOf_eq_of_le le_top]
    rw [hm] at he
    rw [he,hi,hF] at hb
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hb
  have hR : fixedCodim ρ R' = n := le_antisymm (hfixed S A hAM hA hiA)
    (two_subgroup_fixedCodim_lower ρ hnt hn hF R' R'.isPGroup' hne)
  have hT : fixedCodim ρ T' = n := le_antisymm (hfixed T B hBM hB hiB)
    (two_subgroup_fixedCodim_lower ρ hnt hn hF T' T'.isPGroup' hneT)
  have horder : Nat.card (Additive (M ⧸ N.subgroupOf M)) = Nat.card F ^ 2 := by
    exact (Subgroup.index_eq_card (N.subgroupOf M)).symm.trans hcard
  obtain ⟨E,hE⟩ := natural_of_order_and_sharp_fixed ρ hnt hn hF R' T' hgen' hR hT horder
  refine ⟨{
    section_le := le_top
    kernel_le := hNM
    normalized := le_normalizer_of_normal
    coordinates := E.toAddEquiv.toMultiplicative.toMonoidHom.comp c.coordinates
    onto := E.toAddEquiv.toMultiplicative.surjective.comp c.onto
    kernel_eq := ?_
    equivariant := ?_ }⟩
  · ext m
    change E (c.coordinates m).toAdd = 0 ↔ m ∈ N.subgroupOf M
    rw [E.map_eq_zero_iff]
    exact c.coordinates_eq_one_iff m
  · intro a m
    change E (c.coordinates _).toAdd = Matrix.mulVec (π a).val (E (c.coordinates m).toAdd)
    rw [c.equivariant]
    exact hE (π a) (c.coordinates m).toAdd
end Representation.SL2
