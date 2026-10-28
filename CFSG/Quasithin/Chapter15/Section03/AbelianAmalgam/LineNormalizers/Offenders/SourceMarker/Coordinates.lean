module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceMarker.Definitions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.SylowTransport

/-!
# The actual marker coordinates and their pointwise stabilizer

The chosen residual translate exchanges the second coordinate with the first.
It preserves the original V, so fixation of its first projection forces fixation
of all of V/E. This gives displacement in E and derives V-stability, rather
than assuming it. The original seed commutator bound proves Sylow fixation;
the natural orthogonal action identifies the pointwise stabilizer with M.
Nonvanishing follows from |V| = 16 and |E| = 4.

All coordinates use OriginalData's actual paired quotient, with kernel E;
no splitting of the central extension is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154 (PDF pp.1170–1171).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer BestReduction.SourceAssembly
open GoldschmidtCore.LocalRelations GoldschmidtCore.LocalRelations.OrthogonalProducts
open Representation.NormalElementaryQuotient
universe u
variable {G L : Type u} [Group G] [Finite G] [Group L]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
  (o : Geometry.OriginalData Y T V M E Pc)
  (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
  (hker : f.ker = centralizer (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))
local notation "H" => temporaryLineNormalizer T V E
local notation "U" => Replacement.Transvections.localSpan T V E
local notation "E₀" => localLine T V E
local notation "N" => subspace U (Subgroup.subgroupOf E₀ U)
local notation "P" => o.pairedSection f hf hker
local notation "σ" => o.pairedRepresentation f hf hker
local notation "d" => o.chosenPairedGeometry f hf hker
local notation "y" => o.residualElement o.markedResidual o.markedResidual.property

/-- The original residual translate recovers the second paired coordinate from the first. -/
private theorem first_residual_eq_second : let := o.module_normal
    let := o.module_elementary
    let := o.line_normal
    ∀ v : Additive U, ((P).projection (representation U f hf hker (f y⁻¹) v)).1 =
      ((P).projection v).2 := by
  let := o.module_normal
  let := o.module_elementary
  let := o.line_normal
  dsimp only
  intro v
  let ρ := MarkedSection.action U E₀ f hf hker
  have hcube := (MarkedSection.quotient_operator_relations U E₀ f hf hker o.tau y
    (o.markedOperatorRelations f hf hker o.markedResidual o.markedResidual.property
      o.markedResidual_image_ne_one)).1
  have ht (w : Additive U ⧸ N) : ρ y⁻¹ (ρ y⁻¹ w) = ρ y⁻¹ w + w := by
    have h := LinearMap.congr_fun hcube w
    change ρ y⁻¹ (ρ y⁻¹ w) + ρ y⁻¹ w + w = 0 at h
    have h2 : ∀ z : Additive U ⧸ N, z + z = 0 := by
      intro z
      have hz := @two_smul (ZMod 2) (Additive U ⧸ N) _ _ _ z
      rw [show (2 : ZMod 2) = 0 from rfl, zero_smul] at hz
      exact hz.symm
    apply add_right_cancel (b := ρ y⁻¹ w + w)
    rw [h2]
    simpa only [← add_assoc] using h
  change ((d).coordinates (ρ y⁻¹ ((N).mkQ v))).1 = ((d).coordinates ((N).mkQ v)).2
  let a := ((d).coordinates ((N).mkQ v)).1
  let b := ((d).coordinates ((N).mkQ v)).2
  have hr : (a : Additive U ⧸ N) + ρ y⁻¹ b = (N).mkQ v := (d).coordinates_reconstruct _
  rw [← hr, map_add, ht, map_add, map_add, (d).coordinates_second,
    (d).coordinates_second, (d).coordinates_first]
  simp only [ρ, map_add, (d).coordinates_first, (d).coordinates_second,
    Prod.fst_add, Prod.snd_add, zero_add]



/-- The second coordinate of each original seed vector lies in the same literal marker. -/
private theorem second_mem_projected : let := o.module_normal
    let := o.module_elementary
    ∀ v : Additive U, (v.toMul.val.val ∈ V) → ((P).projection v).2 ∈ projected o f hf hker := by
  let := o.module_normal
  let := o.module_elementary
  let := o.line_normal
  dsimp only
  intro v hv
  rw [← first_residual_eq_second o f hf hker v]
  apply Submodule.mem_map.mpr
  refine ⟨representation U f hf hker (f y⁻¹) v, ?_, rfl⟩
  change ((representation U f hf hker (f y⁻¹) v).toMul : H).val ∈ V
  rw [representation_apply]
  exact (o.action.normalizes (M.inv_mem (o.Y_le (lineY_le Y E o.markedResidual.property).1))
    v.toMul.val.val).mp hv

/-- Pointwise fixation of V# is exactly displacement of every original v into E. -/
theorem fixes_iff_displacement (x : H) (hx : x ∈ localCentralizer T V E) :
    let := o.module_normal
    let := o.module_elementary
    (∀ w ∈ projected o f hf hker, σ (QuotientGroup.mk' (localCore T V E) x) w = w) ↔
    ∀ v ∈ V.subgroupOf H, ⁅x, v⁆ ∈ E₀ := by
  let := o.module_normal
  let := o.module_elementary
  let := o.line_normal
  dsimp only
  have hproj (v : Additive U) :
      (P).projection (representation U f hf hker (f x) v) = (P).projection v ↔
      ⁅x, v.toMul.val⁆ ∈ E₀ := by
    change (d).coordinates ((N).mkQ (representation U f hf hker (f x) v)) =
      (d).coordinates ((N).mkQ v) ↔ _
    rw [(d).coordinates.injective.eq_iff]
    refine (Submodule.Quotient.eq (N)).trans ?_
    change ((representation U f hf hker (f x) v).toMul : H) / v.toMul.val ∈ E₀ ↔ _
    rw [representation_apply, div_eq_mul_inv]
    rfl
  constructor
  · intro h v hv
    let u : Additive U := Additive.ofMul ⟨v, le_conjugateSpanBy V _ hv⟩
    apply (hproj u).mp
    rw [(P).equivariant x hx]
    apply Prod.ext
    · exact h _ (Submodule.mem_map.mpr ⟨u, hv, rfl⟩)
    · exact h _ (second_mem_projected o f hf hker u hv)
  · intro h w hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hh := (hproj v).mpr (h v.toMul.val hv)
    rw [(P).equivariant x hx] at hh
    exact congrArg Prod.fst hh

/-- The first projection of original V/E is nonzero. -/
theorem projected_nonzero : let := o.module_normal
    let := o.module_elementary
    projected o f hf hker ≠ ⊥ := by
  let := o.module_normal
  let := o.module_elementary
  let := o.line_normal
  dsimp only
  intro hz
  have hVE : V ≤ E := by
    intro v hv
    let u : Additive U := Additive.ofMul ⟨⟨v, o.span_le_temporary (le_conjugateSpanBy V _ hv)⟩,
      le_conjugateSpanBy V _ hv⟩
    have h1 : ((P).projection u).1 = 0 := by
      have hh : ((P).projection u).1 ∈ projected o f hf hker :=
        Submodule.mem_map.mpr ⟨u, hv, rfl⟩
      rwa [hz, Submodule.mem_bot] at hh
    have h2 : ((P).projection u).2 = 0 := by
      have hh := second_mem_projected o f hf hker u hv
      rwa [hz, Submodule.mem_bot] at hh
    have hk : u ∈ (P).projection.ker := Prod.ext h1 h2
    rw [(P).kernel_eq] at hk
    exact hk
  have hc : Nat.card V = 16 := by
    rw [Nat.card_congr o.action.coordinates.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have he := Nat.card_le_card_of_injective (inclusion hVE) (inclusion_injective hVE)
  rw [hc, o.line_card] at he
  omega

/-- The literal quotient image q(S_E) fixes the actual projected marker. -/
theorem sylow_fixes_projected : let := o.module_normal
    let := o.module_elementary
    projected o f hf hker ≤ fixedSpace σ
      ((centralizerSylow T V E).map (QuotientGroup.mk' (localCore T V E))) := by
  let := o.module_normal
  let := o.module_elementary
  dsimp only
  intro w hw s
  obtain ⟨x, hx, hxs⟩ := s.property
  change σ s.val w = w
  rw [← hxs]
  apply (fixes_iff_displacement o f hf hker x ⟨x.property, hx.2⟩).mpr ?_ w hw
  intro v hv
  change ⁅x.val, v.val⁆ ∈ E
  rw [← commutatorElement_inv]
  exact E.inv_mem (o.seed_commutator (commutator_mem_commutator hv hx))

include o in
omit [Finite G] in
/-- The original orthogonal action puts every centralizer-in-M displacement in E. -/
theorem displacement_of_mem_M (x : H) (hx : x ∈ localCentralizer T V E)
    (hxM : x.val ∈ M) : ∀ v ∈ V.subgroupOf H, ⁅x, v⁆ ∈ E₀ := by
  intro v hv
  let m : M := ⟨x.val, hxM⟩
  have hd := OrthogonalFourBinary.SylowGeometry.line_pointwise_displacement_mem
    (coordinateLine o.action E)
    ((coordinateLine_card o.action E o.line_le).trans o.line_card)
    (coordinateLine_singular o.action E o.line_le o.singular) (o.action.action m)
    ((Orthogonal.coordinateLine_pointwise_iff o.action E o.line_le m).mpr hx.2)
    (o.action.coordinates ⟨v.val,hv⟩)
  have hh := (mem_coordinateLine o.action E _).mp hd
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    o.action.coordinates.symm_apply_apply] at hh
  have hc := o.action.intertwines m ⟨v.val,hv⟩
  change (o.action.coordinates.symm (OrthogonalFourBinary.TerminalLines.vectorAction (o.action.action m)
    (o.action.coordinates ⟨v.val,hv⟩)) : G) = x.val * v.val * x.val⁻¹ at hc
  rw [hc] at hh
  exact hh

/-- Among actual centralizer elements, the pointwise marker stabilizer is exactly M. -/
theorem fixes_iff_mem_M (hNM : normalizer (V : Set G) ≤ M)
    (x : H) (hx : x ∈ localCentralizer T V E) :
    let := o.module_normal
    let := o.module_elementary
    (∀ w ∈ projected o f hf hker, σ (QuotientGroup.mk' (localCore T V E) x) w = w) ↔
      x.val ∈ M := by
  let := o.module_normal
  let := o.module_elementary
  dsimp only
  constructor
  · intro hfix
    have h := (fixes_iff_displacement o f hf hker x hx).mp hfix
    apply hNM
    apply (mem_normalizer_iff_map_conj_eq).mpr
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨v, hv, rfl⟩
      have hvH := o.span_le_temporary (le_conjugateSpanBy V _ hv)
      have he := o.line_le (h ⟨v, hvH⟩ hv)
      have hm := V.mul_mem he hv
      change (x.val * v * x.val⁻¹ * v⁻¹) * v ∈ V at hm
      change x.val * v * x.val⁻¹ ∈ V
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
    · rw [Subgroup.card_map_of_injective (MulAut.conj x.val).injective]
  · intro hm
    exact (fixes_iff_displacement o f hf hker x hx).mpr
      (displacement_of_mem_M o x hx hm)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker
