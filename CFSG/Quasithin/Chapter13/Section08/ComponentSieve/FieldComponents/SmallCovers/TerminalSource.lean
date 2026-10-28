module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Basic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.ThreeDimensional
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.PairMarking
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource.HexacodeMarking

/-!
# A terminal cover contradiction using the other source section

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(2), printed p.956 (PDF p.973), and 13.8.4(5),(6), printed p.947.
Both rendered pages were checked: the terminal sentence names U_H, whereas
the cited quadraticity clause names Ũ_H and V_H/U_H.

The six-dimensional hexacode obstruction in `ThreeDimensional` is preserved.
Instead this module uses the source's noncentral permutation quotient on
V_H/U_H. Once the actual parabolic cosets are identified with the fifteen
pairs, the pair-module theorem rules out quadraticity of its two-core.
Containment from 13.8.8(2) and rank greater than one from 13.8.18(4) identify
the actual Vα* with that four-group; conjugacy transfers 13.8.4(6).

The conjugation equation in the theorem fixes the action on the literal
quotient. No arbitrary lifted representation, ambient normality assumption,
or nonquadraticity on the hexacode is substituted for the source data.

`contradiction_of_hexacode_point` completes the terminal conditional
implication: it constructs `Pairs.Marking` from the faithful embedding of
the actual H* into the hexacode group, the image of K*, and the genuine
F₄-point stabilizer. The order-four two-core excludes the six full-weight
points, selects the fifteen weight-four points, and supplies the actual
double-transposition lifts. Thus no pair marking is left as an extra premise.

The reduction owner must still recognize the actual W (either Ũ_H or its
specified quotient) to construct this embedding and point stabilizer, and
supply the displayed earlier source conclusions. The reduced configuration
Y = L₁,+ normal in H and Ũ_H = [Ũ_H,Y] is used in that recognition, not in
the terminal implication once its geometric outputs are available. The full
13.8.21(2), including the cover reduction and other cases, remains a separate
assembly obligation.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative


private theorem quadratic_map_conj {H V : Type*} [Group H]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) H V} {A : Subgroup H}
    (hA : IsQuadratic ρ A) (g : H) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  have hinv (v : V) : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
  have h := congrArg (ρ g) (hA a ha b hb (ρ g⁻¹ v))
  have hginv (v : V) : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  simpa only [map_mul, Module.End.mul_apply, map_sub, hinv, hginv] using h

variable {G : Type*} [Group G] [Finite G]
open scoped commutatorElement

/-- The terminal contradiction on the literal section V_H/U_H, conditional
on constructing the actual parabolic pair marking. Noncentrality is derived
from the ambient commutator clause using the specified conjugation action.
The actual conjugate Vα* fills O₂(L₁*T*) by its rank bound; quadraticity
transfers from Vγ* along the given inner conjugation. -/
theorem contradiction_of_pair_marking
    (H M L₁ T V V₃ Vα Vγ : Subgroup G)
    [((Source.UH H V₃).subgroupOf (Source.VH H V)).Normal]
    [IsMulCommutative (Source.Vsection H V V₃)]
    [Module (ZMod 2) (Additive (Source.Vsection H V V₃))]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hact : ∀ h : H, ∀ v : Source.VH H V,
      ρ (QuotientGroup.mk' (pCore 2 H) h)
        (Additive.ofMul (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf (Source.VH H V)) v)) =
      Additive.ofMul (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf (Source.VH H V))
        ⟨(h : G) * (v : G) * (h : G)⁻¹,
          (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V H h.property) v).mp v.property⟩))
    (m : Pairs.Marking (Source.starImage H (H ⊓ M)))
    (hparabolic : Source.starImage H (H ⊓ M) =
      Source.starImage H L₁ ⊔ Source.starImage H T)
    (f₀ : BinaryPermutation.Full (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)) →ₗ[ZMod 2]
      Additive (Source.Vsection H V V₃))
    (hf₀ : Function.Surjective f₀)
    (heq₀ : ∀ h v, f₀ (BinaryPermutation.representation
      (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)) (MulAction.toPerm h) v) = ρ h (f₀ v))
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (g : Source.Hstar H)
    (hconj : (Source.starImage H Vγ).map (MulAut.conj g).toMonoidHom = Source.starImage H Vα)
    (hplace : Source.starImage H Vα ≤ (Source.starImage H L₁ ⊔ Source.starImage H T).pCoreIn 2)
    (hfour : Nat.card ((Source.starImage H L₁ ⊔ Source.starImage H T).pCoreIn 2) = 4)
    (hrank : 1 < rank (Source.starImage H Vα))
    (hquad : IsQuadratic ρ (Source.starImage H Vγ)) : False := by
  have hn : ∃ h v, ρ h v ≠ v := by
    by_contra hc
    push Not at hc
    apply hnoncentral
    rw [commutator_comm]
    apply commutator_le.mpr
    intro h hh v hv
    have hnorm := (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V H hh) v).mp hv
    let q := QuotientGroup.mk' ((Source.UH H V₃).subgroupOf (Source.VH H V))
    have he : q ⟨h * v * h⁻¹, hnorm⟩ = q ⟨v, hv⟩ := by
      have ha := hact ⟨h, hh⟩ ⟨v, hv⟩
      rw [hc] at ha
      exact (congrArg Additive.toMul ha).symm
    have hmem : ⁅h, v⁆ ∈ Source.VH H V := by
      exact (Source.VH H V).mul_mem hnorm ((Source.VH H V).inv_mem hv)
    have hq : q ⟨⁅h, v⁆, hmem⟩ = 1 := by
      change q (⟨h * v * h⁻¹, hnorm⟩ * (⟨v, hv⟩ : Source.VH H V)⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    change (⟨⁅h, v⁆, hmem⟩ : Source.VH H V) ∈
      (Source.UH H V₃).subgroupOf (Source.VH H V)
    exact (QuotientGroup.eq_one_iff _).mp hq
  have heq := eq_four_of_rank_gt_one (Source.starImage H Vα)
    ((Source.starImage H L₁ ⊔ Source.starImage H T).pCoreIn 2) hplace hfour hrank
  have hqa := quadratic_map_conj hquad g
  rw [hconj, heq, ← hparabolic] at hqa
  exact Pairs.noncentral_quotient_not_quadratic _ m ρ f₀ hf₀ heq₀ hn hqa

/-- The terminal Â₆ contradiction from the genuine hexacode point stabilizer
and the earlier source conclusions. The embedding identifies the actual K*
with the even hexacode cover. Its point stabilizer is the actual L₁*T*,
whose intrinsic two-core has order four. These geometric outputs of the
recognition of W construct the pair marking used on the different section
V_H/U_H. The latter retains its literal conjugation action, noncentral
permutation quotient from 13.8.4(5), quadraticity from 13.8.4(6), conjugate
placement from 13.8.8(2), and rank bound from 13.8.18(4). -/
theorem contradiction_of_hexacode_point
    (H M K L₁ T V V₃ Vα Vγ : Subgroup G)
    [((Source.UH H V₃).subgroupOf (Source.VH H V)).Normal]
    [IsMulCommutative (Source.Vsection H V V₃)]
    [Module (ZMod 2) (Additive (Source.Vsection H V V₃))]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hact : ∀ h : H, ∀ v : Source.VH H V,
      ρ (QuotientGroup.mk' (pCore 2 H) h)
        (Additive.ofMul (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf (Source.VH H V)) v)) =
      Additive.ofMul (QuotientGroup.mk' ((Source.UH H V₃).subgroupOf (Source.VH H V))
        ⟨(h : G) * (v : G) * (h : G)⁻¹,
          (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V H h.property) v).mp v.property⟩))
    (e : Source.Hstar H →* Atlas.Codes.HexAutomorphisms)
    (he : Function.Injective e)
    (hcomponent : (Source.starImage H K).map e = Atlas.Codes.hexSign.ker)
    (D : Submodule Representation.Hexacode.F Atlas.Codes.hexacode)
    (hD : Module.finrank Representation.Hexacode.F D = 1)
    (hpoint : HexacodeMarking.pointStabilizer e D =
      Source.starImage H L₁ ⊔ Source.starImage H T)
    (hparabolic : Source.starImage H (H ⊓ M) =
      Source.starImage H L₁ ⊔ Source.starImage H T)
    (f₀ : BinaryPermutation.Full (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)) →ₗ[ZMod 2]
      Additive (Source.Vsection H V V₃))
    (hf₀ : Function.Surjective f₀)
    (heq₀ : ∀ h v, f₀ (BinaryPermutation.representation
      (Source.Hstar H ⧸ Source.starImage H (H ⊓ M)) (MulAction.toPerm h) v) = ρ h (f₀ v))
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (g : Source.Hstar H)
    (hconj : (Source.starImage H Vγ).map (MulAut.conj g).toMonoidHom = Source.starImage H Vα)
    (hplace : Source.starImage H Vα ≤ (Source.starImage H L₁ ⊔ Source.starImage H T).pCoreIn 2)
    (hfour : Nat.card ((Source.starImage H L₁ ⊔ Source.starImage H T).pCoreIn 2) = 4)
    (hrank : 1 < rank (Source.starImage H Vα))
    (hquad : IsQuadratic ρ (Source.starImage H Vγ)) : False := by
  have heven : Atlas.Codes.hexSign.ker ≤ e.range := by
    rw [← hcomponent]
    rintro x ⟨k, _, hk⟩
    exact ⟨k, hk⟩
  have hmark : HexacodeMarking.pointStabilizer e D =
      Source.starImage H (H ⊓ M) := hpoint.trans hparabolic.symm
  have hcard : Nat.card ((HexacodeMarking.pointStabilizer e D).pCoreIn 2) = 4 := by
    rwa [hpoint]
  obtain ⟨m⟩ := HexacodeMarking.nonempty_marking_of_twoCore_card_eq_four
    e he heven D hD hcard
  rw [hmark] at m
  exact contradiction_of_pair_marking H M L₁ T V V₃ Vα Vγ ρ hact m
    hparabolic f₀ hf₀ heq₀ hnoncentral g hconj hplace hfour hrank hquad

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.TerminalSource
