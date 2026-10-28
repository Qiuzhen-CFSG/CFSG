module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.Reduction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree.PrimeThirteen
public import Theory.Representation.PSL3Three.SmallDegreeDescent

/-!
# Transport of the PSL₃(3) small-degree calculations to the source action

The representation restricted to the actual generalized Fitting subgroup is
faithful and irreducible. Once its central kernel has been eliminated, the
supplied projective model transports this restriction to the native PSL₃(3).
Scalar descent of the native absolute-degree and field-of-definition
calculations then gives binary degree twelve.

The degree hypothesis retains the actual actor rank, `d ≤ 6 m₂(G)`. The
bound eighteen is used only inside the native scalar calculation. No absolute
irreducibility on F*(G), or SQTK hypothesis on a linear normalizer, is assumed.

The centerless-cover and character calculations below remain explicit inputs.
This module does not yet discharge the small-degree source theorem. The cover
input is supplied by the ordinary SL₃ universal-projection calculation; the
native representation calculation is independent of that cover calculation.

Source: GM02, Classification of 2F-modules I, Proposition 4.2, pp.9–10;
Aschbacher–Smith K.2, printed p.453.
-/

public section
open Subgroup Theory.GroupTheory Representation

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)

private theorem irreducible_comp_equiv {H J W : Type*} [Group H] [Group J]
    [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) H W) [IsIrreducible τ] (e : J ≃* H) :
    IsIrreducible (τ.comp e.toMonoidHom) := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial τ
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation τ :=
    ⟨S.toSubmodule, fun g w hw => by
      simpa using S.apply_mem_toSubmodule (e.symm g) hw⟩
  rcases eq_bot_or_eq_top T with hT | hT
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation τ => U.toSubmodule) hT
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation τ => U.toSubmodule) hT

include h

omit [Finite G] in
/-- Actual source application of scalar descent, with exactly the outstanding
cover and native representation calculations displayed as additional premises. -/
theorem source_degree_twelve_of_centerless_and_absolute_calculations
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 3 3)
    (hrank : primeRank 2 G ≤ 3)
    (hdim : 12 ≤ Module.finrank (ZMod 2) V)
    (hbound : Module.finrank (ZMod 2) V ≤ 6 * primeRank 2 G)
    (hcenter : center (generalizedFitting G) = ⊥)
    (hdegrees : Representation.PSL3Three.AbsoluteDegreeWindow.{v})
    (hfield : Representation.PSL3Three.DegreeSixteenFieldObstruction.{v}) :
    Module.finrank (ZMod 2) V = 12 := by
  obtain ⟨F, hF, hfin, hc, ⟨f⟩⟩ := hm
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hc)
  let q := QuotientGroup.mk' (center (generalizedFitting G))
  have hq : Function.Bijective q := by
    refine ⟨?_, QuotientGroup.mk'_surjective _⟩
    rw [← MonoidHom.ker_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hcenter
  let e : generalizedFitting G ≃* Matrix.PSL3Three.PSL :=
    (MulEquiv.ofBijective q hq).trans (f.trans (Atlas.fieldEquivPSL 3 eF))
  let τ := ρ.comp (generalizedFitting G).subtype
  let : IsIrreducible τ := h.irreducible
  let σ := τ.comp e.symm.toMonoidHom
  let : IsIrreducible σ := irreducible_comp_equiv τ e.symm
  have hf : Function.Injective σ :=
    (h.faithful.comp Subtype.val_injective).comp e.symm.injective
  exact Nat.le_antisymm
    (Representation.PSL3Three.binary_degree_twelve_of_absolute_calculations
      hdegrees hfield σ hf (by omega)).le hdim

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankThree
