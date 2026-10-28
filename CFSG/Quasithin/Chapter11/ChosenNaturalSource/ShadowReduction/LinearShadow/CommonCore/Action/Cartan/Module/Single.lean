module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Line
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Module.Source

/-!
# The Cartan comparison when the component orbit is the chosen seed

If the actual omega-center lies in V, its nonzero coordinate vectors span
field lines invariant under T intersect L. Inner uniqueness identifies
all those lines with the original first flag line. The Cartan action on
that line is scalar. A nonzero fixed vector forces every scalar to be one;
otherwise the omega-center fixed space is zero. This proves the dichotomy
without changing the original flag or conjugation marking.

The source application handles the branch ⟨Z^L⟩ = V, obtains the left
fixed-space vanishing from local uniqueness, and feeds the dichotomy to
the actual Hall comparison. No semisimplicity or split central extension
is assumed. The classification of the orbit and its doubled branch remain
with qt-d-1222-shadow-common-action.

Source: Aschbacher--Smith, 11.3.7(3), printed p.773.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- Inner uniqueness puts all original omega-center vectors in the first flag line. -/
theorem omega_le_flag_line_of_le_seed
    (c : Coordinates D S.field) (f : InvariantFlag c) (hu : f.IsInnerUnique)
    (hZV : omegaCenter T ≤ V) : omegaCenter T ≤ f.Vi 0 := by
  intro z hz
  let v : V := ⟨z,hZV hz⟩
  let w := (c.projection v).toAdd
  apply (c.mem_preimage _ v).mpr
  change w ∈ f.space 0
  by_cases hw : w = 0
  · rw [hw]; exact Submodule.zero_mem _
  let U : Submodule S.field.Carrier c.Space := Submodule.span S.field.Carrier {w}
  have hfix (l : L) (hl : (l : G) ∈ (T : Subgroup G)) :
      c.modelAction (c.quotientMap l) w = w := by
    rw [←c.projection_component_conjugation]
    have he : V.normalizerMonoidHom (inclusion D.normalizes l) v = v := by
      apply Subtype.ext
      change (l : G) * z * (l : G)⁻¹ = z
      exact mul_inv_eq_iff_eq_mul.mpr (omegaCenter_le_sylow_centralizer T hz l hl)
    exact congrArg (fun x : V => (c.projection x).toAdd) he
  have hn : (T : Subgroup G) ⊓ L ≤ normalizer (c.preimage U : Set G) := by
    intro l hl
    apply (c.mem_normalizer_preimage_iff U ⟨l,hl.2⟩).mpr
    intro u
    have he (u : c.Space) (hu : u ∈ U) :
        c.modelAction (c.quotientMap ⟨l,hl.2⟩) u = u := by
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [map_smul,hfix _ hl.1]
    constructor
    · intro hx
      have hx' := he _ hx
      have hi := (c.modelLinearEquiv (c.quotientMap ⟨l,hl.2⟩)).injective
      have hu' : c.modelAction (c.quotientMap ⟨l,hl.2⟩) u = u :=
        hi hx'
      rwa [hu'] at hx
    · intro hx
      rwa [he _ hx]
  have he : U = f.space 0 := hu 0 U (finrank_span_singleton hw) hn
  rw [←he]
  exact Submodule.subset_span (Set.mem_singleton w)


/-- A scalar action on the original line either fixes the whole omega-center or has no fixed points there. -/
theorem omega_fixed_dichotomy_of_line
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (A : Subgroup G) (hAL : A ≤ L) (hn : A ≤ normalizer (f.Vi 0 : Set G))
    (hZline : omegaCenter T ≤ f.Vi 0)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) :
    omegaCenter T ⊓ centralizer (A : Set G) = omegaCenter T ⊓ centralizer (L : Set G) ∨
      ⁅omegaCenter T,A⁆ = ⊥ := by
  have hZV := hZline.trans (D.centralQuotientPreimage_le _)
  have hi : Function.Injective c.projection := by
    apply c.projection.ker_eq_bot_iff.mp
    apply bot_unique
    intro v hv
    exact Subtype.ext (hfixed.le ⟨v.property,(c.projection_eq_one_iff v).mp hv⟩)
  have hzL : omegaCenter T ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hZV).trans hfixed.le)
  by_cases hzero : omegaCenter T ⊓ centralizer (A : Set G) = ⊥
  · exact Or.inl (hzero.trans hzL.symm)
  right
  obtain ⟨z,hz,hz1⟩ := (omegaCenter T ⊓ centralizer (A : Set G)).bot_or_exists_ne_one.resolve_left hzero
  let v : V := ⟨z,hZV hz.1⟩
  have hw : (c.projection v).toAdd ≠ 0 := by
    intro he
    exact hz1 (congrArg Subtype.val (hi (he.trans c.projection.map_one.symm)))
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro y hy d hd
  let l : L := ⟨d,hAL hd⟩
  obtain ⟨a,ha⟩ := line_scalar_of_normalizes c f l (hn hd)
  have hmem : (c.projection v).toAdd ∈ f.space 0 := (c.mem_preimage _ v).mp (hZline hz.1)
  have hzconj : V.normalizerMonoidHom (inclusion D.normalizes l) v = v := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hz.2 d hd)
  have has : a • (c.projection v).toAdd = (c.projection v).toAdd := by
    rw [←ha _ hmem,←c.projection_component_conjugation,hzconj]
  have ha1 : a = 1 := by
    have hh : (a-1) • (c.projection v).toAdd = 0 := by
      rw [sub_smul,one_smul,has,sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_right hw)
  let y' : V := ⟨y,hZV hy⟩
  have hm : (c.projection y').toAdd ∈ f.space 0 := (c.mem_preimage _ y').mp (hZline hy)
  have he := c.projection_component_conjugation l y'
  rw [ha _ hm,ha1,one_smul] at he
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hi (Multiplicative.toAdd.injective he)))

/-- The actual fixed-space consumer in the single-module branch. The common-action
owner retains the proof that the B.5.1 alternatives select this branch or the doubled branch. -/
theorem source_single_component_fixed_spaces
    (cL : Coordinates D S.field) (f : InvariantFlag cL) (hu : f.IsInnerUnique)
    (s : Hypothesis1131At D S U₁ H) (c : NaturalQuotientMarking T H S.field)
    (A X : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X)
    (hsingle : componentOmegaSpan T L = V) :
    omegaCenter T ⊓ centralizer (L : Set G) = ⊥ ∧
      V ⊓ centralizer (L : Set G) = ⊥ ∧
      omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥ := by
  have hAL : oddCartanPart A ≤ L := hAX.trans (hX.1.trans inf_le_left)
  have hv := (source_left_fixed_spaces s c A hA hHall hAL).2
  have hZV : omegaCenter T ≤ V := hsingle ▸ le_conjugateSpanBy (omegaCenter T) L
  have hline := omega_le_flag_line_of_le_seed cL f hu hZV
  have hcases := omega_fixed_dichotomy_of_line cL f (oddCartanPart A) hAL
    (hAX.trans (f.cartan_normalizes hu hX 0)) hline hv
  exact Hall.source_fixed_spaces s (source_omegaClosure_le_sylow s) c A hA hHall hcases

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
