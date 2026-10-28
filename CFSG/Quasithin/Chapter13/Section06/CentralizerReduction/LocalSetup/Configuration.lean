module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule

/-!
# The constructed marked A₅ local configuration

Starting with an unaligned `FlagSource`, the finite Sylow calculation constructs
z generating the actual V₁ and v in V₂ − V₁, while relabelling both action maps
and preserving the kernel O₂(L). On that same marking, the local normalizer
argument constructs a Sylow subgroup of C_G(v) with ambient image C_T(v).
Earlier 13.3.2/5 and 3.3.2 supply the outside local subgroup and centralizer
vanishing; 13.5.10/12 give the abelian spans; 13.2.4/5 and 12.2.6 give the
Baumann, Thompson and normalizer conclusions of 13.6.4–5.

The residual calculation identifies the image of O²(C_L(v)) with the actual
cubic subgroup, with kernel O₂(Lᵥ). Its multiplication map realizes
Vᵥ = ⟨v⟩ × [V,Lᵥ], and its checked image is the faithful irreducible natural
binary module of rank two. The same a is an ambient conjugate of z, centralizes
Lᵥ, and has a nonidentity central image in the literal checked Sylow subgroup.
Fusion control from 13.2.6(2) identifies the three singular vectors; their
product v gives the full normalizer reduction preceding 13.6.8.

`localConfiguration_of_earlier_source` discharges every module, local-index,
Sylow, and geometric premise of these constructions. Only `FlagSource`, the
specified genuine earlier statements in `EarlierLocal`, earlier fusion, and
the 13.6 counterexample condition are inputs. Their derivation from the full
Hypothesis 13.3.1 remains with the section assembly owner (the earlier-source
producers are qt-13-02-a5-prelim, qt-13-03-preliminaries and qt-13-05).
This conditional construction does not assert the later characteristic-two
statement 13.6.6.

The earlier `LocalReductions` interface is re-exported unchanged through the
flag module; its implementation is below the assembly to avoid an import cycle.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.926–928; Notations 12.2.5 and 13.2.1, printed pp.796 and 877.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open Subgroup Stellmacher ChapterB A5Module
open scoped BigOperators IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}

/-- Constructed local groups, module and geometry on one flag marking.
All fields are conclusions; the construction below takes only the unaligned
module and the specified earlier-source inputs. -/
structure LocalConfiguration (M : Subgroup G) (f : FlagMarking T L V V₁ V₂) where
  reductions : LocalReductions T L M V (markedZ f.module) (markedV f.module)
  residual_kernel : (residualAction f.module).ker = pCore 2 (Lv L (markedV f.module))
  residual_image : (residualAction f.module).range = ResidualCoordinates.cubicGroup
  residual_card : Nat.card (Lv L (markedV f.module) ⧸ pCore 2 (Lv L (markedV f.module))) = 3
  span_eq : Vv L (markedZ f.module) (markedV f.module) =
    zpowers (markedV f.module) ⊔ ⁅V, Lv L (markedV f.module)⁆
  line_disjoint : Disjoint (zpowers (markedV f.module)) ⁅V, Lv L (markedV f.module)⁆
  product : zpowers (markedV f.module) × ↥(⁅V, Lv L (markedV f.module)⁆ : Subgroup G) ≃*
    Vv L (markedZ f.module) (markedV f.module)
  product_apply : ∀ x y, (product (x, y) : G) = (x : G) * (y : G)
  natural : CheckedNaturalData f.module
  checked_commutator : checkedVv f.module = ⁅checkedV f.module, checkedLv f.module⁆
  aPoint : Tv (T : Subgroup G) (markedV f.module)
  aPoint_val : (aPoint : G) = markedA f.module
  a_conjugate : ∃ c : G, MulAut.conj c (markedZ f.module) = markedA f.module
  a_centralizes : markedA f.module ∈ V ⊓ centralizer (Lv L (markedV f.module) : Set G)
  a_checked_nonidentity :
    (checkedSylowMap (T : Subgroup G) (markedV f.module)).rangeRestrict aPoint ≠ 1
  a_checked_central :
    (checkedSylowMap (T : Subgroup G) (markedV f.module)).rangeRestrict aPoint ∈
      center (checkedSylowMap (T : Subgroup G) (markedV f.module)).range
  singular_intersection : ∀ x : Vv L (markedZ f.module) (markedV f.module),
    x ∈ singularPoints f.module ↔ ∃ c : G, MulAut.conj c (markedZ f.module) = (x : G)
  singular_card : (singularPoints f.module).card = 3
  singular_product :
    letI := span_abelian f.module
    ((∏ x ∈ singularPoints f.module, x : Vv L (markedZ f.module) (markedV f.module)) : G) =
      markedV f.module

/-- Assemble 13.6.2–5 and the singular-product normalizer reduction on the
constructed flag. The flag index, outside local subgroup, global Sylow witness,
residual module and checked central point are all constructed, not hypotheses.
The earlier-source inputs remain the responsibility of the section owner. -/
theorem localConfiguration_of_earlier_source
    (d : FlagSource T L V V₁ V₂) (M V₃ : Subgroup G)
    (e : EarlierLocal T L M V V₂ V₃ (markedZ d.flag.module))
    (hcounter : IsA5Counterexample G)
    (hfusion : ControlsFusionOfZ d.flag.module) :
    Nonempty (LocalConfiguration M d.flag) := by
  obtain ⟨r⟩ := localReductions_of_flagSource d M V₃ e hcounter hfusion
  obtain ⟨aT, ha, hane, hac⟩ := d.flag_checkedPoint
  obtain ⟨hcard, hspan, hdisjoint, hchecked, hconj, hcentral⟩ := d.flag.residual_and_checked
  exact ⟨{
    reductions := r
    residual_kernel := residualAction_kernel d.flag.module d.flag.action_kernel
    residual_image := residualAction_range d.flag.module
    residual_card := hcard
    span_eq := hspan
    line_disjoint := hdisjoint
    product := spanProductEquiv d.flag.module
    product_apply := spanProductEquiv_apply d.flag.module
    natural := d.flag.checkedNaturalData
    checked_commutator := hchecked
    aPoint := aT
    aPoint_val := ha
    a_conjugate := hconj
    a_centralizes := hcentral
    a_checked_nonidentity := hane
    a_checked_central := hac
    singular_intersection := mem_singularPoints_iff d.flag.module hfusion
    singular_card := singularPoints_card d.flag.module
    singular_product := singularPoints_product d.flag.module }⟩

/-- Existential form retaining the relation between the original action and
the constructed marking. Relabelling preserves its given two-core kernel. -/
theorem exists_localConfiguration_of_earlier_source
    (d : FlagSource T L V V₁ V₂) (M V₃ : Subgroup G)
    (e : EarlierLocal T L M V V₂ V₃ (markedZ d.flag.module))
    (hcounter : IsA5Counterexample G)
    (hfusion : ControlsFusionOfZ d.flag.module) :
    ∃ f : FlagMarking T L V V₁ V₂,
      (∃ g : Equiv.Perm (Fin 5), f.module = d.module.relabel g) ∧
      Nonempty (LocalConfiguration M f) :=
  ⟨d.flag, d.flag_relabel, localConfiguration_of_earlier_source d M V₃ e hcounter hfusion⟩

namespace LocalConfiguration
variable {M : Subgroup G} {f : FlagMarking T L V V₁ V₂} (c : LocalConfiguration M f)

/-- All three quotient kernels, on the literal maps used by the configuration.
In particular the faithful natural action kills exactly O₂(Lᵥ) when pulled back
to Lᵥ, whereas the ambient checked map kills exactly the specified v-line. -/
theorem quotient_kernels :
    (checkedQuotientMap (markedV f.module)).ker = vLine (markedV f.module) ∧
    (checkedSylowMap (T : Subgroup G) (markedV f.module)).ker =
      (vLine (markedV f.module)).comap (inclusion inf_le_right) ∧
    (c.natural.action.comp (QuotientGroup.mk' (pCore 2 (Lv L (markedV f.module))))).ker =
      pCore 2 (Lv L (markedV f.module)) := by
  refine ⟨checkedQuotientMap_kernel _, checkedSylowMap_kernel _ _, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ c.natural.faithful, QuotientGroup.ker_mk']

/-- The marked a is central and nonidentity in the literal quotient image of
the constructed Sylow subgroup of C_G(v), not just an abstract isomorphic group. -/
theorem checkedPoint_on_sylow :
    ∃ aP : (c.reductions.centralizerSylow : Subgroup (Gv (markedV f.module))).map
        (QuotientGroup.mk' (vLine (markedV f.module))),
      aP.val =
        checkedSylowMap (T : Subgroup G) (markedV f.module) c.aPoint ∧
      aP ≠ 1 ∧ aP ∈ center
        ((c.reductions.centralizerSylow : Subgroup (Gv (markedV f.module))).map
          (QuotientGroup.mk' (vLine (markedV f.module)))) := by
  rw [c.reductions.checked_sylow_image]
  exact ⟨(checkedSylowMap (T : Subgroup G) (markedV f.module)).rangeRestrict c.aPoint,
    rfl, c.a_checked_nonidentity, c.a_checked_central⟩

/-- The same source generator is nonidentity and central in the constructed
Sylow subgroup, with its ambient value retained for the subsequent local
characteristic-two and component arguments. -/
theorem z_in_sylow_center :
    ∃ zP : c.reductions.centralizerSylow,
      ((zP : Gv (markedV f.module)) : G) = markedZ f.module ∧
      zP ≠ 1 ∧ zP ∈ center c.reductions.centralizerSylow := by
  have hz := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp f.z_central
  have hzimage : markedZ f.module ∈
      (c.reductions.centralizerSylow : Subgroup (Gv (markedV f.module))).map
        (Gv (markedV f.module)).subtype := by
    rw [c.reductions.sylow_image]
    exact ⟨hz.1, markedZ_mem_Gv f.module⟩
  obtain ⟨z, hzP, hzG⟩ := hzimage
  let zP : c.reductions.centralizerSylow := ⟨z, hzP⟩
  refine ⟨zP, hzG, ?_, mem_center_iff.mpr ?_⟩
  · intro he
    apply markedZ_ne_one f.module
    exact hzG.symm.trans
      (congrArg (fun q : c.reductions.centralizerSylow =>
        ((q : Gv (markedV f.module)) : G)) he)
  · intro t
    apply Subtype.ext
    apply Subtype.ext
    change ((t : Gv (markedV f.module)) : G) * (z : G) =
      (z : G) * ((t : Gv (markedV f.module)) : G)
    change (z : G) = markedZ f.module at hzG
    rw [hzG]
    have ht : ((t : Gv (markedV f.module)) : G) ∈ Tv (T : Subgroup G) (markedV f.module) := by
      rw [← c.reductions.sylow_image]
      exact mem_map.mpr ⟨t, t.property, rfl⟩
    exact hz.2.2 _ ht.1

end LocalConfiguration
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
