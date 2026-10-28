module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Coordinates
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.ProjectedSeed

/-!
# Original natural-module recognition and projected seed

The natural coordinates make the intersection [U,L] ∩ C_U(L) trivial.
The image of the original component Sylow subgroup fixes one natural line;
Sylow-fixed representatives of the original seed supply a nonidentity point
on that line. This identifies its stabilizer with the original ML and completes
all clauses of HasNaturalMovedModule for either exchanged source-plane size.

Source: Aschbacher--Smith 15.1.27--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The actual natural moved module, direct splitting, and original projected seed. -/
theorem HasExchangedLinearSource.natural_moved_module
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hfull : V = localModule T M)
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.HasNaturalMovedModule t := by
  obtain ⟨hU,hE,hn,n,hn45,e,x,hx⟩ :=
    s.original_natural_coordinates hG hempty hM hmany hJ hu hne hfull h t ht htS
  let := hU
  let := hE
  let f : d.L →* LinearGroup n :=
    ((e.trans (slEquivLinear n)).toMonoidHom).comp (QuotientGroup.mk' (pCore 2 d.L))
  have hf : Function.Surjective f :=
    (e.trans (slEquivLinear n)).surjective.comp (QuotientGroup.mk'_surjective _)
  have hinter (l : d.L) (v : Additive (d.UL t)) :
      x (Additive.ofMul (ChapterD.UniqueFactor.actionHom d.L (d.UL t) hn l v.toMul)) =
        f l (x v) := hx l v
  have hdim : 2 ≤ Module.finrank (ZMod 2) (Fin n → ZMod 2) := by
    simpa using (show 2 ≤ n by omega)
  have hdis : d.UL t ⊓ (d.U t ⊓ centralizer (d.L : Set G)) = ⊥ := by
    apply bot_unique
    rintro v ⟨hv,hvU,hvC⟩
    let v' : Additive (d.UL t) := Additive.ofMul ⟨v,hv⟩
    have hfixed : x v' ∈ (BinaryParabolicNatural.natural (Fin n → ZMod 2)).invariants := by
      intro g
      obtain ⟨l,rfl⟩ := hf g
      change f l (x v') = x v'
      rw [← hinter]
      apply congrArg x
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hvC l l.property)
    rw [BinaryParabolicNatural.natural_invariants hdim,Submodule.mem_bot] at hfixed
    have hv0 : v' = 0 := x.injective (hfixed.trans x.map_zero.symm)
    exact congrArg (fun w : Additive (d.UL t) => (w.toMul : G)) hv0
  obtain ⟨P,hP⟩ := s.1.component_sylow
  let Q := P.mapSurjective (f := f) hf
  obtain ⟨y,hy0,hy⟩ := BinaryNaturalDual.VectorStabilizers.Pure.linear_sylow_fixed_line
    (show 0 < Module.finrank (ZMod 2) (Fin n → ZMod 2) by omega) Q
  let ZU := d.UL t ⊓ centralizer (d.S : Set G)
  let zmap (v : ZU) : Additive (d.UL t) := Additive.ofMul ⟨v,v.property.1⟩
  have hfixed (v : ZU) : x (zmap v) ∈ BinaryLinear.fixedSpace (Q : Subgroup (LinearGroup n)) := by
    intro g hg
    obtain ⟨l,hl,rfl⟩ := hg
    change f l (x (zmap v)) = x (zmap v)
    rw [← hinter]
    apply congrArg x
    apply Additive.toMul.injective
    apply Subtype.ext
    have hlS : (l : G) ∈ d.S := d.SL_le_S (hP ▸ mem_map_of_mem d.L.subtype hl)
    exact mul_inv_eq_iff_eq_mul.mpr (v.property.2 l hlS)
  have hnonzero (v : ZU) (hv : v ≠ 1) : x (zmap v) ≠ 0 := by
    intro he
    apply hv
    apply Subtype.ext
    exact congrArg (fun w : Additive (d.UL t) => (w.toMul : G))
      (x.injective (he.trans x.map_zero.symm))
  have honly (v : ZU) (hv : v ≠ 1) : x (zmap v) = y := by
    have hh := hfixed v
    rw [hy] at hh
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hh
    have ha0 : a ≠ 0 := by
      intro hz
      exact hnonzero v hv (by simpa only [hz,zero_smul] using ha.symm)
    have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
    simpa only [ha1,one_smul] using ha.symm
  obtain ⟨z,hz,hzC⟩ := Set.not_subset.mp
    (d.exchanged_Z2_not_centralizes_L s.1 hM hu h t ht htS)
  obtain ⟨u,huU,huC⟩ := d.exchanged_Z2_fixed_coset s.1 hG hM hu h
    (s.c27Input hG h) s.cubicFacts t ht hz
  have huS : u ∈ centralizer (d.S : Set G) := by
    have hh := (centralizer (d.S : Set G)).mul_mem
      (centralizer_le (show d.S ≤ d.L ⊔ d.S from le_sup_right) huC.2)
      ((centralizer (d.S : Set G)).inv_mem (d.exchanged_Z2_le_centralizer_S s.1 t ht hz))
    simpa only [mul_inv_cancel_right] using hh
  have hu1 : u ≠ 1 := by
    intro he
    apply hzC
    intro l hl
    simpa only [he,one_mul] using huC.2 l (mem_sup_left hl)
  let u' : ZU := ⟨u,huU,huS⟩
  have hu' : u' ≠ 1 := fun he => hu1 (congrArg Subtype.val he)
  have hline : Nat.card ZU = 2 := by
    apply (Nat.card_eq_two_iff' (1 : ZU)).mpr
    refine ⟨u',hu',?_⟩
    intro v hv
    apply Subtype.ext
    exact congrArg (fun w : Additive (d.UL t) => (w.toMul : G))
      (x.injective ((honly v hv).trans (honly u' hu').symm))
  refine ⟨hU,hE,hn,n,hn45,e,x,hx,?_,hdis,?_⟩
  · exact (d.exchanged_U_split s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht).symm
  · exact d.exchanged_projected_seed s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht htS hline

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
