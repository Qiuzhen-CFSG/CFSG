module

public import Stellmacher.SectionNine.NineTenNormalizedFactor
public import Stellmacher.SectionOne.OneSevenGlobalProduct
public import Stellmacher.SectionOne.OneSevenModuleProduct

/-!
# The factor product in the normalized terminal action

The source's transvection gives a canonical (1.7) factor in the faithful
terminal action on `V/Z`. The global Section One product theorem lists all
factors of that same action as an internal direct product. Their four-point
commutator supports, together with the product's fixed module, split the
whole terminal quotient module. The selected transvection factor occurs
in this list.

This proves the action-theoretic part of Stellmacher (9.10)(3)--(4),
printed p.57 of `refs/files/stellmacher-n-group.pdf`. It does not identify
the action-defined factor product with the image of the geometric
terminal residual; that identification is a separate source step.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_normalized_factor_product
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hterminalNot :
      ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot :
      ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a') :
    ∃ cp : CriticalPath ctx.Γ,
      cp.length = ctx.criticalPath.length ∧
      ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ cp.a'⁆ = ⊥ ∧
      ∃ actor : GAt ctx.Γ cp.a',
        (actor : G) ∈ ZAt ctx.Γ cp.a ∧
        (actor : G) ∉ QAt ctx.Γ cp.a' ∧
        ∃ hN : ((ZAt ctx.Γ cp.a').subgroupOf (VAt ctx.Γ cp.a')).Normal,
          let _ := hN
          let U := VAt ctx.Γ cp.a'
          let Z := ZAt ctx.Γ cp.a'
          ∃ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
            let _ := hW
            ∃ action : GAt ctx.Γ cp.a' →* MulAut (U ⧸ Z.subgroupOf U),
              let X := action.range
              let W := U ⧸ Z.subgroupOf U
              action.ker = pCore 2 (GAt ctx.Γ cp.a') ∧
              ∃ (n : ℕ) (D : Fin n → Subgroup X),
                (∃ i, D i =
                  (⁅SectionOne.oddCore X,
                      Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
                    Subgroup.zpowers (action.rangeRestrict actor))) ∧
                IsInternalDirectProductFamily (SectionOne.oneSevenGenerated (G := X) (V := W)) D ∧
                (∀ i, SectionOne.IsOneSevenFactor (V := W) (D i)) ∧
                IsInternalDirectProductFamily (⊤ : Subgroup W)
                  (fun i : Option (Fin n) => match i with
                    | none => FixedPoints.subgroup (SectionOne.oneSevenGenerated (G := X) (V := W)) W
                    | some i => commutatorAction (D i) W) := by
  classical
  obtain ⟨cp, hlength, hcomm, _, _, actor, hactor, hactorNot,
    hN, hW, action, _, hkernel, hyp, hcanonical⟩ :=
    nine_ten_normalized_first_factor ctx hb hterminalNot hfirstNot
  let _ := hN
  let _ := hW
  let X := action.range
  let W := VAt ctx.Γ cp.a' ⧸
    (ZAt ctx.Γ cp.a').subgroupOf (VAt ctx.Γ cp.a')
  let F := SectionOne.oneSevenFactors (G := X) (V := W)
  let E := SectionOne.oneSevenGenerated (G := X) (V := W)
  let sylow : Sylow 2 X := default
  obtain ⟨_, hproduct, _⟩ := SectionOne.oneSeven_global_product hyp sylow
  let I := {factor : Subgroup X // factor ∈ F}
  let n := Fintype.card I
  let enumeration : Fin n ≃ I := (Fintype.equivFin I).symm
  let D : Fin n → Subgroup X := fun i => (enumeration i).val
  have hDi (i : Fin n) : D i ∈ F := (enumeration i).property
  have hfactor (i : Fin n) : SectionOne.IsOneSevenFactor (V := W) (D i) :=
    (SectionOne.mem_oneSevenFactors_iff (D i)).mp (hDi i)
  have hinjective : Function.Injective D := by
    intro i j heq
    exact enumeration.injective (Subtype.ext heq)
  have hgen : E = ⨆ i : Fin n, D i := by
    change SectionOne.oneSevenGenerated (G := X) (V := W) = _
    rw [hproduct.1]
    apply le_antisymm
    · apply iSup_le
      intro factor
      obtain ⟨i, rfl⟩ := enumeration.surjective factor
      exact le_iSup D i
    · exact iSup_le fun i => le_iSup (fun factor : I => (factor : Subgroup X))
        (enumeration i)
  have hfamily : IsInternalDirectProductFamily E D := by
    refine ⟨hgen, ?_, ?_⟩
    · intro i j hij
      exact hproduct.2.2.1 (D i) (hDi i) (D j) (hDi j)
        (fun heq => hij (hinjective heq))
    · intro i j hij
      exact hproduct.2.2.2 (D i) (hDi i) (D j) (hDi j)
        (fun heq => hij (hinjective heq))
  have hmodule := SectionOne.oneSevenFactor_module_product hyp D hfactor hinjective E hgen
  have hselected : ∃ i, D i =
      (⁅SectionOne.oddCore X,
          Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
        Subgroup.zpowers (action.rangeRestrict actor)) := by
    let selected : I := ⟨_, (SectionOne.mem_oneSevenFactors_iff _).mpr hcanonical⟩
    obtain ⟨i, hi⟩ := enumeration.surjective selected
    exact ⟨i, congrArg Subtype.val hi⟩
  exact ⟨cp, hlength, hcomm, actor, hactor, hactorNot, hN, hW, action,
    hkernel, n, D, hselected, hfamily, hfactor, hmodule⟩

end Stellmacher.SectionNine
