module

public import Stellmacher.SectionNine.NineTenNormalizedFactor
public import Stellmacher.SectionNine.NineResidualCanonicalDerived
public import Stellmacher.SectionOne.OneSevenDerivedModuleProduct

/-!
# The order-three residual factors in the normalized terminal action

The actual normalized transvection action yields the source's residual
and module decompositions. The geometric terminal residual image is an
internal product of order-three groups; their four-element commutator
supports, together with the residual's fixed subgroup, form the whole
terminal module modulo its center. The derived subgroup of the canonical
transvection factor occurs among the residual factors.

Keep the normalized path, both explicit source noncontainments, actual
transvection actor, exact conjugation-action formula, two-core kernel,
and faithful Section One hypotheses. Enumerate the action's actual
canonical factors and take their derived subgroups. The local residual
identification gives the precise geometric group, and the derived
module-product theorem gives the corresponding supports and fixed part.

This proves the conditional normalized form of Stellmacher (9.10)(3)--(4),
printed p.57 of `refs/files/stellmacher-n-group.pdf`. It does not assert
the later reversed critical pair or the final critical-distance bound.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_normalized_residual_product
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
      (¬ ZAt ctx.Γ cp.a' ≤ VAt ctx.Γ cp.firstStep) ∧
      (¬ ZAt ctx.Γ cp.firstStep ≤ VAt ctx.Γ cp.a') ∧
      ∃ actor : GAt ctx.Γ cp.a',
        (actor : G) ∈ ZAt ctx.Γ cp.a ∧
        (actor : G) ∉ QAt ctx.Γ cp.a' ∧
        ∃ hN : ((ZAt ctx.Γ cp.a').subgroupOf (VAt ctx.Γ cp.a')).Normal,
          let _ := hN
          let P := GAt ctx.Γ cp.a'
          let U := VAt ctx.Γ cp.a'
          let Z := ZAt ctx.Γ cp.a'
          ∃ hW : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
            let _ := hW
            ∃ action : P →* MulAut (U ⧸ Z.subgroupOf U),
              let X := action.range
              let W := U ⧸ Z.subgroupOf U
              let residual := ((EAt ctx.Γ cp.a').subgroupOf P).map action.rangeRestrict
              let canonical := ⁅SectionOne.oddCore X,
                  Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
                Subgroup.zpowers (action.rangeRestrict actor)
              (∀ mover : P, ∀ point : U,
                action mover (QuotientGroup.mk' (Z.subgroupOf U) point) =
                  QuotientGroup.mk' (Z.subgroupOf U)
                    ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
                      (Subgroup.mem_normalizer_iff.mp
                        (stabilizer_le_normalizer_v ctx.Γ cp.a' mover.property) point).mp
                          point.property⟩) ∧
              action.ker = pCore 2 P ∧
                SectionOne.Hypotheses X W ∧
                SectionOne.IsOneSevenFactor (V := W) canonical ∧
                ∃ (n : ℕ) (F : Fin n → Subgroup X),
                  (∃ i, F i = (commutator canonical).map canonical.subtype) ∧
                  IsInternalDirectProductFamily residual F ∧
                  (∀ i, Nat.card (F i) = 3 ∧ Nat.card (commutatorAction (F i) W) = 4) ∧
                  IsInternalDirectProductFamily (⊤ : Subgroup W)
                    (fun i : Option (Fin n) => match i with
                      | none => FixedPoints.subgroup residual W
                      | some i => commutatorAction (F i) W) := by
  classical
  obtain ⟨cp, hlength, hcomm, hterminal, hfirst, actor, hactor, hactorNot,
    hN, hW, action, hformula, hkernel, hyp, hcanonical⟩ :=
    nine_ten_normalized_first_factor ctx hb hterminalNot hfirstNot
  let _ := hN
  let _ := hW
  let X := action.range
  let W := VAt ctx.Γ cp.a' ⧸
    (ZAt ctx.Γ cp.a').subgroupOf (VAt ctx.Γ cp.a')
  let factors := SectionOne.oneSevenFactors (G := X) (V := W)
  let E := SectionOne.oneSevenGenerated (G := X) (V := W)
  let canonical : Subgroup X :=
    ⁅SectionOne.oddCore X, Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
      Subgroup.zpowers (action.rangeRestrict actor)
  let normalizedCtx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    { ctx with criticalPath := cp, commutator_eq := hcomm }
  have hbound : 1 < normalizedCtx.criticalPath.length := by
    change 1 < cp.length
    rw [hlength]
    exact hb
  have hneighbor := (nine_three_initial_extraction_inputs normalizedCtx.toLocalContext hbound).1
  have hadj := (mem_neighborhood_iff_adjacent ctx.Γ).mp hneighbor
  have hkernel' : pCore 2 (GAt ctx.Γ cp.a') ≤ action.rangeRestrict.ker :=
    ((MonoidHom.ker_rangeRestrict action).trans hkernel).symm.le
  have hresidual := nine_local_residual_eq_canonical_derived normalizedCtx.toLocalContext
    cp.a' _ hadj action.rangeRestrict action.rangeRestrict_surjective hkernel' hyp _ hcanonical
  change ((EAt ctx.Γ cp.a').subgroupOf (GAt ctx.Γ cp.a')).map action.rangeRestrict =
    (commutator E).map E.subtype at hresidual
  let sylow : Sylow 2 X := default
  obtain ⟨_, hproduct, _⟩ := SectionOne.oneSeven_global_product hyp sylow
  let I := {factor : Subgroup X // factor ∈ factors}
  let n := Fintype.card I
  let enumeration : Fin n ≃ I := (Fintype.equivFin I).symm
  let D : Fin n → Subgroup X := fun i => (enumeration i).val
  have hDi (i : Fin n) : D i ∈ factors := (enumeration i).property
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
  let F := fun i => (commutator (D i)).map (D i).subtype
  obtain ⟨hderived, hcard, hmodule⟩ :=
    SectionOne.oneSevenFactor_derived_module_product hyp D hfactor hinjective E hfamily
  have hselected : ∃ i, F i = (commutator canonical).map canonical.subtype := by
    let selected : I := ⟨_, (SectionOne.mem_oneSevenFactors_iff _).mpr hcanonical⟩
    obtain ⟨i, hi⟩ := enumeration.surjective selected
    have heq : D i = selected.val := congrArg Subtype.val hi
    refine ⟨i, ?_⟩
    dsimp only [F]
    rw [heq]
  refine ⟨cp, hlength, hcomm, hterminal, hfirst, actor, hactor, hactorNot,
    hN, hW, action, hformula, hkernel, hyp, hcanonical, n, F, hselected, ?_, hcard, ?_⟩
  · rw [hresidual]
    exact hderived
  · rw [hresidual]
    exact hmodule

end Stellmacher.SectionNine
