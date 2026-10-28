module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.M24.BlockObstruction.CentralCoordinates
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SimplePowerExtension
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Products
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo

/-!
# No chi-zero blocks in lifted octad locals

The native octad stabilizer maps onto A₈ with elementary kernel of order
sixteen. Central component-orbit coordinates turn a short subnormal block
into a subnormal image in a finite power of this stabilizer. Its central
kernel is a two-group, since the center of a short group lies in F* = O₂.
After applying the native A₈ quotient in every coordinate, each coordinate
image is trivial or all of A₈. The short-group quotient is consequently A₈.
Its order 20160 excludes every actual χ₀ model.

This excludes all χ₀ blocks in the displayed local overgroup, and therefore
also those moved by the supplied J(S). Relative subnormality, the central
cover and permutation of components are retained throughout.

Source: Aschbacher–Smith 2.3.9(7), printed p.526, C.1.7 and C.1.12,
printed pp.123–124; GLS3 Table 5.3e for the native E₁₆.A₈ local.
-/

public section

open Subgroup Theory.GroupTheory Sporadic.Mathieu
open M24LocalGeometry
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion
open CFSG.Quasithin.ChapterC

private theorem short_center_le_core {B : Type*} [Group B] (hB : IsShort B) :
    center B ≤ pCore 2 B := by
  have hn : Group.IsNilpotent (center B) := by
    refine ⟨1, ?_⟩
    rw [Subgroup.upperCentralSeries_one_eq_top_iff]
    infer_instance
  rw [← hB.fitting]
  exact (show center B ≤ fittingSubgroup B from
    le_sSup ⟨inferInstance, hn⟩).trans (fitting_le_generalizedFitting B)

private theorem quotient_equiv_of_central_coordinates {B P T : Type*}
    [Group B] [Group P] [Finite P] [Group T] [IsSimpleGroup T]
    (hB : IsShort B) (hTcenter : center T = ⊥) (hTtwo : ¬ IsPGroup 2 T)
    {n : ℕ} (q : B →* (Fin n → P)) (hqc : q.ker ≤ center B)
    (hqs : q.range.IsSubnormal)
    (f : P →* T) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nonempty ((B ⧸ pCore 2 B) ≃* T) := by
  obtain ⟨F, hF, hFk⟩ := power_surjection_kernel_isPGroup (I := Fin n) f hf hk
  let g := F.comp q
  have hqk : IsPGroup 2 q.ker := pCore_isPGroup.to_le (hqc.trans (short_center_le_core hB))
  have hgk : IsPGroup 2 g.ker := by
    change IsPGroup 2 (F.comp q).ker
    rw [← MonoidHom.comap_ker]
    exact hFk.comap_of_ker_isPGroup q hqk
  have hgs : g.range.IsSubnormal := by
    rw [MonoidHom.range_comp]
    exact hqs.map hF
  apply hB.quotient_equiv_of_simple_coordinates hTcenter hTtwo g hgk
  intro i
  let ev := Pi.evalMonoidHom (fun _ : Fin n => T) i
  have hev : Function.Surjective ev := fun t => ⟨fun _ => t, rfl⟩
  have hs : (ev.comp g).range.IsSubnormal := by
    rw [MonoidHom.range_comp]
    exact hgs.map hev
  rcases hs.eq_bot_or_top_of_isSimpleGroup inferInstance with hh | hh
  · exact Or.inl (MonoidHom.range_eq_bot_iff.mp hh)
  · exact Or.inr (MonoidHom.range_eq_top.mp hh)

private theorem octad_alternating_quotient (O : Octad) :
    ∃ f : octadStabilizer O →* alternatingGroup (Fin 8),
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  classical
  let e₈ : LinearFourCore.seedOctad.val ≃ Fin 8 :=
    Finset.equivFinOfCardEq (m24Blocks_card _ LinearFourCore.seedOctad.property)
  let a := e₈.altCongrHom
  obtain ⟨g, hg⟩ := exists_smul_octad_eq LinearFourCore.seedOctad O
  have hs : octadStabilizer O =
      (octadStabilizer LinearFourCore.seedOctad).map (MulAut.conj g).toMonoidHom := by
    change MulAction.stabilizer M24 O.val =
      (MulAction.stabilizer M24 LinearFourCore.seedOctad.val).map _
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  let e : octadStabilizer O ≃* octadStabilizer LinearFourCore.seedOctad :=
    (((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hs.symm)).symm
  let t := LinearFourCore.alternatingAction
  have htk : IsPGroup 2 t.ker := by
    have he : t.ker = (LinearFourCore.action LinearFourCore.seedOctad).ker := by
      ext x
      change (t x = 1) ↔ LinearFourCore.action LinearFourCore.seedOctad x = 1
      simp only [t, Subtype.ext_iff, LinearFourCore.alternatingAction_coe, Subgroup.coe_one]
    rw [he]
    exact IsPGroup.of_card (p := 2) (n := 4) (by simpa using LinearFourCore.kernel_card)
  let f := a.toMonoidHom.comp (t.comp e.toMonoidHom)
  refine ⟨f, a.surjective.comp (LinearFourCore.alternatingAction_surjective.comp e.surjective), ?_⟩
  have hk : f.ker = t.ker.comap e.toMonoidHom := by
    ext x
    change a (t (e x)) = 1 ↔ t (e x) = 1
    exact map_eq_one_iff a a.injective
  rw [hk]
  exact htk.comap_of_injective e.toMonoidHom e.injective

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Every χ₀ block is excluded, even before imposing movement by J(S). -/
theorem no_chiZeroBlock_in_octad (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) (O : Octad)
    (hinter : L ⊓ localOvergroup d ((S : Subgroup H).map H.subtype) (octadStabilizer O) =
      lift d (octadStabilizer O))
    (B : Subgroup (localOvergroup d ((S : Subgroup H).map H.subtype) (octadStabilizer O))) :
    ¬ IsChiZeroBlockIn B := by
  intro hB
  obtain ⟨n, q, hqc, hqs⟩ := block_central_coordinates h d (octadStabilizer O) hinter B hB.1
  obtain ⟨f, hf, hk⟩ := octad_alternating_quotient O
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hc : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have htwo : ¬ IsPGroup 2 (alternatingGroup (Fin 8)) := by
    intro hp
    obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
    rw [hc] at hn
    have hd : 3 ∣ 2 ^ n := (by decide : 3 ∣ 20160).trans hn
    have := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at this
  obtain ⟨e⟩ := quotient_equiv_of_central_coordinates hB.1.short
    (alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 8)))
    htwo q hqc hqs f hf hk
  exact LieType.not_chiZero_of_quotient_card_20160
    ((Nat.card_congr e.toEquiv).trans hc) hB.2

/-- The octad branch of the actual lifted M₂₄ block obstruction. -/
theorem octad_blockObstruction (h : LocalSetup H L M S z)
    (d : SporadicQuotientInput L z .m24) (O : Octad)
    (hinter : L ⊓ localOvergroup d ((S : Subgroup H).map H.subtype) (octadStabilizer O) =
      lift d (octadStabilizer O)) :
    BlockObstruction M ((S : Subgroup H).map H.subtype)
      (localOvergroup d ((S : Subgroup H).map H.subtype) (octadStabilizer O)) := by
  intro B hB _
  exact (no_chiZeroBlock_in_octad h d O hinter B hB).elim
end CFSG.Quasithin.Chapter2.ComponentRefinement.M24Exclusion

end
