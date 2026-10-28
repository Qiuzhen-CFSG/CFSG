module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Symplectic
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Parabolics
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.LocalActions
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage

/-!
# The marked plane quotient of an original symplectic local component

Proper local components map to parabolic residuals in the actual Sp₄(4)
quotient. The exceptional graph automorphism interchanges the point and
plane residuals. Every automorphism of the SL₂(4) quotient lifts to the
plane local group, by its inner--field description. Correcting by this
lift retains any prescribed original quotient marking.

Consequently a local component with the given SL₂(4) section has an actual
surjection onto the plane local group, with kernel its intersection with
the ambient two-core. The construction retains the original Sylow before
mapping to the model, and no block-recognition assumption is used.

Source: Aschbacher--Smith A.3.12 and the final paragraph of 9.3,
printed pp.47--48,734--735; the rank-one automorphism calculation is
GLS4, Chapter4, Lemma3.1(a).
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem map_residual (a : MulAut (Sp F)) (P : Subgroup (Sp F)) :
    ((solvableResidual P).map P.subtype).map a.toMonoidHom =
      (solvableResidual (P.map a.toMonoidHom)).map (P.map a.toMonoidHom).subtype := by
  let e := P.equivMapOfInjective a.toMonoidHom a.injective
  have h := congrArg (fun D => D.map (P.map a.toMonoidHom).subtype)
    (map_solvableResidual_eq e.toMonoidHom e.surjective)
  rw [map_map] at h
  rw [map_map]
  convert h using 1
  congr 1

theorem local_plane_marking (hF : Nat.card F = 4)
    (S : Sylow 2 (Sp F)) (B : Subgroup (Sp F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤) :
    ∃ a : MulAut (Sp F), B.map a.toMonoidHom = planeLocal := by
  obtain ⟨g,hg⟩ := FiveLocalFF.symplectic_local_placement (n := 2) hF (by decide) S B hB hproper
  rcases hg with hp | hp
  · let a := DiagramAutomorphisms.ExceptionalGraph.graphAut (F := F)
    have ha : pointLocal.map a.toMonoidHom = planeLocal := by
      rw [←pointParabolic_solvableResidual_eq (n := 2) hF (by decide),map_residual,
        DiagramAutomorphisms.ExceptionalGraph.graphAut_map_point,
        planeParabolic_solvableResidual_eq (n := 2) hF (by decide)]
    refine ⟨(MulAut.conj g).trans a,?_⟩
    change B.map (a.toMonoidHom.comp (MulAut.conj g).toMonoidHom) = _
    rw [←map_map,hp,ha]
  · exact ⟨MulAut.conj g,hp⟩

theorem plane_quotient_automorphism_lift (hF : Nat.card F = 4)
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ b : MulAut (planeLocal (F := F)),
      ∀ x, Plane.quotientMap (b x) = a (Plane.quotientMap x) := by
  obtain ⟨g,c,hac,hU,hw⟩ := BenderSuzuki.ZD.Linear.exists_root_weyl_normalization a
  obtain ⟨σ,hσ⟩ := BenderSuzuki.ZD.Linear.eq_sl2FieldAut_of_rootParameter_mul c hU hw
    (BenderSuzuki.ZD.Linear.rootParameter_mul c hU hw)
  obtain ⟨l,hl⟩ := Plane.quotientMap_surjective g
  let b := DiagramAutomorphisms.restrict (DiagramAutomorphisms.fieldAutomorphism σ)
    planeLocal (DiagramAutomorphisms.planeLocal_map (n := 2) hF (by decide) _
      (DiagramAutomorphisms.field_map_planeParabolic σ))
  refine ⟨(MulAut.conj l) * b,?_⟩
  intro x
  change Plane.quotientMap (l * b x * l⁻¹) = _
  rw [map_mul,map_mul,map_inv,hl,hac,hσ]
  rfl

theorem mark_plane_surjection {B : Type*} [Group B] [Finite B]
    (hF : Nat.card F = 4)
    (q : B →* planeLocal (F := F)) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker)
    (e : (B ⧸ pCore 2 B) ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ q' : B →* planeLocal (F := F), Function.Surjective q' ∧ q'.ker = q.ker ∧
      ∀ x, Plane.quotientMap (q' x) = e (QuotientGroup.mk' (pCore 2 B) x) := by
  let e₀ := (q.quotientPCoreEquivOfSurjective hq hk).trans
    (planeLocalCoreQuotientEquiv (n := 2) hF (by decide))
  let a : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := e₀.symm.trans e
  obtain ⟨b,hb⟩ := plane_quotient_automorphism_lift hF a
  refine ⟨b.toMonoidHom.comp q,b.surjective.comp hq,
    MonoidHom.ker_comp_of_injective _ _ b.injective,?_⟩
  intro x
  change Plane.quotientMap (b (q x)) = _
  rw [hb]
  have he₀ : e₀ (QuotientGroup.mk' (pCore 2 B) x) = Plane.quotientMap (q x) := by
    rw [MulEquiv.trans_apply,MonoidHom.quotientPCoreEquivOfSurjective_mk,
      QuotientGroup.mk'_apply,planeLocalCoreQuotientEquiv_mk]
  rw [←he₀]
  exact congrArg e (e₀.symm_apply_apply _)

theorem local_plane_surjection {K : Type*} [Group K] [Finite K]
    (hF : Nat.card F = 4) (S : Sylow 2 K) (B : Subgroup K)
    (hB : B ∈ localCComponents S)
    (eK : (K ⧸ pCore 2 K) ≃* Sp F)
    (eB : (B ⧸ pCore 2 B) ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ q : B →* planeLocal (F := F), Function.Surjective q ∧
      q.ker = (pCore 2 K).subgroupOf B ∧
      ∀ b, Plane.quotientMap (q b) = eB (QuotientGroup.mk' (pCore 2 B) b) := by
  let f := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent
  let : Group.IsSolvable f.ker := hk ▸ inferInstance
  let BI := B.map f
  have hlocal : BI ∈ localCComponents (S.mapSurjective hf) :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hB f
  let fB := f.subgroupMap B
  have hfB : Function.Surjective fB := f.subgroupMap_surjective B
  have hkB : IsPGroup 2 fB.ker := by
    have hi : fB.ker ≤ (pCore 2 K).subgroupOf B := by
      intro b hb
      have hh : f b = 1 := congrArg Subtype.val hb
      exact hk ▸ hh
    exact pCore_isPGroup.comap_subtype.to_le hi
  let eBI := (fB.quotientPCoreEquivOfSurjective hfB hkB).symm.trans eB
  have hproper : BI ≠ ⊤ := by
    intro ht
    let i : BI ≃* Sp F := (MulEquiv.subgroupCongr ht).trans topEquiv
    have hcore : pCore 2 (Sp F) = ⊥ := by
      rw [←pCore_map_iso 2 eK,pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
    let j : (BI ⧸ pCore 2 BI) ≃* Sp F :=
      (QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).trans
        ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot)
    have hc := Nat.card_congr (j.symm.trans eBI).toEquiv
    rw [card_sp,GorensteinWalter.sl2_card_formula,hF] at hc
    norm_num at hc
  obtain ⟨a,ha⟩ := local_plane_marking hF (S.mapSurjective hf) BI hlocal hproper
  let j : BI ≃* planeLocal (F := F) := (a.subgroupMap BI).trans (MulEquiv.subgroupCongr ha)
  let q := j.toMonoidHom.comp fB
  have hq : Function.Surjective q := j.surjective.comp hfB
  have hqk : q.ker = (pCore 2 K).subgroupOf B := by
    rw [MonoidHom.ker_comp_of_injective _ _ j.injective]
    ext b
    change fB b = 1 ↔ (b : K) ∈ pCore 2 K
    rw [←hk]
    change fB b = 1 ↔ f b = 1
    exact ⟨congrArg Subtype.val,fun h => Subtype.ext h⟩
  have hqp : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ j.injective]
    exact hkB
  obtain ⟨q',hq',hk',he'⟩ := mark_plane_surjection hF q hq hqp eB
  exact ⟨q',hq',hk'.trans hqk,he'⟩

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
