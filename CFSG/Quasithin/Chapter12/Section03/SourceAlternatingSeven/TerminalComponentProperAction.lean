module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperSource
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentMaximal
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceConclusion
public import Theory.Representation.BinarySevenCode.SylowFivePlacement

/-!
# The escaping A₅ as an original weight-two point residual

Restrict the marked A₇ projection to the actual perfect subgroup K.
Its solvable kernel lies in O₂(K), so its image is A₅. Sylow normalization
places that image on five complementary letters and forces the remaining
weight-two word to be fixed by the entire original Sylow subgroup.

The point residual has the same image. Perfect containment through the
central-by-two kernel identifies it with K: the intrinsic two-core lies
in the restricted Sylow and normalizes both subgroups. Source 12.3.7(2)
therefore proves K=[K,J(T)] in the proper branch. The final theorem joins
this with the checked maximal branch.

The explicit ResidualAnalysis input is the remaining 12.2.7 recognition
obligation owned by qt-d-1231-terminal-component. That same owner retains
the natural-module transport and final ComponentAnalysis assembly.
Source: Aschbacher--Smith, Lemmas 12.3.7 and 12.3.12, printed pp.809,811.
-/

@[expose] public noncomputable section
open Subgroup
open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

/-- A perfect Sylow-normalized subgroup with A₅ two-core quotient is the
actual residual of a Sylow-central weight-two point. Both subgroups are
compared under the original marked projection, including its central cover. -/
theorem Setup.LocalAnalysis.exists_central_weight_two_residual (D : S.LocalAnalysis)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (K : Subgroup G) [Group.IsPerfect K] (hKL : K ≤ L)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    ∃ v : V, weight (D.model.coordinates v).toAdd.val = 2 ∧
      (v : G) ∈ centralizer (T : Set G) ∧ K = SylowNormalizer.pointResidual L (v : G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B := K.subgroupOf L
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKL).symm.toMonoidHom)
    (subgroupOfEquivOfLe hKL).symm.surjective
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKL) (pCore_map_iso 2 _)).trans e
  have hker : S.projection.ker = centralPreimage (pCore 2 L) := by
    change (S.quotient.toMonoidHom.comp (QuotientGroup.mk' _)).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ S.quotient.injective,QuotientGroup.ker_mk']
    rfl
  let : Group.IsSolvable S.projection.ker := hker ▸ centralPreimage_pCore_isSolvable 2
  let j : (S.projection.subgroupMap B).ker →* S.projection.ker := {
    toFun := fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let : Group.IsSolvable (S.projection.subgroupMap B).ker :=
    Group.isSolvable_of_isSolvable_injective (f := j) (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : S.projection.ker => (z : L)) h)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  have hkb : (S.projection.subgroupMap B).ker ≤ pCore 2 B := by
    rw [← radical_eq_core_of_perfect_simple_core_quotient]
    exact le_solvableRadical _ inferInstance inferInstance
  have htwo : IsPGroup 2 (S.projection.subgroupMap B).ker :=
    pCore_isPGroup.of_injective (inclusion hkb) (inclusion_injective hkb)
  let eImage := alternatingGroup.SevenFiveSection.imageFiveEquiv S.projection B htwo eB
  obtain ⟨U,hU⟩ := (T.subtype
    (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  have hU' : (U : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using hU
  have hUT : (U : Subgroup L) ≤ (T : Subgroup G).subgroupOf L := by
    intro x hx
    exact (show (x : G) ∈ (T : Subgroup G) ⊓ L from
      hU' ▸ mem_map_of_mem L.subtype hx).1
  have hUB : (U : Subgroup L) ≤ normalizer (B : Set L) :=
    (hUT.trans (comap_mono hTK)).trans (le_normalizer_comap L.subtype)
  have hUI : ((U.mapSurjective S.projection_surjective) : Subgroup (alternatingGroup (Fin 7))) ≤
      normalizer (B.map S.projection : Set (alternatingGroup (Fin 7))) :=
    (map_mono hUB).trans (le_normalizer_map S.projection)
  obtain ⟨w,hw,hfive,hn⟩ := WeightTwoGeometry.exists_weight_two_of_sylow_normalizes_five (B.map S.projection)
    eImage (U.mapSurjective S.projection_surjective) hUI
  let v := D.model.coordinates.symm (Multiplicative.ofAdd w)
  have hv : (D.model.coordinates v).toAdd = w := D.model.coordinates.apply_symm_apply _
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) :=
    ((structural G T L S.hypothesis).2.2 V S.chosen).1
  have hKV : K ≤ normalizer (V : Set G) := hKL.trans S.chosen.normalizes
  have hmap : (K.subgroupOf (normalizer (V : Set G))).map D.model.permutation =
      (B.map S.projection).map (alternatingGroup (Fin 7)).subtype := by
    ext a
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨S.projection ⟨k,hKL hk⟩,⟨⟨k,hKL hk⟩,hk,rfl⟩,
        (D.component_action ⟨k,hKL hk⟩).symm⟩
    · rintro ⟨a,⟨k,hk,rfl⟩,rfl⟩
      exact ⟨⟨k,hKV hk⟩,hk,D.component_action k⟩
  have hc : (v : G) ∈ centralizer (T : Set G) := by
    intro t ht
    let n : normalizer (V : Set G) := ⟨t,hTV ht⟩
    have hnK : n ∈ normalizer
        (K.subgroupOf (normalizer (V : Set G)) : Set (normalizer (V : Set G))) :=
      le_normalizer_comap (normalizer (V : Set G)).subtype (show n ∈
        (normalizer (K : Set G)).comap (normalizer (V : Set G)).subtype from hTK ht)
    have hp := le_normalizer_map D.model.permutation (mem_map_of_mem D.model.permutation hnK)
    rw [hmap] at hp
    have hwfix := (WeightTwoGeometry.mem_symmetricStabilizer _ w).mp (hn hp)
    have he := D.model.equivariant n v
    rw [hv,hwfix] at he
    have he' : V.normalizerMonoidHom n v = v :=
      D.model.coordinates.injective (Multiplicative.toAdd.injective (he.trans hv.symm))
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he')
  let E : S.NaturalCoordinates :=
    ⟨D.model.coordinates,fun l v => by
      simpa only [D.component_action] using
        D.model.equivariant ⟨l,S.chosen.normalizes l.property⟩ v⟩
  let C := SylowNormalizer.pointResidual L (v : G)
  have hCL : C ≤ L := (SylowNormalizer.pointResidual_le L (v : G)).trans inf_le_left
  let A := C.subgroupOf L
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hCL).symm.toMonoidHom)
    (subgroupOfEquivOfLe hCL).symm.surjective
  have hi : A.map S.projection = B.map S.projection :=
    (E.point_residual_image v (hv ▸ hw)).trans (hv ▸ hfive)
  have hUA : (U : Subgroup L) ≤ normalizer (A : Set L) :=
    (hUT.trans (comap_mono
      (SylowNormalizer.pointResidual_normalized S.chosen.sylow_normalizes_component hc))).trans
        (le_normalizer_comap L.subtype)
  have hcore : pCore 2 L ≤ (U : Subgroup L) := pCore_isPGroup.le_sylow_of_normal U
  let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
  have hN : pCore 2 L ≤ S.projection.ker := hker.symm ▸ le_centralPreimage _
  have hcentral : S.projection.ker.map (QuotientGroup.mk' (pCore 2 L)) ≤
      center (L ⧸ pCore 2 L) := by rw [hker]; exact map_comap_le _ _
  have heq : B = A := le_antisymm
    (perfect_le_of_map_le_of_kernel_central_mod_solvable S.projection (pCore 2 L)
      hN hcentral B A (hcore.trans hUA) hi.ge)
    (perfect_le_of_map_le_of_kernel_central_mod_solvable S.projection (pCore 2 L)
      hN hcentral A B (hcore.trans hUB) hi.le)
  refine ⟨v,hv ▸ hw,hc,?_⟩
  have hh := congrArg (map L.subtype) heq
  simpa only [B,A,map_subgroupOf_eq_of_le hKL,map_subgroupOf_eq_of_le hCL] using hh

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- The proper-overcomponent application of source 12.3.7(2), on the
original escaping residual and the original Thompson subgroup. -/
theorem thompson_generation_in_overcomponent
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (R : P.ResidualAnalysis) {Y W : Subgroup G} (hKY : P.K ≤ Y)
    (SY : Setup T Y W) (DY : SY.LocalAnalysis) :
    ⁅P.K,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.K := by
  let : Group.IsPerfect P.K := Chapter1.mem_L_isPerfect R.local_mem
  obtain ⟨v,hv,hvc,hK⟩ := DY.exists_central_weight_two_residual structural P.K hKY
    P.sylow_normalizes_residual R.quotient
  let E : SY.NaturalCoordinates :=
    ⟨DY.model.coordinates,fun l v => by
      simpa only [DY.component_action] using
        DY.model.equivariant ⟨l,SY.chosen.normalizes l.property⟩ v⟩
  obtain ⟨z,hz,hzc⟩ := E.central_representative_weight structural (n := 6)
    (Or.inr (Or.inr rfl))
  let Q : SylowNormalizer.Points E := ⟨v,z,hv,hz,hvc,hzc⟩
  have he := Q.five_thompson_generation_of_weight_six structural escape (by
    intro x _ hx
    apply DY.pointCentralizers x ?_ (Or.inr hx)
    intro he
    have hh : weight (E.coordinates (1 : W)).toAdd.val = 0 := by
      simp only [map_one]; rfl
    rw [he] at hx
    omega)
  change SylowNormalizer.pointResidual Y (v : G) =
    ⁅SylowNormalizer.pointResidual Y (v : G),Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ at he
  rw [← hK] at he
  exact he.symm

/-- Residual recognition suffices for the Thompson conclusion of 12.3.12.
The marked A₇ overcomponent handles the proper branch; the previously
proved maximal action theorem handles the maximal branch. -/
theorem thompson_generation_of_residual
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (localAnalysis : ∀ (Y W : Subgroup G) (SY : Setup T Y W), Nonempty SY.LocalAnalysis)
    (R : P.ResidualAnalysis) :
    ⁅P.K,Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.K := by
  obtain ⟨F⟩ := P.overcomponents_nonempty R.local_mem
  have hKY : P.K ≤ F.Y := F.residual_le.trans F.le_maximal
  by_cases he : P.K = F.Y
  · have hm : P.K ∈ Chapter1.LStar G (T : Subgroup G) := he.symm ▸ F.maximal
    exact (P.maximal_action R.quotient
      ⟨hm,(R.overgroups P.K hm le_rfl).1⟩ (R.maximal_natural hm)).1
  · obtain ⟨W,⟨SY⟩⟩ := (R.overgroups F.Y F.maximal hKY).2.resolve_left he
    obtain ⟨DY⟩ := localAnalysis F.Y W SY
    exact P.thompson_generation_in_overcomponent structural escape R hKY SY DY

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
