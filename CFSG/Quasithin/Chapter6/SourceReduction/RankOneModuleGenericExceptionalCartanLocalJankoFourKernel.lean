module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourCubicCore
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoFourCubicCore
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.MixedRow
public import Theory.SpecificGroups.SymmetricFive.EvenInvolutionCentralizer
import all Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.A5Factor
public import Theory.SpecificGroups.SymmetricFive.LocalTwoCore
public import Theory.GroupTheory.PGroup.NormalSubgroupUpperCentralBound

/-!
# The original max1 Cartan actor normalizes the same J₄ residual

The checked Sylow catalogue puts every Sylow-normal elementary eight in
the literal max1 kernel. At a simultaneous max4 marking, that elementary
kernel therefore centralizes the max4 eight. The full eight-centralizer
order kills its SL₃(2) quotient coordinate. Its S₅ coordinate lies in the
even two-core of the original cubic/Sylow overgroup, where a cubic fixes
no nonidentity involution. Thus its cubic-fixed subgroup is exactly the
already identified max4 eight.

The escaping actor normalizes the same max1 kernel and centralizes the
original cubic, so it normalizes this eight. Its full normalizer is max4,
which normalizes the SAME original A₅ residual. This closes the entire
max1 row, including both Mathieu octad and trio placements. The native
application retains the original component quotient and both Hall
conditions; the final component sieve discharges the local-A₅ premise.

The internal imports reuse the existing Sylow marking and literal A₅
factor bodies without changing their public boundaries. All finite
certificates are reused from the imported native model calculations.
Source: Aschbacher--Smith 5.1.13, printed p.637, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open Janko4 Janko4.LocalStructure.SymmetricLinear
open Janko4.Cardinality Janko4.OuterReduction.OddIndex
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds
open Janko4.LocalStructure.SylowNormalEights.MatrixWords
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup max1Subgroup localKernel
private abbrev M₁ : Subgroup Model := max1Subgroup matrixA_mul_self matrixB_pow_four
private abbrev Q₁ : Subgroup Model := (localKernel matrixA_mul_self matrixB_pow_four).map M₁.subtype

private theorem kernel_mask_mem (m : ℕ) : kernelMask m ∈ Q₁ :=
  mem_map_of_mem M₁.subtype (Janko4.Simplicity.Max1Fusion.KernelOrbits.maskValue
    matrixA_mul_self matrixB_pow_four m).property

private theorem family_le_kernel (i : Fin 3) : U i ≤ Q₁ := by
  have h17 : (pcGenerator 17 : Model) ∈ Q₁ := pcGenerator17_eq_kernelMask.symm ▸ kernel_mask_mem 456
  have h18 : (pcGenerator 18 : Model) ∈ Q₁ := pcGenerator18_eq_kernelMask.symm ▸ kernel_mask_mem 1011
  have h19 : (pcGenerator 19 : Model) ∈ Q₁ := ThirdConjugacy.pc19_eq_kernelMask.symm ▸ kernel_mask_mem 1387
  have h20 : (pcGenerator 20 : Model) ∈ Q₁ := ThirdConjugacy.pc20_eq_kernelMask.symm ▸ kernel_mask_mem 198
  change (F i).map twoSubgroup.subtype ≤ _
  rw [map_le_iff_le_comap]
  fin_cases i <;> change Subgroup.closure _ ≤ _
  all_goals
    apply (Subgroup.closure_le _).mpr
    intro x hx
  all_goals rcases (show x = _ ∨ x = _ ∨ x = _ from hx) with rfl | rfl | rfl
  all_goals first | exact h17 | exact h18 | exact h19 | exact h20 | exact Q₁.mul_mem h17 h18

/-- Every elementary normal eight of the marked full Sylow lies in its SAME max1 kernel. -/
private theorem jankoFour_normal_eight_le_kernel (A : Subgroup Model)
    (hAS : A ≤ twoSubgroup) (hn : twoSubgroup ≤ normalizer (A : Set Model))
    (he : IsElementaryAbelian 2 A) (hc : Nat.card A = 8) : A ≤ Q₁ := by
  let B := A.subgroupOf twoSubgroup
  let : B.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 B := he.subgroupOf hAS
  have hb : Nat.card B = 8 := (Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv).trans hc
  obtain ⟨i,hi⟩ := literal_family_coverage B inferInstance inferInstance hb
    (le_upperCentralSeries_of_card_eq_prime_pow twoSubgroup_isPGroup B (by simpa using hb))
  have hh := congrArg (map twoSubgroup.subtype) hi
  rw [map_subgroupOf_eq_of_le hAS] at hh
  exact hh.trans_le (family_le_kernel i)

private abbrev SL := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
private abbrev Sym := Equiv.Perm (Fin 5)
private def linearProjection : max4Subgroup →* SL :=
  (MonoidHom.snd Sym SL).comp max4Projection

/-- Centralizing the certified eight kills the literal SL₃(2) quotient coordinate. -/
private theorem jankoFour_eight_centralizer_linear_trivial :
    centralizer (NormalEight.eight : Set max4Subgroup) ≤ linearProjection.ker := by
  let C := centralizer (NormalEight.eight : Set max4Subgroup)
  have hC : C = (centralizer (max4Eight : Set Model)).subgroupOf max4Subgroup := by
    ext x
    constructor
    · intro hx y hy
      obtain ⟨z,hz,rfl⟩ := hy
      exact congrArg Subtype.val (hx z hz)
    · intro hx y hy
      apply Subtype.ext
      exact hx y (mem_map_of_mem max4Subgroup.subtype hy)
  have hc : Nat.card C = 3932160 := by
    rw [hC,Nat.card_congr (subgroupOfEquivOfLe max4_eight_centralizer_le).toEquiv]
    apply Nat.le_antisymm
    · exact Max4EightCentralizer.centralizer_card_le
        Max4EightCentralizer.marking Max4EightCentralizer.pair_orbit_witness
    · have hh := Max4EightCentralizer.relative_centralizer_card_ge
      rwa [Nat.card_congr (subgroupOfEquivOfLe max4_eight_centralizer_le).toEquiv] at hh
  let := NormalEight.normal_eight
  let : C.Normal := inferInstance
  have hf : Function.Surjective linearProjection := by
    intro x
    obtain ⟨g,hg⟩ := max4Projection_surjective (1,x)
    exact ⟨g,congrArg Prod.snd hg⟩
  let : (C.map linearProjection).Normal := Normal.map inferInstance _ hf
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hb : C.map linearProjection = ⊥ := by
    rcases (inferInstance : (C.map linearProjection).Normal).eq_bot_or_eq_top with hh | hh
    · exact hh
    · have hd := card_map_dvd (f := linearProjection) (H := C)
      rw [hh,card_top,Atlas.Comparisons.Exceptional.sl3Two_card,hc] at hd
      norm_num at hd
  exact (map_eq_bot_iff C).mp hb
private def symmetricProjection : max4Subgroup →* Sym :=
  (MonoidHom.fst Sym SL).comp max4Projection

/-- An elementary Sylow-normal subgroup containing the eight has no
cubic-fixed image in either coordinate of the literal max4 quotient. -/
private theorem jankoFour_kernel_cubic_fixed_le_core (P : Sylow 2 max4Subgroup)
    (Q E : Subgroup max4Subgroup) (hQ : IsElementaryAbelian 2 Q)
    (hQP : Q ≤ (P : Subgroup max4Subgroup))
    (hPQ : (P : Subgroup max4Subgroup) ≤ normalizer (Q : Set max4Subgroup))
    (hEQ : E ≤ normalizer (Q : Set max4Subgroup))
    (h8 : NormalEight.eight ≤ Q) (hE : Nat.card E = 3) (hEA : E ≤ a5Preimage) :
    Q ⊓ centralizer (E : Set max4Subgroup) ≤ pCore 2 max4Subgroup := by
  let := hQ
  have hdis : Disjoint E max4Projection.ker := by
    apply disjoint_of_coprime_natCard
    rw [hE,max4Projection_kernel_eq_twoCore,twoCore_card]
    decide
  have hi : Function.Injective (symmetricProjection.comp E.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply hdis.le_bot
    refine ⟨x.property,?_⟩
    change max4Projection x = 1
    apply Prod.ext
    · exact hx
    · exact (hEA x.property).2
  let : IsCyclic E := isCyclic_of_prime_card hE
  obtain ⟨e,he⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have he3 : orderOf (symmetricProjection e) = 3 :=
    (orderOf_injective (symmetricProjection.comp E.subtype) hi e).trans (he.trans hE)
  let N := E ⊔ (P : Subgroup max4Subgroup)
  have hQN : Q ≤ N := hQP.trans le_sup_right
  have hn : N ≤ normalizer (Q : Set max4Subgroup) := sup_le hEQ hPQ
  let : (Q.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hn
  have hqc : Q.subgroupOf N ≤ pCore 2 N :=
    le_sSup ⟨inferInstance,hQ.isPGroup.comap_subtype⟩
  have hqc' : Q ≤ N.pCoreIn 2 := by
    have hh := map_mono (f := N.subtype) hqc
    rwa [map_subgroupOf_eq_of_le hQN] at hh
  have hf : Function.Surjective symmetricProjection := by
    intro x
    obtain ⟨g,hg⟩ := max4Projection_surjective (x,1)
    exact ⟨g,congrArg Prod.fst hg⟩
  let P5 := P.mapSurjective hf
  have h3 : 3 ∣ Nat.card (N.map symmetricProjection) := by
    have hh := orderOf_dvd_natCard (⟨symmetricProjection e,
      mem_map_of_mem symmetricProjection ((show E ≤ N from le_sup_left) e.property)⟩ : N.map symmetricProjection)
    rwa [←orderOf_coe,he3] at hh
  have hc := Theory.SpecificGroups.SymmetricFive.LocalTwoCore.core_le_alternating
    (N.map symmetricProjection) P5 (map_mono le_sup_right) h3
  have hqeven : Q.map symmetricProjection ≤ alternatingGroup (Fin 5) :=
    (map_mono hqc').trans ((Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_image_le
      symmetricProjection N).trans hc)
  have hQeight : Q ≤ centralizer (NormalEight.eight : Set max4Subgroup) :=
    Q.le_centralizer.trans (centralizer_le h8)
  rintro q ⟨hq,hqe⟩
  have h2 : linearProjection q = 1 := jankoFour_eight_centralizer_linear_trivial (hQeight hq)
  have h1 : symmetricProjection q = 1 := by
    by_contra hne
    have hpow : symmetricProjection q ^ 2 = 1 := by
      rw [←map_pow]
      have hh : (⟨q,hq⟩ : Q)^2 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hQ.exponent_dvd_p _
      have hh' : q ^ 2 = 1 := congrArg (fun z : Q => (z : max4Subgroup)) hh
      rw [hh',map_one]
    have ho : orderOf (symmetricProjection q) = 2 := orderOf_eq_prime hpow hne
    exact Equiv.Perm.three_not_commute_even_involution_five _ _ ho
      (hqeven (mem_map_of_mem _ hq)) he3
      ((show Commute q (e : max4Subgroup) from (hqe e e.property).symm).map symmetricProjection)
  rw [←max4Projection_kernel_eq_twoCore]
  exact Prod.ext h1 h2

private theorem max1_normalizes_kernel : M₁ ≤ normalizer (Q₁ : Set Model) := by
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
    (localKernel matrixA_mul_self matrixB_pow_four).le_normalizer_map M₁.subtype

/-- The normal-eight containment holds at every full Sylow in the same max1. -/
private theorem normal_eight_le_kernel (S : Sylow 2 Model) (hSM : (S : Subgroup Model) ≤ M₁)
    (A : Subgroup Model) (hAS : A ≤ (S : Subgroup Model))
    (hn : (S : Subgroup Model) ≤ normalizer (A : Set Model))
    (he : IsElementaryAbelian 2 A) (hc : Nat.card A = 8) : A ≤ Q₁ := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M₁ (S.subtype hSM) localSylow
  let f := MulAut.conj (g : Model)
  have hSg : (S : Subgroup Model).map f.toMonoidHom = twoSubgroup := by
    have hh := congrArg (fun P : Sylow 2 M₁ => (P : Subgroup M₁).map M₁.subtype) hg
    change (((S : Subgroup Model).subgroupOf M₁).map (MulAut.conj g).toMonoidHom).map
      M₁.subtype = twoSubgroup at hh
    rw [map_map] at hh
    change ((S : Subgroup Model).subgroupOf M₁).map (f.toMonoidHom.comp M₁.subtype) = _ at hh
    rwa [←map_map,map_subgroupOf_eq_of_le hSM] at hh
  let := he
  have hh := jankoFour_normal_eight_le_kernel (A.map f.toMonoidHom)
    (hSg ▸ map_mono hAS)
    (hSg ▸ ((map_mono hn).trans (A.le_normalizer_map f.toMonoidHom)))
    (IsElementaryAbelian.map _) ((card_map_of_injective f.injective).trans hc)
  intro x hx
  exact (mem_normalizer_iff.mp (max1_normalizes_kernel g.property) x).mpr
    (hh (mem_map_of_mem _ hx))

/-- The original residual is normalized once its marked eight is the
fixed subgroup of an elementary kernel normalized by the commuting actor. -/
private theorem kernel_actor_normalizes (S : Sylow 2 Model) (R D E Q : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hS : (S : Subgroup Model) ≤ max4Subgroup)
    (hE : Nat.card E = 3) (hER : E ≤ R)
    (hQ : IsElementaryAbelian 2 Q) (hQS : Q ≤ (S : Subgroup Model))
    (hSQ : (S : Subgroup Model) ≤ normalizer (Q : Set Model))
    (hEQ : E ≤ normalizer (Q : Set Model))
    (hDQ : D ≤ normalizer (Q : Set Model))
    (hDE : ⁅D,E⁆ = ⊥) (h8 : max4Eight ≤ Q) : D ≤ normalizer (R : Set Model) := by
  have hR := jankoFour_residual_le_max4 S R hl hn he hS
  have hE4 := hER.trans hR
  have hQ4 := hQS.trans hS
  let R₄ := R.subgroupOf max4Subgroup
  let E₄ := E.subgroupOf max4Subgroup
  let Q₄ := Q.subgroupOf max4Subgroup
  let := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients.local_perfect hl
  let d := subgroupOfEquivOfLe hR
  let : Group.IsPerfect R₄ := Group.IsPerfect.ofSurjective
    (f := d.symm.toMonoidHom) d.symm.surjective
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := he
  let eR := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans
    (eF.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)
  have hpre : R₄ ≤ a5Preimage := by
    change R₄ ≤ a5Factor.comap max4Projection
    rw [←map_le_iff_le_comap,perfect_five_projection R₄ eR]
  have hEl : Nat.card E₄ = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hE4).toEquiv).trans hE
  have hQl : IsElementaryAbelian 2 Q₄ := hQ.subgroupOf hQ4
  have hPc : (S.subtype hS : Subgroup max4Subgroup) ≤ normalizer (Q₄ : Set max4Subgroup) := by
    rw [←subgroupOf_normalizer_eq hQ4]
    exact comap_mono hSQ
  have hEc : E₄ ≤ normalizer (Q₄ : Set max4Subgroup) := by
    rw [←subgroupOf_normalizer_eq hQ4]
    exact comap_mono hEQ
  have h8l : NormalEight.eight ≤ Q₄ := by
    intro x hx
    exact h8 (mem_map_of_mem max4Subgroup.subtype hx)
  have hfix := jankoFour_kernel_cubic_fixed_le_core (S.subtype hS) Q₄ E₄ hQl
    (comap_mono hQS) hPc hEc h8l hEl ((comap_mono hER).trans hpre)
  have h8eq := jankoFour_same_cubic_fixed_core S R E hl hn
    ⟨F,inferInstance,inferInstance,hF,⟨eF⟩⟩ hE hER hS
  have hfixed : Q ⊓ centralizer (E : Set Model) = max4Eight := by
    apply le_antisymm
    · rintro x ⟨hx,hxe⟩
      let y : max4Subgroup := ⟨x,hQ4 hx⟩
      have hy : y ∈ Q₄ ⊓ centralizer (E₄ : Set max4Subgroup) := by
        refine ⟨hx,?_⟩
        intro z hz
        exact Subtype.ext (hxe z hz)
      have hy8 : y ∈ NormalEight.eight := h8eq ▸ (show y ∈
        pCore 2 max4Subgroup ⊓ centralizer (E₄ : Set max4Subgroup) from ⟨hfix hy,hy.2⟩)
      exact mem_map_of_mem max4Subgroup.subtype hy8
    · rintro x ⟨y,hy,rfl⟩
      refine ⟨h8 (mem_map_of_mem max4Subgroup.subtype hy),?_⟩
      have hyc : y ∈ centralizer (E₄ : Set max4Subgroup) :=
        (show y ∈ pCore 2 max4Subgroup ⊓ centralizer (E₄ : Set max4Subgroup) from h8eq.symm ▸ hy).2
      intro e he
      exact congrArg Subtype.val (hyc ⟨e,hE4 he⟩ he)
  have hDn : D ≤ normalizer (max4Eight : Set Model) := by
    rw [←hfixed]
    intro d hd
    have hdE : d ∈ centralizer (E : Set Model) :=
      commutator_eq_bot_iff_le_centralizer.mp hDE hd
    apply mem_normalizer_fintype
    rintro x ⟨hx,hxE⟩
    exact ⟨(mem_normalizer_iff.mp (hDQ hd) x).mp hx,
      (centralizer (E : Set Model)).mul_mem
        ((centralizer (E : Set Model)).mul_mem hdE hxE)
        ((centralizer (E : Set Model)).inv_mem hdE)⟩
  exact (hDn.trans max4_eight_normalizer_le).trans (jankoFour_max4_normalizes S R hl hn
    ⟨F,inferInstance,inferInstance,hF,⟨eF⟩⟩ hS)

/-- A commuting max1 actor normalizes the SAME full-Sylow-normalized A₅ residual.
Sylow conjugacy constructs the max4 marking without an extra premise. -/
theorem jankoFour_max1_commuting_actor_normalizes (S : Sylow 2 Model) (R D E : Subgroup Model)
    (hl : R ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Model) ≤ normalizer (R : Set Model))
    (he : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hE : Nat.card E = 3) (hER : E ≤ R) (hDE : ⁅D,E⁆ = ⊥)
    (hSM : (S : Subgroup Model) ≤ max1Subgroup matrixA_mul_self matrixB_pow_four)
    (hDM : D ≤ max1Subgroup matrixA_mul_self matrixB_pow_four)
    (hEM : E ≤ max1Subgroup matrixA_mul_self matrixB_pow_four) :
    D ≤ normalizer (R : Set Model) := by
  obtain ⟨a,hSa⟩ := exists_max4_marking S
  have hid₁ : a.symm.toMonoidHom.comp a.toMonoidHom = MonoidHom.id Model := by
    ext x
    exact a.symm_apply_apply x
  have hid₂ : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id Model := by
    ext x
    exact a.apply_symm_apply x
  let P := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let := NormalEight.elementary_eight
  let := NormalEight.normal_eight
  let : IsElementaryAbelian 2 max4Eight := IsElementaryAbelian.map_subtype
  have h8c : Nat.card max4Eight = 8 := by
    rw [card_map_of_injective max4Subgroup.subtype_injective,NormalEight.card_eight]
  have h8P : max4Eight ≤ (P : Subgroup Model) := by
    have h8core : NormalEight.eight ≤ pCore 2 max4Subgroup :=
      le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 _⟩
    have hh := map_mono (f := max4Subgroup.subtype)
      (h8core.trans (pCore_isPGroup.le_sylow_of_normal (P.subtype hSa)))
    change max4Eight ≤ (((S : Subgroup Model).map a.toMonoidHom).subgroupOf max4Subgroup).map max4Subgroup.subtype at hh
    rwa [map_subgroupOf_eq_of_le hSa] at hh
  let A := max4Eight.map a.symm.toMonoidHom
  have hAS : A ≤ (S : Subgroup Model) := by
    rintro x ⟨y,hy,rfl⟩
    obtain ⟨s,hs,heq⟩ := h8P hy
    change a.symm y ∈ (S : Subgroup Model)
    rw [←heq]
    change a.symm (a s) ∈ (S : Subgroup Model)
    rwa [a.symm_apply_apply]
  have hnA : (S : Subgroup Model) ≤ normalizer (A : Set Model) := by
    have hh := map_mono (f := a.symm.toMonoidHom) (hSa.trans max4_le_eight_normalizer)
    rw [map_map,hid₁,map_id,
      map_equiv_normalizer_eq] at hh
    exact hh
  have hAQ := normal_eight_le_kernel S hSM A hAS hnA (IsElementaryAbelian.map _)
    ((card_map_of_injective a.symm.injective).trans h8c)
  have h8Q : max4Eight ≤ Q₁.map a.toMonoidHom := by
    have hh := map_mono (f := a.toMonoidHom) hAQ
    change (max4Eight.map a.symm.toMonoidHom).map a.toMonoidHom ≤ Q₁.map a.toMonoidHom at hh
    rwa [map_map,hid₂,map_id] at hh
  have hQS : Q₁ ≤ (S : Subgroup Model) := by
    have hh := map_mono (f := M₁.subtype) (LocalStructure.localKernel_le_sylow (S.subtype hSM))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSM] using hh
  let := LocalStructure.localKernel_elementary matrixA_mul_self matrixB_pow_four
  let : IsElementaryAbelian 2 Q₁ := IsElementaryAbelian.map_subtype
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot a.injective]
    infer_instance
  let d := a.subgroupMap R
  let e := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hh := kernel_actor_normalizes P (R.map a.toMonoidHom) (D.map a.toMonoidHom)
    (E.map a.toMonoidHom) (Q₁.map a.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl a.toMonoidHom)
    ((map_mono hn).trans (R.le_normalizer_map a.toMonoidHom)) (he.of_mulEquiv e.symm)
    hSa ((card_map_of_injective a.injective).trans hE) (map_mono hER)
    (IsElementaryAbelian.map _) (map_mono hQS)
    ((map_mono (hSM.trans max1_normalizes_kernel)).trans (Q₁.le_normalizer_map a.toMonoidHom))
    ((map_mono (hEM.trans max1_normalizes_kernel)).trans (Q₁.le_normalizer_map a.toMonoidHom))
    ((map_mono (hDM.trans max1_normalizes_kernel)).trans (Q₁.le_normalizer_map a.toMonoidHom))
    (by rw [←map_commutator,hDE,Subgroup.map_bot]) h8Q
  rw [←map_equiv_normalizer_eq] at hh
  exact (map_le_map_iff_of_injective a.injective).mp hh

open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

/-- The original normal J₄ component contradicts Cartan escape. Both Hall
conditions and the original quotient markings enter through the native pair theorem. -/
theorem normal_jankoFour_cartan_exclusion
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (hR : residual H ∈ Chapter1.L G (T : Subgroup G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hRC : residual H ≤ C.map Y.subtype)
    (e : (C ⧸ pCore 2 C) ≃* Janko4.Model) : False := by
  obtain ⟨f,S,hfs,hf,hS,hl,hSR,hfour,hB,hE,hER,hcyc,hodd,hED,hDS,hsol,
    hES,hcard,hcore,hext,he₃,hout,hnot,htwo,hplace,hsolplace,hmax,hRcore,hremain,
    ⟨g,hSg,hKM,himage,hgeometry⟩,hD,hDE,hdis,h9,hel,hK⟩ :=
    normal_jankoFour_native_cubic_pair h hH hgen c hY hescape hR C hC hRC e
  let R := ((residual H).subgroupOf Y).map f
  let D := (A.subgroupOf Y).map f
  let E := (B.subgroupOf Y).map f
  let a := MulAut.conj g
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot a.injective]
    infer_instance
  let d := a.subgroupMap R
  let q := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hh := jankoFour_max1_commuting_actor_normalizes
    (S.mapSurjective (f := a.toMonoidHom) a.surjective)
    (R.map a.toMonoidHom) (D.map a.toMonoidHom) (E.map a.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl a.toMonoidHom)
    ((map_mono hSR).trans (R.le_normalizer_map a.toMonoidHom)) (hfour.of_mulEquiv q.symm)
    ((card_map_of_injective a.injective).trans hE) (map_mono hER)
    (by rw [←map_commutator,hDE,Subgroup.map_bot])
    ((map_mono (le_sup_right.trans le_sup_left)).trans hKM)
    ((map_mono (le_sup_left.trans le_sup_left)).trans hKM)
    ((map_mono le_sup_right).trans hKM)
  rw [←map_equiv_normalizer_eq] at hh
  exact hout ((map_le_map_iff_of_injective a.injective).mp hh)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The original component sieve excludes J₄, preserving every earlier
source alternative, the same residual and the original component inclusions. -/
theorem localCartan_escape_seed_jankoFour_excluded
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd,hJ4⟩ :=
    localCartan_escape_seed_jankoFour_hall_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hCn,hJ,hOdd,?_⟩
  rintro ⟨e⟩
  obtain ⟨hKR,hfour,hB,hext⟩ := hJ4 ⟨e⟩
  let : C.Normal := hCn
  exact LocalSieve.normal_jankoFour_cartan_exclusion h hH hgen c hY hescape
    (hKR ▸ hKL) C hC (hKR ▸ hKC) e

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
