module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeMovement

/-!
# Suitable vectors from a single normal binary-three seed

In the single normal component branch, Mc=KT. The marked natural central
quotient supplies the seed's index-two stabilizer. Self-normalization of
Sylows in L₃(2), lifted through the component's two-core, gives the literal
normalizer Mc∩N_G(N_T(W))=T. The original seed geometry supplies fitting
placement and separation with component-fixed overlap allowed.

When this seed has dimension three, its covering kernel vanishes by the
proved dimension identity. Orbit counting supplies a nonzero vector fixed
by N_T(W); the component moves it. The original W/Z coordinates lift that
same vector to an involution and prove all U0--U3 clauses.

This is a conditional branch consumer. Its component generation, natural
seed marking and dimension-three premise must be derived by
qt-e-suitable-component-supports, which retains the full support identities,
cover and FF exclusions and final assembly. The five-dimensional A₆ cover
is handled by its separate fixed-moving lift. Original14.6.18 remains with
qt-e-14625-source; final14.6.24 source-clause assembly stays with
qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.21(1),14.6.22 and14.6.24(1),
printed pp.1037--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Subgroup.NormalSylowQuotientAction
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

/-- In the single normal L₃ branch the seed stabilizer already has the
literal local normalizer needed in U3. The central cover need not split. -/
theorem source_normal_l3_seed_geometry
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hnK : (K.subgroupOf Mc).Normal) (hgen : K ⊔ (T : Subgroup G) = Mc)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))}
    (hI : IsIrrPlusWith a.representation (actorImage Mc K)
      (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)) :
    let W := (originalSection a).subspacePreimage I
    CentralOverlapGeometry T Mc (conjugateSpanBy (localModule T M) Mc) K W
      ((T : Subgroup G) ⊓ normalizer (W : Set G)) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  let W := (originalSection a).subspacePreimage I
  let S := (T : Subgroup G) ⊓ normalizer (W : Set G)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hout.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKM).mp hnK)
  have hindex : S.relIndex (T : Subgroup G) = 2 := by
    have hh := (source_l3_seed_stabilizer_index hG T hempty hM hunique hmany hcard e hab hsolv
      Mc hout K hKM hK a hI b).2
    rw [inf_eq_left.mpr hTK] at hh
    exact (inf_relIndex_left (T : Subgroup G) (normalizer (W : Set G))).trans hh
  obtain ⟨hz,hle,hKW,hN,hsep⟩ := source_component_seed_geometry
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hI.isIrrPlus
  have hST : S ≤ (T : Subgroup G) := inf_le_left
  have hSM : S ≤ Mc := hST.trans hout.1.2
  let P := T.subtype hout.1.2
  let R := K.subgroupOf Mc
  let B := S.subgroupOf Mc
  let : R.Normal := hnK
  have hgen' : R ⊔ (P : Subgroup Mc) = ⊤ := by
    rw [show (P : Subgroup Mc) = (T : Subgroup G).subgroupOf Mc from rfl,
      ←subgroupOf_sup hKM hout.1.2,hgen,subgroupOf_self]
  let ec := (cComponentTwoCoreQuotientEquiv hK).trans b.groupEquiv
  let f := ec.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hf : Function.Surjective f := ec.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ ec.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hself : ∀ Q : Sylow 2 R, normalizer (Q : Set R) = Q :=
    Sylow.self_normalizing_of_two_kernel f hf hk Matrix.PSL3Two.self_normalizing_sylow
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp (normal_of_index_eq_two hindex)
  have hBN : normalizer (B : Set Mc) = (P : Subgroup Mc) := by
    apply P.normalizer_subgroup_eq_of_normal_supplement R hgen' hself B
      (fun _ hx => hST hx)
    · intro x hx
      exact ⟨hx.1,hKW hx.2⟩
    · intro x hx
      rw [←subgroupOf_normalizer_eq hSM]
      exact hTS hx
  have hlocal : Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
    have hn : (normalizer (S : Set G)).subgroupOf Mc = (T : Subgroup G).subgroupOf Mc := by
      rw [subgroupOf_normalizer_eq hSM]
      exact hBN
    have hh := congrArg (Subgroup.map Mc.subtype) hn
    rw [map_subgroupOf_eq_of_le hout.1.2,subgroupOf_map_subtype] at hh
    exact (inf_comm Mc (normalizer (S : Set G))).trans hh
  refine ⟨source_component_fitting_placement hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK,(originalSection a).subspacePreimage_le I,hz,hKW,hST,hindex,hlocal,?_⟩
  intro t ht hnt
  exact hsep t ht (hTK ht) (fun hn => hnt ⟨ht,hn⟩)

/-- A three-dimensional marked seed in the single normal L₃ branch gives
an actual suitable involution. No vector, separation, index, or normalizer
premise remains; its same literal support and quotient centralizer are kept. -/
theorem source_exists_on_normal_l3_seed_of_three
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hnK : (K.subgroupOf Mc).Normal) (hgen : K ⊔ (T : Subgroup G) = Mc)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))}
    (hI : IsIrrPlusWith a.representation (actorImage Mc K)
      (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3))
    (hdim : Module.finrank (ZMod 2) I = 3) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let W := (originalSection a).subspacePreimage I
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = (T : Subgroup G) ⊓ normalizer (W : Set G) ∧
      Suitable h Mc u := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  let c := originalSection a
  let W := c.subspacePreimage I
  let A := Mc ⊓ normalizer (W : Set G)
  have d := source_normal_l3_seed_geometry hG T hempty hM hunique hmany hcard e hab hsolv
    K hKM hK hnK hgen a hI b
  have hKA : K ≤ A := le_inf hKM d.normalized
  have hWM : W ≤ Mc := (c.subspacePreimage_le I).trans c.section_le
  have hWA : W ≤ A := le_inf hWM W.le_normalizer
  have hinv : A.subgroupOf Mc ≤ subspaceStabilizer
      (a.representation.comp (QuotientGroup.mk' (pCore 2 Mc))) I := by
    intro x hx
    exact (subspace_map_eq_iff _ I x).mp ((c.mem_normalizer_subspacePreimage_iff I x).mp hx.2)
  let τ := BinaryConjugationSection.subspaceAction A (show A ≤ Mc from inf_le_left) I hinv
  let s := c.subspaceSection A (show A ≤ Mc from inf_le_left) I hinv hWA
  have hker : (fixedSpace a.representation (actorImage Mc K)).comap I.subtype = ⊥ := by
    have hi := hI.isIrrPlus.finrank_of_linear_three_central_quotient a.representation (actorImage Mc K)
      b.groupEquiv b.linearEquiv b.intertwines
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hfree : fixed (τ.comp (K.subgroupOf A).subtype) = ⊥ := by
    apply bot_unique
    intro v hv
    have hvk : v ∈ (fixedSpace a.representation (actorImage Mc K)).comap I.subtype := by
      intro k
      obtain ⟨x,hx,he⟩ := k.property
      have hh := congrArg Subtype.val (hv (⟨⟨x,hKA hx⟩,hx⟩ : K.subgroupOf A))
      change a.representation (QuotientGroup.mk' (pCore 2 Mc) x) v.val = v.val at hh
      change a.representation k.val v.val = v.val
      rw [←he]
      exact hh
    rwa [hker] at hvk
  let : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr (hI.isIrrPlus.ne_bot a.representation)
  let : Group.IsPerfect (K.subgroupOf Mc) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKM).toMonoidHom) (subgroupOfEquivOfLe hKM).surjective
  exact source_exists_of_fixed_free_central_overlap hG T hempty hM hunique hmany hcard e hab
    K W ((T : Subgroup G) ⊓ normalizer (W : Set G)) A d τ s
    (inf_le_inf hout.1.2 le_rfl) hfree

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
