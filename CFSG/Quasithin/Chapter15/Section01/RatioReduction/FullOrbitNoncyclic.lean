module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.ClassifiedNoThree
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.SingletonSupport
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.GlobalOrthogonal

/-!
# The singleton noncyclic full-orbit case of original 15.1.2

The marked D.2.22 support family has two binary planes: the original local
source excludes its three-plane alternative. A singleton full-orbit factor
has the whole original module as its support. Transporting its planes along
the actual embedding, the existing order-36 recognition theorem makes the
original action image equal its marked Jhat. The resulting Omega-four
coordinates intertwine the original action, without an enlargement premise.

Source: Aschbacher--Smith 15.1.2, printed p.1086, the singleton noncyclic case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition ChapterD.FittingConfigurations
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_singleton_noncyclic_full
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (U : Submodule (ZMod 2) (Additive V)) (c : FactorData ρ (Jhat ρ) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (i : d.Index), (∀ j : d.Index, j = i) → U = ⊤ →
    ∀ (A : Subgroup (d.factor i).Carrier), A ∈ QhatStar (d.factor i).action → 1 < rank A →
      Jhat ρ = ⊤ ∧ cubicRatio ρ = 3 / 2 ∧ Module.finrank (ZMod 2) (Additive V) = 4 ∧
      Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      ∃ (x : Additive V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
        (e : D ≃* OrthogonalFourBinary.omega),
        ∀ g v, x (ρ g v) = (e g).val.val (x v) := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let f := actionHom M V (le_normalizer_conjugateSpanBy _ _)
  let := source_localAction_isSolvable hG T hempty hM
  let : (Jhat ρ).Normal := Jhat_normal ρ
  dsimp only
  intro U c d hd i hi hU A hA hArank
  let F₀ := d.factor i
  let F := c.ambientFactor d i
  let j : F₀.Carrier →* D := (Jhat ρ).subtype.comp F₀.embedding.groupMap
  let : Group.IsSolvable F₀.Carrier := Group.isSolvable_of_isSolvable_injective
    (f := j) ((Jhat ρ).subtype_injective.comp F₀.embedding.group_injective)
  obtain ⟨B,r,hB,hr⟩ := c.factor_cover d
    (Chapter3.sqtk_of_mem_H hG (Chapter1.mem_H_of_isTwoLocal hM.1.1.1))
    f.rangeRestrict f.rangeRestrict_surjective i
  obtain ⟨s,h,ds,halt,hsdim,hq,_⟩ := SourceReduction.source_noncyclic_global_configurations
    F₀.action hB r hr F₀.faithful hA hArank
    (generalizedFitting_eq_fitting_of_solvable F₀.Carrier)
    (c.factor_twoCore d (source_localAction_twoCore hG T hM) i) (hd i) F₀.generated
  have hs : s = 2 := by
    rcases h.rank_cases with hs | hs
    · exact hs
    · subst s
      exact (source_localAction_no_three_support_factor hG T hempty hM hmany hJ hu hne
        U c d hd i A h ds).elim
  subst s
  obtain ⟨e₀,he₀,_⟩ : ∃ e : F₀.Carrier ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
      ds.IsDiagonal e ∧ ds.IsTransitive A := by
    rcases halt with ⟨_,he⟩ | ⟨hn,_⟩
    · exact he
    · norm_num at hn
  have hactor : F.actor = Jhat ρ := c.unique_factor_actor d i hi
  have hspace : F.space = ⊤ := (c.unique_factor_space d i hi).trans hU
  let eV : F.Space ≃ₗ[ZMod 2] Additive V := LinearEquiv.ofBijective F.embedding.spaceMap
    ⟨F.embedding.space_injective,LinearMap.range_eq_top.mp hspace⟩
  let P := (pCore 3 F.Carrier).map F.embedding.groupMap
  let : F.actor.Normal := hactor ▸ (Jhat_normal ρ)
  have hP : P = F.actor.pCoreIn 3 :=
    (pCoreIn_range_of_injective 3 _ F.embedding.group_injective).symm
  let : P.Normal := by
    rw [hP]
    exact inferInstanceAs ((pCore 3 F.actor).map F.actor.subtype).Normal
  let : IsElementaryAbelian 3 (pCore 3 F.Carrier) := h.elementary
  let : IsElementaryAbelian 3 P := IsElementaryAbelian.map F.embedding.groupMap
  let ds' : SupportFactors ρ P 2 := ds.map F.action ρ F.embedding.groupMap
    F.embedding.group_injective eV F.embedding.equivariant
  have hqρ : cubicRatio ρ = 3 / 2 := F.embedding.ratio.symm.trans hq
  have hlow : 1 < cubicRatio ρ := by
    rw [hqρ]
    norm_num [ENNReal.lt_div_iff_mul_lt]
  have hcardF₀ : Nat.card F₀.Carrier = 36 := by
    rw [Nat.card_congr e₀.toEquiv,Nat.card_prod]
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hcardF : Nat.card F.Carrier = 36 := hcardF₀
  have hcardJ : Nat.card (Jhat ρ) = 36 :=
    (Nat.card_congr (c.unique_factor_equiv d i hi).toEquiv).symm.trans hcardF
  have htop : Jhat ρ = ⊤ := ds'.eq_top_of_card_thirty_six ρ
    (imageRepresentation_injective _ _ _) (ds'.factor_conj_closed ρ
      (imageRepresentation_injective _ _ _)) (Jhat ρ) hcardJ hlow
  let eG : F.Carrier ≃* D := MulEquiv.ofBijective F.embedding.groupMap
    ⟨F.embedding.group_injective,MonoidHom.range_eq_top.mp (hactor.trans htop)⟩
  let eD : D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := eG.symm.trans e₀
  refine ⟨htop,hqρ,eV.finrank_eq.symm.trans ?_,⟨eD⟩,?_⟩
  · have hh : Module.finrank (ZMod 2) F₀.Space = 4 := by omega
    exact hh
  · exact ds'.exists_omega_coordinates ρ (imageRepresentation_injective _ _ _)
      (ds'.factor_conj_closed ρ (imageRepresentation_injective _ _ _)) eD hlow

end CFSG.Quasithin.Chapter15.Section01
