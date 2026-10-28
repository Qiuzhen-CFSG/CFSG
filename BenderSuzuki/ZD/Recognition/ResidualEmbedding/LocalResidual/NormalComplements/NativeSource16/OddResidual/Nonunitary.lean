module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.FinalCircle
public import Theory.SpecificGroups.Suzuki.OddSubgroups

/-!
# Excluding the nonunitary final circles in Proposition 16.5

Odd-primary subgroups of the literal linear and Suzuki carriers are cyclic.
The linear fact uses the faithful characteristic-two SL₂ lift; the Suzuki
fact follows by embedding in a cyclic odd Sylow subgroup. Thus a perfect
odd central Bender cover containing the original noncyclic odd residual
must have a genuine unitary model.

The terminal consumer recognizes the circle at the corrected distinguished
base, transports the original residual through the conjugate-circle
isomorphism, and returns a unitary model of the original circle. It never
identifies the original two-point stabilizer with a newly chosen Borel pair.

Source: GLS IV, Chapter 2, Proposition 16.5, terminal circle analysis;
Chapter 4, Lemma 3.7 and the Suzuki odd-torus geometry.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
open RankOneModelGeometry _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The literal odd-primary subgroup in an actual Suzuki overgroup is cyclic. -/
public theorem pSubgroup_isCyclic_of_suzuki_model (F R : Subgroup G)
    {m : ℕ} (hm : 0 < m) (e : F ≃* SuzukiMatrixGroup m) (hRF : R ≤ F)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hR : IsPGroup p R) : IsCyclic R := by
  let f := e.toMonoidHom.comp (inclusion hRF)
  have hf : Function.Injective f := e.injective.comp (inclusion_injective hRF)
  have hr : IsPGroup p f.range := hR.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨P,hP⟩ := hr.exists_le_sylow
  let : IsCyclic P := suzukiSylow_isCyclic_of_ne_two hm hp P
  let : IsCyclic f.range := isCyclic_of_le hP
  exact isCyclic_of_injective f.rangeRestrict (fun _ _ hh => hf (congrArg Subtype.val hh))

/-- A noncyclic odd-primary subgroup excludes the linear and Suzuki models
of the same perfect odd central cover. Its inclusion is the supplied faithful map. -/
public theorem oddCentralCover_unitary_of_noncyclic_pSubgroup
    {C P : Type*} [Group C] [Finite C] [Group P] [Finite P] {n p : ℕ}
    [Fact p.Prime] (hn : 2 ≤ n) (hp : p ≠ 2) (hP : IsPGroup p P)
    (hne : ¬ IsCyclic P) (f : P →* C) (hf : Function.Injective f)
    (hperfect : commutator C = ⊤) (hodd : Odd (Nat.card (center C)))
    (hmodel : IsSimpleBenderGroupAtExponent n (C ⧸ center C)) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      J.form = !![0,0,1;0,1,0;1,0,0] ∧ Nat.card E = (2 ^ n) ^ 2 ∧
      Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
      (Nonempty (C ≃* ProjectiveSpecialUnitaryMatrixGroup J) ∨
        (Odd n ∧ Nonempty (C ≃* J.specialSubgroup))) := by
  have hfp : IsPGroup p f.range := hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfc : ¬ IsCyclic f.range := fun hc => by
    let := hc
    exact hne (isCyclic_of_injective f.rangeRestrict
      (fun _ _ hh => hf (congrArg Subtype.val hh)))
  rcases oddCentralCover_model_cases hn hperfect hodd hmodel with
    ⟨_,⟨e⟩⟩ | ⟨_,m,hm,_,⟨e⟩⟩ | ⟨E,hfield,hfinite,J,hJ,hcard,hfixed,he⟩
  · exact (hfc (pSubgroup_isCyclic_of_linear_model ⊤
      (Subgroup.topEquiv.trans e) f.range le_top hp hfp)).elim
  · exact (hfc (pSubgroup_isCyclic_of_suzuki_model ⊤ f.range (by omega)
      (Subgroup.topEquiv.trans e) le_top hp hfp)).elim
  · refine ⟨E,hfield,hfinite,J,hJ,hcard,hfixed,?_⟩
    rcases he with ⟨_,he⟩ | ⟨_,ho,he⟩
    · exact Or.inl he
    · exact Or.inr ⟨ho,he⟩

variable {Z : Set G} {M : Subgroup G}

/-- The original final circle is unitary. All recognition and nonunitary
exclusion premises are discharged from the actual odd-residual configuration. -/
public theorem source16_final_circle_unitary
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {t u w : G}
    (ht : t ∈ Z) (htM : t ∉ M)
    (hu : PFAppendixIII.IsInvolution u) (huD : u ∈ residualPairStabilizer M t)
    (hw : PFAppendixIII.IsInvolution w) (htw : Commute t w)
    (R : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hpo : Odd p) (hRp : IsPGroup p R)
    (hRD : R ≤ residualPairStabilizer M t) (hRw : R ≤ centralizer ({w} : Set G))
    (htR : t ∈ normalizer R) (hrep : ⁅R,zpowers t⁆ = R) (hne : ¬ IsCyclic R) :
    ∃ (n : ℕ), 2 ≤ n ∧
      ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
        J.form = !![0,0,1;0,1,0;1,0,0] ∧ Nat.card E = (2 ^ n) ^ 2 ∧
        Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
        (Nonempty (localCircle Z (centralizer ({w} : Set G)) ≃*
            ProjectiveSpecialUnitaryMatrixGroup J) ∨
          (Odd n ∧ Nonempty (localCircle Z (centralizer ({w} : Set G)) ≃*
            J.specialSubgroup))) := by
  have hp2 : p ≠ 2 := fun he => (by decide : ¬ Odd (2 : ℕ)) (he ▸ hpo)
  have hodd : Odd (Nat.card R) := by
    obtain ⟨k,hk⟩ := hRp.exists_card_eq
    rw [hk]
    exact hpo.pow
  obtain ⟨g,hgt,hgw,hcross,hns,n,hn,hperfect,hcenter,hmodel⟩ :=
    source16_final_circle_conjugate_recognition h r ha ht htM hu huD hw htw
      R hodd hRD hRw htR hrep hne
  obtain ⟨e⟩ := Source16OddResidual.circle_equiv_of_isConj h.disconnected
    (show IsConj w (MulAut.conj g w) from isConj_iff.mpr ⟨g,rfl⟩)
  let B := centralizer ({w} : Set G)
  let eB : localCircle Z B ≃* localCircleIn Z B :=
    (localCircle Z B).equivMapOfInjective B.subtype B.subtype_injective
  have hRL : R ≤ localCircleIn Z B :=
    Source16OddResidual.full_commutator_le_circle h.disconnected R ht htw hRw hrep
  let f := e.toMonoidHom.comp (eB.symm.toMonoidHom.comp (inclusion hRL))
  have hf : Function.Injective f := e.injective.comp
    (eB.symm.injective.comp (inclusion_injective hRL))
  obtain ⟨E,hfield,hfinite,J,hJ,hcard,hfixed,hunitary⟩ :=
    oddCentralCover_unitary_of_noncyclic_pSubgroup hn hp2 hRp hne f hf
      hperfect hcenter hmodel
  refine ⟨n,hn,E,hfield,hfinite,J,hJ,hcard,hfixed,?_⟩
  rcases hunitary with hprojective | ⟨ho,⟨eu⟩⟩
  · obtain ⟨eu⟩ := hprojective
    exact Or.inl ⟨e.trans eu⟩
  · exact Or.inr ⟨ho,⟨e.trans eu⟩⟩

end BenderSuzuki.ZD
