module

public import CFSG.Quasithin.Chapter14.Section06.Singleton.E9Ambient.PlaneFrattini
public import CFSG.Quasithin.Chapter14.Section02.ResidualSylow
public import Theory.GroupAction.CardFourCubic

/-!
# The actual middle core at an elementary-nine critical plane

The critical point centralizer is the conjugate of the original middle
vertex two-core, with the same conjugator that places its central plane.
Consequently the original cubic endpoint supplies an actual element of
order three normalizing that centralizer and acting nontrivially on its plane.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- The literal critical centralizer is an original middle two-core, and
its full original cubic endpoint provides a nontrivial order-three plane actor. -/
theorem source_singleton_nine_middle_core_cubic_actor
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation) (hd : d.FittingFull)
    (hone : Nat.card d.Index = 1)
    (hnine : Nat.card (pResidual 2 (J ⧸ pCore 2 J)) = 9) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ i : h.CriticalEndpoint,
      let A := D.V₁ ⊔ i.conjugate D.V₁
      let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
      ∃ g : J,
        A = (localModule T M).conjBy (g : G) ∧
        C = (X.pCoreIn 2).conjBy (g : G) ∧
        X.conjBy (g : G) ≤ normalizer (C : Set G) ∧
        ∃ b ∈ X.conjBy (g : G), orderOf b = 3 ∧ b ∉ centralizer (A : Set G) ∧
          ∀ z ∈ A, z ≠ 1 → b * z * b⁻¹ ≠ z := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let V := localModule T M
  let Q := X.pCoreIn 2
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∀ i : h.CriticalEndpoint, _
  intro i
  let A := D.V₁ ⊔ i.conjugate D.V₁
  let C := J ⊓ centralizer (i.conjugate D.V₁ : Set G)
  obtain ⟨g,hgV,_,_,hgT⟩ := source_singleton_nine_point_plane_placement
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i
  have hO : omegaOneCenterAmbient C = A := (source_singleton_nine_point_centralizer_omega
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.1
  have hAV : A = V.conjBy (g : G) := hO.symm.trans hgV
  have hC : C = (T : Subgroup G).conjBy (g : G) ⊓ centralizer (A : Set G) := by
    apply le_antisymm
    · refine le_inf ?_ ?_
      · rw [←hgT]
        exact le_inf inf_le_left C.le_normalizer
      · apply le_centralizer_iff.mp
        apply sup_le
        · exact (le_centralizer_iff.mp h.H_centralizes).trans (centralizer_le inf_le_left)
        · exact le_centralizer_iff.mp inf_le_right
    · exact le_inf (inf_le_left.trans (hgT.ge.trans inf_le_left))
        (inf_le_right.trans (centralizer_le (show i.conjugate D.V₁ ≤ A from le_sup_right)))
  obtain ⟨hQ,⟨eX⟩⟩ := Section02.source_residualSylow_quotient
    hG T hempty hM hu hmany hcard e
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow X (T.subtype hTX)).trans_eq (map_subgroupOf_eq_of_le hTX)
  have hQ' : Q = (T : Subgroup G) ⊓ centralizer (V : Set G) := le_antisymm
    (le_inf hQT (hQ.le.trans inf_le_right))
    (hQ.ge.trans' (inf_le_inf hTX le_rfl))
  have hCQ : C = Q.conjBy (g : G) := by
    rw [hC,hAV,hQ']
    change _ = ((T : Subgroup G) ⊓ centralizer (V : Set G)).map
      (MulAut.conj (g : G)).toMonoidHom
    rw [map_inf _ _ _ (MulAut.conj (g : G)).injective,map_centralizer_equiv]
    rfl
  have hXQ : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hXC : X.conjBy (g : G) ≤ normalizer (C : Set G) := by
    have hh := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hXQ
    rw [map_equiv_normalizer_eq] at hh
    exact hh.trans_eq (congrArg (fun B : Subgroup G => normalizer (B : Set G)) hCQ.symm)
  have hquot : Nat.card (X ⧸ pCore 2 X) = 6 := by
    rw [Nat.card_congr eX.toEquiv,Nat.card_perm,Nat.card_fin]
    rfl
  have hthree : 3 ∣ Nat.card X := by
    have hh := (pCore 2 X).card_mul_index
    rw [index_eq_card,hquot] at hh
    rw [←hh]
    exact dvd_mul_of_dvd_right (by decide : 3 ∣ 6) _
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 hthree
  have hbG : orderOf (b : G) = 3 := (orderOf_coe b).trans hb
  have hbQ : (b : G) ∉ Q := by
    intro hbQ
    have hp : IsPGroup 2 (zpowers (b : G)) :=
      (isPGroup_pCoreIn 2 X).to_le (zpowers_le.mpr hbQ)
    have hp3 : IsPGroup 3 (zpowers (b : G)) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers,hbG]; rfl)
    have hd := hp.disjoint_of_coprime hp3 (by decide : Nat.Coprime 2 3)
    have he : zpowers (b : G) = ⊥ := disjoint_self.mp hd
    have hc := Nat.card_zpowers (b : G)
    rw [he,card_bot,hbG] at hc
    contradiction
  have hbV : (b : G) ∉ centralizer (V : Set G) := fun hbV => hbQ (hQ.ge ⟨b.property,hbV⟩)
  let bg : G := (MulAut.conj (g : G)) b
  have hbgX : bg ∈ X.conjBy (g : G) := mem_map_of_mem _ b.property
  have hbg3 : orderOf bg = 3 := (orderOf_injective (MulAut.conj (g : G)).toMonoidHom
    (MulAut.conj (g : G)).injective (b : G)).trans hbG
  have hbgmove : bg ∉ centralizer (A : Set G) := by
    intro hbg
    have hh : (MulAut.conj (g : G)) b ∈
        (centralizer (V : Set G)).map (MulAut.conj (g : G)).toMonoidHom := by
      rw [map_centralizer_equiv]
      change (MulAut.conj (g : G)) b ∈ centralizer (V.conjBy (g : G) : Set G)
      rwa [←hAV]
    exact hbV ((mem_map_iff_mem (MulAut.conj (g : G)).injective).mp hh)
  refine ⟨g,hAV,hCQ,hXC,bg,hbgX,hbg3,hbgmove,?_⟩
  have hnA : normalizer (C : Set G) ≤ normalizer (A : Set G) :=
    (source_singleton_nine_point_centralizer_omega
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2
  let bgN : normalizer (A : Set G) := ⟨bg,hnA (hXC hbgX)⟩
  let σ : MulAut A := A.normalizerMonoidHom bgN
  have hσ3 : σ ^ 3 = 1 := by
    change (A.normalizerMonoidHom bgN) ^ 3 = 1
    rw [←map_pow,show bgN ^ 3 = 1 from Subtype.ext
      (by change bg ^ 3 = 1; simpa only [hbg3] using pow_orderOf_eq_one bg),map_one]
  have hσne : σ ≠ 1 := by
    intro hσ
    apply hbgmove
    have hh : bgN ∈ A.normalizerMonoidHom.ker := hσ
    rwa [normalizerMonoidHom_ker] at hh
  have hAc : Nat.card A = 4 :=
    (source_singleton_nine_paired_point_lines
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd hone hnine i).2.2.2.2.1
  intro z hz hz1 hfix
  exact Theory.GroupAction.CardFourCubic.moves_nonidentity hAc σ hσ3 hσne ⟨z,hz⟩
    (fun hh => hz1 (congrArg Subtype.val hh)) (Subtype.ext hfix)

end CFSG.Quasithin.Chapter14.Section06
