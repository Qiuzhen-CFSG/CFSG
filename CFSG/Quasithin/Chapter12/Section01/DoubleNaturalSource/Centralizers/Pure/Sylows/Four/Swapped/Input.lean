module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.ComponentSieve

/-!
# Full swapped-component detection for the pure-point Sylow obstruction

The original escaping Sylow and residual supply component detection with
noncentrality and the commutator identity retained. The previously proved
binary-linear and Held interval-normalizer calculations exclude every
invariant row. Thus the surviving component has the complete swapped
Sylow input, with its orbit equal to the original normal closure.

The application constructs every input from the marked point. Only the
original L-fixed omega-subgroup nontriviality remains explicit. Its actual
ambient specialization belongs to `qt-rank-two-ms93`, with final earlier
inputs supplied by `qt-d-double-natural-centralizers`. This task retains
the ambient Sylow, core, fusion and abelian-closure assembly.
Source: Aschbacher--Smith 12.1.4, printed pp.790--791, and the corrected
1.3.4 component detection, pp.509--511.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open Chapter1 Chapter1.XiEmbedding
open Chapter10.SourceLinearThreeReplacement.Overgroups.Closure
variable {G : Type*} [Group G] [Finite G]

/-- Retain the full detected swapped input after the invariant exclusions. -/
theorem swapped_input_of_core_interval (T : Sylow 2 G) {P X A U : Subgroup G}
    (hi : LocalInput 3 (T : Subgroup G) X A (P ⊔ (X ⊔ (T : Subgroup G))))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (P ⊔ (X ⊔ (T : Subgroup G)) : Subgroup G))
    (hn : ¬ (X.subgroupOf (P ⊔ (X ⊔ (T : Subgroup G)))).Normal)
    (hPU : P ≤ normalizer (U : Set G)) (hUT : U ≤ (T : Subgroup G))
    (hcore : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ U)
    (hindex : U.relIndex (T : Subgroup G) ≤ 2)
    (hw : Nonempty (XiQuotient (X ⊔ (T : Subgroup G)) ≃* ParabolicWreath)) :
    ∃ K : Subgroup G,
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X A
        (P ⊔ (X ⊔ (T : Subgroup G))) K ∧
      conjugateSpanBy X (P ⊔ (X ⊔ (T : Subgroup G))) = componentOrbit K (T : Subgroup G) := by
  let H := P ⊔ (X ⊔ (T : Subgroup G))
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans le_sup_right
  have hT : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  let hA := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremC_knownSimple (G := Y)
  rcases hi.normal_or_detected_containment hA hC hsq hT with
    hnormal | ⟨K,hK,hKn,hcomm,hAK,hXK⟩
  · exact (hn hnormal).elim
  have he := normalClosure_eq_of_commutator hi.complement_le hXK
    ((componentOrbit_le_sup K (T : Subgroup G)).trans (sup_le hK.mem.1 hTH)) hKn hcomm
  by_cases hTK : (T : Subgroup G) ≤ normalizer (K : Set G)
  · have horbit : componentOrbit K (T : Subgroup G) = K :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer K T K le_rfl hTK)
        (le_componentOrbit K T)
    rw [horbit] at hKn hcomm hAK hXK
    have halt := InvariantThree.Source.alternatives_knownSimple hi hsq hT
      hK.mem.1 hKn hK.quasisimple hAK hcomm
    have hNX : H ⊓ normalizer (U : Set G) ≤ normalizer (X : Set G) := by
      rcases halt with halt | hheld
      · obtain ⟨n,hn,hm,_⟩ := invariantWreathSieve T X A H K hi hsq hK.mem
          hK.quasisimple hKn hTK hAK hXK hcomm hw halt
        exact normalizes_of_binary_quotient T hi hK.mem.1 hKn hXK hUT hcore hn hm
      · exact normalizes_of_held_quotient T hi hK.mem.1 hKn hXK hUT hcore
          hsq hK.quasisimple hcomm hindex hheld.2.2.2
    have hHX : H ≤ normalizer (X : Set G) :=
      sup_le ((le_inf le_sup_left hPU).trans hNX)
        (sup_le X.le_normalizer hi.invariant)
    exact (hn ((normal_subgroupOf_iff_le_normalizer
      (show X ≤ H from le_sup_left.trans le_sup_right)).mpr hHX)).elim
  · exact ⟨K,{ toLocalInput := hi
               sqtk := hsq
               component := hK.mem
               quasisimple := hK.quasisimple
               orbit_normal := hKn
               complement_le_orbit := hAK
               orbit_commutator := hcomm
               noncentral := hK.noncentral_component_core
               not_invariant := hTK
               sylow_two := hT },he⟩
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private instance : IsElementaryAbelian 3 (Plane 3) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    exact (by decide +kernel : ∀ x : Plane 3, x^3 = 1)

/-- The actual obstruction supplies all the original swapped-input fields,
including noncentrality and the literal commutator and normal-closure identities. -/
theorem doubleNatural_four_pure_swapped_input_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
        (P : Subgroup G) ≤ B.pointCentralizer w ∧
        (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
        (P : Subgroup G) ≤ normalizer (B.pointSylow w : Set G) ∧
        (B.pointSylow w).relIndex (T : Subgroup G) = 2 ∧
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        H ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
        H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        ¬ H ≤ normalizer (L : Set G) ∧
        ∃ A : Sylow 3 X, ∃ K : Subgroup G,
          SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X
            ((A : Subgroup X).map X.subtype) H K ∧
          conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
          X < componentOrbit K (T : Subgroup G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨hXi,_,P,hlt,hPC,hPM,hH,_,hHN,hout,hn⟩ :=
    D.doubleNatural_four_pure_xi_nonnormal_of_many_of_omega_fixed h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans le_sup_right
  have hT : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  have hsq : IsSQTK KnownSimple.IsKnownSimple H := by
    let N := normalizer (H.pCoreIn 2 : Set G)
    have hHN' : H ≤ N := H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    have hN : IsTwoLocal N := ⟨H.pCoreIn 2,hH.1,isPGroup_pCoreIn 2 H,rfl⟩
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN')).mp
      ((h.simpleQTKE.twoLocal_sqtk hN).subgroup (H.subgroupOf N))
  obtain ⟨_,hXT,⟨eN⟩,⟨eX⟩⟩ := D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf
  have hq : XiOddQuotient 3 (XiQuotient X) := by
    apply XiOddQuotient.of_mulEquiv (e := eX.symm)
    exact Or.inl ⟨inferInstance,plane_card 3⟩
  let A : Sylow 3 X := Classical.arbitrary _
  have hi := localInput_of_mem_Xi hXi hT (show X ⊔ (T : Subgroup G) ≤ H from le_sup_right)
    (by decide : Odd 3) hq A
  have hc : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≤ B.pointSylow w := by
    rw [hXT]
    exact D.doubleNatural_four_pure_normalizer_core_le_of_many h hmany B S w hw hp hfix hf
  have hiT : (B.pointSylow w).relIndex (T : Subgroup G) = 2 := by
    have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
    change B.pointSylow w = _ at he
    rw [he]
    exact S.naturalSylowNormalizer_relIndex D.sylow_normalizes_component
  have hiP : (B.pointSylow w).relIndex (P : Subgroup G) = 2 := by
    have h1 := relIndex_mul_relIndex (⊥ : Subgroup G) (B.pointSylow w) (T : Subgroup G)
      bot_le inf_le_left
    have h2 := relIndex_mul_relIndex (⊥ : Subgroup G) (B.pointSylow w) (P : Subgroup G)
      bot_le hlt.le
    rw [relIndex_bot_left,relIndex_bot_left,hiT] at h1
    rw [relIndex_bot_left,relIndex_bot_left] at h2
    have hcard : Nat.card P = Nat.card T := by rw [P.card_eq_multiplicity,T.card_eq_multiplicity]
    rw [hcard,←h1] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := B.pointSylow w)) h2
  have hPN : (P : Subgroup G) ≤ normalizer (B.pointSylow w : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hlt.le).mp (normal_of_index_eq_two hiP)
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  have hwreath : Nonempty (XiQuotient (X ⊔ (T : Subgroup G)) ≃*
      Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.ParabolicWreath) := by
    rw [hXT]
    exact ⟨eN.trans (RegularWreathProduct.congr eSL (MulEquiv.refl (Multiplicative (ZMod 2))))⟩
  obtain ⟨K,hs,he⟩ := PureFourXi.swapped_input_of_core_interval T hi hsq hn hPN
    inf_le_left hc hiT.le hwreath
  have hstrict : X < componentOrbit K (T : Subgroup G) := by
    refine lt_of_le_of_ne (he ▸ le_conjugateSpanBy X H) ?_
    intro heq
    apply hn
    change (X.subgroupOf H).Normal
    rw [heq]
    exact hs.orbit_normal
  exact ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
