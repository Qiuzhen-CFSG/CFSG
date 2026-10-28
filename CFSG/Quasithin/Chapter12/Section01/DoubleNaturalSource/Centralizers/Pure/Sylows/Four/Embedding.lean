module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.XiNonnormal
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.XiFaithful
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Orbit

/-!
# The actual faithful component in the escaping pure-point overgroup

Apply the proved adequate p=3 embedding theorem to the original X and
H=<T0,XT>. The full ambient Sylow restricts to H. Its containment in the
normalizer of the nontrivial Thompson subgroup supplies the SQTK hypothesis.
The literal elementary-nine quotient identifies the cubic complement.

The component orbit is exactly the H-normal closure of X and properly
contains X by the proved relative nonnormality. The genuine 1.3.9(2)
application makes the selected component faithful. Its centralizer on W
is trivial since the orbit contains X. All four original embedding rows,
their quotient markings, and the corrected Held alternative are retained.

The only extra premise is the exact nontrivial L-fixed subgroup in the
point omega center. Its ambient MS proof remains with the existing
`qt-rank-two-ms93` producer and this task's assembly. Maximality, the
component exclusions and parabolic-normalizer contradiction remain with
`qt-d-double-natural-pure-fusion`; `qt-d-double-natural-centralizers` supplies
the original earlier inputs. This is not the finished 12.1.4 Sylow theorem.
Source: Aschbacher--Smith 12.1.4, printed p.790, using the corrected
1.3.4 theorem, pp.509--511, and 1.3.9(2), p.514.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private instance : IsElementaryAbelian 3 (Plane 3) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    exact (by decide +kernel : ∀ x : Plane 3, x^3 = 1)

/-- The original escaping overgroup contains an actual faithful local
component with all adequate embedding alternatives and the literal normal
closure retained. The sole extra MS premise is fixed-subgroup nontriviality. -/
theorem doubleNatural_four_pure_component_embedding_of_many_of_omega_fixed
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
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        H ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
        H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        ¬ H ≤ normalizer (L : Set G) ∧
        ∃ A : Sylow 3 X, ∃ K : Subgroup G,
          K ∈ cComponentsIn H ∧ K ∈ Chapter1.L G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          IsQuasisimple (XiQuotient K) ∧
          ((componentOrbit K (T : Subgroup G)).subgroupOf H).Normal ∧
          conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
          X < componentOrbit K (T : Subgroup G) ∧
          componentOrbit V (T : Subgroup G) ⊓
            centralizer (componentOrbit K (T : Subgroup G) : Set G) = ⊥ ∧
          (Alternatives 3 (T : Subgroup G) ((A : Subgroup X).map X.subtype) K ∨
            HeldAlternative 3 (T : Subgroup G) ((A : Subgroup X).map X.subtype) K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  obtain ⟨hXi,_,P,hlt,hPC,hPM,hH,_,hHN,hout,hn⟩ :=
    D.doubleNatural_four_pure_xi_nonnormal_of_many_of_omega_fixed h hmany B S w hw hp hfix hf hne
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans le_sup_right
  have hT : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]⟩
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hJne : J ≠ ⊥ := by
    intro he
    exact (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).2
      (by change J ≤ _; rw [he]; exact bot_le)
  have hlocal : IsTwoLocal (normalizer (J : Set G)) :=
    ⟨J,hJne,T.isPGroup'.to_le (sSup_le fun _ hA => hA.1),rfl⟩
  have hsq : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
      ((h.simpleQTKE.twoLocal_sqtk hlocal).subgroup (H.subgroupOf (normalizer (J : Set G))))
  obtain ⟨e⟩ := (D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf).2.2.2
  have hq : XiOddQuotient 3 (XiQuotient X) := by
    apply XiOddQuotient.of_mulEquiv (e := e.symm)
    exact Or.inl ⟨inferInstance,plane_card 3⟩
  let A : Sylow 3 X := Classical.arbitrary _
  have hi := localInput_of_mem_Xi hXi hT (show X ⊔ (T : Subgroup G) ≤ H from le_sup_right)
    (by decide : Odd 3) hq A
  rcases Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.adequate_three_normalClosure
      hi hsq hT with he | ⟨K,hK,hqK,hnK,_,_,he,halt⟩
  · apply (hn ?_).elim
    apply (normal_subgroupOf_iff_le_normalizer
      (show X ≤ H from le_sup_left.trans le_sup_right)).mpr
    change conjugateSpanBy X H = X at he
    rw [←he]
    exact le_normalizer_conjugateSpanBy X H
  have hXK : X ≤ componentOrbit K (T : Subgroup G) := he ▸ le_conjugateSpanBy X H
  have hstrict : X < componentOrbit K (T : Subgroup G) := by
    refine lt_of_le_of_ne hXK ?_
    intro heq
    apply hn
    change (X.subgroupOf H).Normal
    rw [heq]
    exact hnK
  have hfixK : componentOrbit V (T : Subgroup G) ⊓
      centralizer (componentOrbit K (T : Subgroup G) : Set G) = ⊥ := by
    apply bot_unique
    exact (inf_le_inf_left _ (centralizer_le hXK)).trans_eq
      (D.doubleNatural_four_pure_xi_centralizer_of_many h hmany B S w hw hp hfix hf)
  have hKL := mem_L_of_cComponent hH.1 hT hK.1 hK.2
  have hfaith := (Terminal.lemma_1_3_9_two_source h.simpleQTKE T
    (D.doubleNatural_four_pure_xi_faithful_of_many h hmany B S w hw hp hfix hf) hKL hXK).2
  exact ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,halt⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
