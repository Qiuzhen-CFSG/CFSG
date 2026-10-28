module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Quotient
public import Theory.GroupTheory.ConjugationFamilyWeakClosure

/-!
# The radical obstruction in the faithful component quotient

The original residual X has elementary-nine two-core quotient. Its two-core
is therefore a normal Sylow subgroup and maps onto the two-core of every
image, even when the homomorphism kernel has odd-order elements. The proved
O₂(XT) containment puts the actual quotient radical R inside the image of T₁.

Weak closure of R in the image of T would make the image of T₀ normalize R.
If N(R) normalizes the image of X, generation H=<T₀,XT> then makes that image
normal. The previous faithful-component construction proves it is not normal.
The final application records this obstruction on the literal section quotient,
retaining all embedding alternatives, including Held, and the exact nontrivial
L-fixed omega-subgroup premise. It assumes no parabolic identification.

The source component maximality, model markings, L₅(2) radical calculation,
and MS fixed-subgroup discharge remain with qt-d-double-natural-pure-fusion
and the existing qt-rank-two-ms93 producer. The final earlier-input assembly
owner is qt-d-double-natural-centralizers. This is not the ambient Sylow theorem.
Source: Aschbacher--Smith 12.1.4, printed pp.790--791.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
variable {G Q : Type*} [Group G] [Group Q] [Finite G]

private theorem map_core_of_odd_index (X : Subgroup G) (f : G →* Q)
    (hi : ¬ 2 ∣ (pCore 2 X).index) :
    (X.pCoreIn 2).map f = (X.map f).pCoreIn 2 := by
  let S : Sylow 2 X := pCore_isPGroup.toSylow hi
  have hle : pCore 2 (X.map f) ≤ (pCore 2 X).map (f.subgroupMap X) :=
    pCore_isPGroup.le_sylow_of_normal (S.mapSurjective (f.subgroupMap_surjective X))
  have hn : ((pCore 2 X).map (f.subgroupMap X)).Normal :=
    Normal.map inferInstance _ (f.subgroupMap_surjective X)
  have he : (pCore 2 X).map (f.subgroupMap X) = pCore 2 (X.map f) :=
    le_antisymm (le_sSup ⟨hn,pCore_isPGroup.map _⟩) hle
  calc
    _ = ((pCore 2 X).map (f.subgroupMap X)).map (X.map f).subtype := by
      rw [pCoreIn,map_map,map_map]
      rfl
    _ = _ := by rw [he]; rfl
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual residual image has its two-core inside the marked point image,
without any assumption on the homomorphism kernel. -/
theorem doubleNatural_four_pure_residual_image_core_le_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ Chapter1.IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      ∀ H : Subgroup G, PureFourXi.residual T L ≤ H →
      ∀ (Q : Type*) [Group Q] (q : H →* Q),
        (((PureFourXi.residual T L).subgroupOf H).map q).pCoreIn 2 ≤
          ((B.pointSylow w).subgroupOf H).map q := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf H hXH Q _ q
  let X := PureFourXi.residual T L
  obtain ⟨hXi,he,_,⟨e⟩⟩ := D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf
  have hi : ¬ 2 ∣ (pCore 2 (X.subgroupOf H)).index := by
    let a := subgroupOfEquivOfLe hXH
    rw [index_eq_card,Nat.card_congr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).toEquiv,
      Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  rw [←PureFourXi.map_core_of_odd_index (X.subgroupOf H) q hi]
  apply map_mono
  have hc : X.pCoreIn 2 ≤ B.pointSylow w := by
    have hn : X ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) :=
      sup_le X.le_normalizer hXi.invariant
    have hh : X.pCoreIn 2 ≤ (PureFourXi.normalizerJoin T L).pCoreIn 2 := by
      rw [←he]
      exact pCoreIn_mono_of_normalizes le_sup_left hn
    exact hh.trans (D.doubleNatural_four_pure_normalizer_core_le_of_many h hmany B S w hw hp hfix hf)
  intro x hx
  have hh := mem_map_of_mem H.subtype hx
  rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le hXH] at hh
  exact hc hh
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
variable {G Q : Type*} [Group G] [Group Q]

private theorem image_normal_of_weak_radical (P X T U : Subgroup G)
    (hUT : U ≤ T) (hPU : P ≤ normalizer (U : Set G))
    (hTX : T ≤ normalizer (X : Set G))
    (q : (P ⊔ (X ⊔ T) : Subgroup G) →* Q) (hq : Function.Surjective q)
    (R : Subgroup Q)
    (hRU : R ≤ (U.subgroupOf (P ⊔ (X ⊔ T))).map q)
    (hweak : ∀ g : Q, R.map (MulAut.conj g).toMonoidHom ≤
      (T.subgroupOf (P ⊔ (X ⊔ T))).map q → R.map (MulAut.conj g).toMonoidHom = R)
    (hn : normalizer (R : Set Q) ≤
      normalizer ((X.subgroupOf (P ⊔ (X ⊔ T))).map q : Set Q)) :
    ((X.subgroupOf (P ⊔ (X ⊔ T))).map q).Normal := by
  let H := P ⊔ (X ⊔ T)
  have hUH : U ≤ H := hUT.trans (le_sup_right.trans le_sup_right)
  have hXH : X ≤ H := le_sup_left.trans le_sup_right
  have hTH : T ≤ H := le_sup_right.trans le_sup_right
  have hPH : P ≤ H := le_sup_left
  have hp : P.subgroupOf H ≤ normalizer (U.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hUH]
    exact comap_mono hPU
  have ht : T.subgroupOf H ≤ normalizer (X.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq hXH]
    exact comap_mono hTX
  have hpq : (P.subgroupOf H).map q ≤ normalizer ((X.subgroupOf H).map q : Set Q) := by
    apply ((map_mono hp).trans ((U.subgroupOf H).le_normalizer_map q)).trans
    exact (SubgroupFusion.normalizer_le_of_weakly_closed hRU
      (map_mono (comap_mono hUT)) hweak).trans hn
  have htq := (map_mono (f := q) ht).trans ((X.subgroupOf H).le_normalizer_map q)
  have he : P.subgroupOf H ⊔ (X.subgroupOf H ⊔ T.subgroupOf H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hPH,
      map_subgroupOf_eq_of_le hXH,map_subgroupOf_eq_of_le hTH,
      ←MonoidHom.range_eq_map,range_subtype]
  have hgen := congrArg (map q) he
  rw [Subgroup.map_sup,Subgroup.map_sup,←MonoidHom.range_eq_map,
    MonoidHom.range_eq_top_of_surjective q hq] at hgen
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←hgen]
  exact sup_le hpq (sup_le ((X.subgroupOf H).map q).le_normalizer htq)
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The constructed component quotient cannot satisfy both parabolic radical
properties. All original component and quotient markings are retained. -/
theorem doubleNatural_four_pure_component_radical_obstruction_of_many_of_omega_fixed
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
            HeldAlternative 3 (T : Subgroup G) ((A : Subgroup X).map X.subtype) K) ∧
          ∃ hn : H ≤ normalizer (componentOrbit K (T : Subgroup G) : Set G),
            let q := PureFourXi.sectionProjection H (componentOrbit K (T : Subgroup G)) hn
            let R := ((X.subgroupOf H).map q).pCoreIn 2
            (normalizer ((B.pointSylow w).subgroupOf H : Set H)).map q =
              normalizer (((B.pointSylow w).subgroupOf H).map q :
                Set (H ⧸ PureFourXi.sectionKernel H (componentOrbit K (T : Subgroup G)) hn)) ∧
            ¬ ((X.subgroupOf H).map q).Normal ∧
            R ≤ ((B.pointSylow w).subgroupOf H).map q ∧
            ¬ ((∀ g : H ⧸ PureFourXi.sectionKernel H (componentOrbit K (T : Subgroup G)) hn,
                R.map (MulAut.conj g).toMonoidHom ≤ ((T : Subgroup G).subgroupOf H).map q →
                R.map (MulAut.conj g).toMonoidHom = R) ∧
              normalizer (R : Set (H ⧸ PureFourXi.sectionKernel H (componentOrbit K (T : Subgroup G)) hn)) ≤
                normalizer ((X.subgroupOf H).map q :
                  Set (H ⧸ PureFourXi.sectionKernel H (componentOrbit K (T : Subgroup G)) hn))) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,halt,hn,hquot,hnormal⟩ :=
    D.doubleNatural_four_pure_component_quotient_of_many_of_omega_fixed h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  let Y := componentOrbit K (T : Subgroup G)
  let q := PureFourXi.sectionProjection H Y hn
  let R := ((X.subgroupOf H).map q).pCoreIn 2
  have hb : R ≤ ((B.pointSylow w).subgroupOf H).map q :=
    D.doubleNatural_four_pure_residual_image_core_le_of_many h hmany B S w hw hp hfix hf
      H (le_sup_left.trans le_sup_right) _ q
  refine ⟨P,hlt,hPC,hPM,hH,hHN,hout,A,K,hK,hKL,hfaith,hqK,hnK,he,hstrict,hfixK,halt,hn,
    hquot,hnormal,hb,?_⟩
  rintro ⟨hweak,hnorm⟩
  have hi : (B.pointSylow w).relIndex (T : Subgroup G) = 2 := by
    have hm := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
    change B.pointSylow w = _ at hm
    rw [hm]
    exact S.naturalSylowNormalizer_relIndex D.sylow_normalizes_component
  have hiP : (B.pointSylow w).relIndex (P : Subgroup G) = 2 := by
    have h1 := relIndex_mul_relIndex (⊥ : Subgroup G) (B.pointSylow w) (T : Subgroup G)
      bot_le inf_le_left
    have h2 := relIndex_mul_relIndex (⊥ : Subgroup G) (B.pointSylow w) (P : Subgroup G)
      bot_le hlt.le
    rw [relIndex_bot_left,relIndex_bot_left,hi] at h1
    rw [relIndex_bot_left,relIndex_bot_left] at h2
    have hcard : Nat.card P = Nat.card T := by rw [P.card_eq_multiplicity,T.card_eq_multiplicity]
    rw [hcard,←h1] at h2
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := B.pointSylow w)) h2
  have hpnormal : ((B.pointSylow w).subgroupOf (P : Subgroup G)).Normal :=
    normal_of_index_eq_two hiP
  have hPN : (P : Subgroup G) ≤ normalizer (B.pointSylow w : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hlt.le).mp hpnormal
  have hXi := (D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf).1
  exact hnormal (PureFourXi.image_normal_of_weak_radical (P : Subgroup G) X
    (T : Subgroup G) (B.pointSylow w) inf_le_left hPN hXi.invariant q
    (PureFourXi.sectionProjection_surjective H Y hn) R hb hweak hnorm)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
