module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.NormalFourModule
public import Theory.Representation.BinaryConjugationSection.ImageCoordinates
public import Theory.Representation.BinaryConjugationSection.MarkedCentralDuality
public import Theory.Representation.BinaryConjugationSection.PairingCentralizer
public import Theory.Representation.BinaryPermutation.CoreFixedLine

/-!
# Full support and the original two-core action at field four

For the original relatively normal PSL₂(4) component, the entire support
W=[U_J,K] has order 32. Its quotient by the original central involution Z
has the marked five-point augmentation action, compatible with the same
J-action and point-stabilizer overlap as the preceding permutation marking.

The fixed subgroup C_W(K) is exactly Z. The original generalized-Fitting
centrality theorem then gives C_W(O₂(J))=Z, and [W,O₂(J)]=Z. The literal
commutator pairing constructs the dual section O₂(J)/C_{O₂(J)}(W), of
order 16, preserving every actor and the vanishing-commutator pairing.
Finally the three-subgroups lemma forces O₂(K) itself to move W: otherwise
[O₂(J),K] centralizes W, and perfect commutator generation would make
O₂(J) centralize W.

Thus a splitting theorem for an A₅-module cannot be applied to W merely
from the marking of W/Z. The ambient normal field-four exclusion still
requires a further argument. Original 14.6.18 remains an explicit input.
Source: Aschbacher--Smith 14.3.6(1),14.6.1(5),14.6.2,14.6.20 and F.9.7,
refs/quasithin.pdf printed pp.991,1021,1037,321.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Modules.Recognition
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
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

/-- The full original support, with its central kernel retained, has order 32
and the prescribed four-dimensional five-point action on its quotient. -/
theorem source_normal_four_full_support
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    let J := K ⊔ (T : Subgroup G)
    let W := ⁅conjugateSpanBy (localModule T M) J,K⁆
    let Z := centralInvolutions T
    ∃ (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
      (f : J →* Equiv.Perm (Fin 5)) (i : Fin 5)
      (_d : BinaryConjugationSection J W Z ((BinaryPermutation.coreRepresentation (Fin 5)).comp f)),
      f.ker = pCore 2 J ∧
      (f.range = alternatingGroup (Fin 5) ∨ f.range = ⊤) ∧
      (∀ k : K, f ⟨k,(show K ≤ J from le_sup_left) k.property⟩ =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      M.subgroupOf J = (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).comap f ∧
      Nat.card W = 32 := by
  dsimp only
  let J := K ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) J
  let W := ⁅U,K⁆
  have hKJ : K ≤ J := le_sup_left
  have hJH : J ≤ H := sup_le hKH hH.1.2
  have hc : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  have hJ := (source_normal_four_join_minimal hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn hm).1
  obtain ⟨hU,a,eK,f,i,hker,hr,hf,hi,w,hw,hseed,⟨F,hF,hFw,hinj,hs,hd⟩,_⟩ :=
    source_normal_four_module_marking hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn hm
  let := hU
  let c := originalSection a
  have hp := source_component_support_placement hG T hempty hM hunique hmany hcard e hab hsolv
    J hJ K hKJ hc
  have hNW : J ≤ normalizer (W : Set G) := by
    apply (le_inf le_rfl ?_).trans hp.2.2
    exact hJH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  let j := F.toLinearMap.domRestrict (BinaryPermutation.core (Fin 5))
  have hj (g : J) (v : BinaryPermutation.core (Fin 5)) :
      j (BinaryPermutation.coreRepresentation (Fin 5) (f g) v) =
        a.representation (QuotientGroup.mk' (pCore 2 J) g) (j v) :=
    IntertwiningMap.isIntertwining _ _ F g v
  have hjr : c.imageSpace W = LinearMap.range j := by
    rw [hs]
    ext v
    exact ⟨fun ⟨x,hx,he⟩ => ⟨⟨x,hx⟩,he⟩,fun ⟨x,he⟩ => ⟨x,x.property,he⟩⟩
  obtain ⟨d,hcoord⟩ := c.exists_of_image_eq_range (σ := (BinaryPermutation.coreRepresentation (Fin 5)).comp f)
    W (hp.2.1.trans inf_le_left) hp.1 hNW j hinj hj hjr
  have hcW := d.card_section
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := BinaryPermutation.core (Fin 5)),Nat.card_zmod,BinaryPermutation.finrank_core,hZ] at hcW
  exact ⟨eK,f,i,d,hker,hr,hf,hi,by simpa using hcW⟩

/-- The original local core acts nontrivially on the five-dimensional support.
Its faithful quotient is the dual of the marked four-space, and has order 16. -/
theorem source_normal_four_core_duality
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    let J := K ⊔ (T : Subgroup G)
    let W := ⁅conjugateSpanBy (localModule T M) J,K⁆
    let Z := centralInvolutions T
    let Q := J.pCoreIn 2
    ∃ (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
      (f : J →* Equiv.Perm (Fin 5))
      (d : BinaryConjugationSection J W Z ((BinaryPermutation.coreRepresentation (Fin 5)).comp f))
      (sQ : BinaryConjugationSection J Q (Q ⊓ centralizer (W : Set G))
        (Representation.dual ((BinaryPermutation.coreRepresentation (Fin 5)).comp f))),
      f.ker = pCore 2 J ∧
      (∀ k : K, f ⟨k,(show K ≤ J from le_sup_left) k.property⟩ =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      Nat.card W = 32 ∧ W ⊓ centralizer (K : Set G) = Z ∧
      W ⊓ centralizer (Q : Set G) = Z ∧ ⁅W,Q⁆ = Z ∧
      (centralizer (W : Set G)).relIndex Q = 16 ∧
      ∀ (q : Q) (w : W), (sQ.coordinates q).toAdd (d.coordinates w).toAdd = 0 ↔
        ⁅(q : G),(w : G)⁆ = 1 := by
  dsimp only
  let J := K ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) J
  let W := ⁅U,K⁆
  let Z := centralInvolutions T
  let Q := J.pCoreIn 2
  have hKJ : K ≤ J := le_sup_left
  have hJH : J ≤ H := sup_le hKH hH.1.2
  have hc : (K.subgroupOf J).IsCComponent := hK.subgroupOf_of_le hKJ hJH
  have hJ := (source_normal_four_join_minimal hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn hm).1
  have h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab J hJ
  let : IsElementaryAbelian 2 U :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  obtain ⟨eK,f,i,d,hker,hr,hf,hi,hWcard⟩ := source_normal_four_full_support
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn hm
  have hp := source_component_support_placement hG T hempty hM hunique hmany hcard e hab hsolv
    J hJ K hKJ hc
  have hWU : W ≤ U := (hp.2.1.trans inf_le_left)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWU
  have hWQ : W ≤ Q := hWU.trans h.UH_le_QH
  have hZJ : Z ≤ centralizer (J : Set G) := le_centralizer_iff.mp h.H_centralizes
  have hZQ : Z ≤ Q := hp.1.trans hWQ
  have hZcard : Nat.card Z = 2 := h.point_card
  have hWK : W ⊓ centralizer (K : Set G) = Z := by
    apply le_antisymm
    · intro w hw
      let v := (d.coordinates ⟨w,hw.1⟩).toAdd
      have hv (b : alternatingGroup (Fin 5)) :
          BinaryPermutation.coreRepresentation (Fin 5) b.val v = v := by
        obtain ⟨k,hk⟩ := eK.surjective b
        obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) k
        have he := d.equivariant ⟨k,hKJ k.property⟩ ⟨w,hw.1⟩
        have hwfix : (k : G)*w*(k : G)⁻¹ = w := by
          rw [hw.2 k k.property,mul_inv_cancel_right]
        have hwe : (⟨(k : G)*w*(k : G)⁻¹,
            (mem_normalizer_iff.mp (d.normalized (hKJ k.property)) w).mp hw.1⟩ : W) =
            ⟨w,hw.1⟩ := Subtype.ext hwfix
        rw [hwe] at he
        change v = BinaryPermutation.coreRepresentation (Fin 5) (f ⟨k,hKJ k.property⟩) v at he
        rw [hf,hk] at he
        exact he.symm
      have hz : v = 0 := by
        apply Subtype.ext
        exact (Submodule.disjoint_def.mp
          (BinaryPermutation.core_isCompl_constants (Fin 5) (by decide)).disjoint)
          v v.property ((BinaryPermutation.core_fixed_iff_constant (by simp) v).mp hv)
      exact (d.coordinates_eq_one_iff ⟨w,hw.1⟩).mp hz
    · exact le_inf hp.1 (hZJ.trans (centralizer_le hKJ))
  have hcent := (source_component_fitting_placement
    hG T hempty hM hunique hmany hcard e hab hsolv J hJ K hKJ hc).trans
      (source_generalizedFittingPreimage_centralizes_omegaCore hG T hempty hJ h.H_centralizes)
  have hWfix : W ⊓ centralizer (Q : Set G) = Z := by
    apply le_antisymm
    · intro w hw
      have hwom : w ∈ omegaOneCenterAmbient Q :=
        (mem_omegaOneCenterAmbient_iff Q w).mpr
          ⟨hWQ hw.1,elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw.1,hw.2⟩
      exact hWK.le ⟨hw.1,fun k hk => (hcent hk w hwom).symm⟩
    · exact le_inf hp.1 (hZJ.trans (centralizer_le (pCoreIn_le 2 J)))
  have hcomm : ⁅W,Q⁆ ≤ Z :=
    (commutator_mono hWU le_rfl).trans h.commutator_UH_QH_le_point
  have hcommne : ⁅W,Q⁆ ≠ ⊥ := by
    intro hz
    have hWZ : W ≤ Z := by
      rw [←hWfix]
      exact le_inf le_rfl (commutator_eq_bot_iff_le_centralizer.mp hz)
    have hcW := Nat.card_le_card_of_injective
      (inclusion hWZ) (inclusion_injective hWZ)
    rw [hWcard,hZcard] at hcW
    omega
  have hcomeq : ⁅W,Q⁆ = Z := by
    have hd : Nat.card (⁅W,Q⁆ : Subgroup G) ∣ 2 := by
      simpa only [hZcard] using card_dvd_of_le hcomm
    have hcc := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left
      (fun he => hcommne (card_eq_one.mp he))
    exact eq_of_le_of_card_ge hcomm (by rw [hcc,hZcard])
  have hNQ : J ≤ normalizer (Q : Set G) := by
    exact J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  obtain ⟨sQ,hpair⟩ := d.exists_marked_central_duality Q (pCoreIn_le 2 J) hNQ hZQ hZJ
    (by rwa [commutator_comm]) hZcard hWfix
  have hind := d.centralizer_index_of_dual_pairing sQ hpair W le_rfl
  rw [d.imageSpace_self] at hind
  have hcorecard : Nat.card (BinaryPermutation.core (Fin 5)) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,BinaryPermutation.finrank_core]
    rfl
  rw [Nat.card_congr (Submodule.topEquiv).toEquiv,hcorecard] at hind
  exact ⟨eK,f,d,sQ,hker,hf,hWcard,hWK,hWfix,hcomeq,hind,hpair⟩

/-- Even the original component two-core moves its full support. Thus the
upstairs action cannot be inflated from K/O₂(K); only its quotient by Z can. -/
theorem source_normal_four_component_core_moves
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) :
    ¬ K.pCoreIn 2 ≤ centralizer
      (⁅conjugateSpanBy (localModule T M) (K ⊔ (T : Subgroup G)),K⁆ : Subgroup G) := by
  let J := K ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) J
  let W := ⁅U,K⁆
  let Z := centralInvolutions T
  let Q := J.pCoreIn 2
  have hKJ : K ≤ J := le_sup_left
  have hJH : J ≤ H := sup_le hKH hH.1.2
  have hJ := (source_normal_four_join_minimal hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn hm).1
  have h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab J hJ
  let : IsElementaryAbelian 2 U :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  obtain ⟨eK,f,d,sQ,hker,hf,hWcard,hWK,hWfix,hcomm,hindex,hpair⟩ :=
    source_normal_four_core_duality hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn hm
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  have hpK : IsPPerfect 2 K := by
    intro N hN hq
    let := hN
    by_contra hne
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  have hmove : ⁅W,K⁆ = W := commutator_isPPerfect_idempotent K U hpK
    (IsElementaryAbelian.isPGroup 2 U) (hKJ.trans (le_normalizer_conjugateSpanBy _ _))
  have hNQ : J ≤ normalizer (Q : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hQK : Q ≤ normalizer (K : Set G) :=
    ((pCoreIn_le 2 J).trans hJH).trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  have hcore : ⁅K,Q⁆ ≤ K.pCoreIn 2 := commutator_le_pCore_of_mutual_normalization
    K Q (pCore_isPGroup.map J.subtype) (hKJ.trans hNQ) hQK
  intro hcentral
  have h₁ : ⁅⁅K,Q⁆,W⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hcore.trans hcentral)
  have h₂ : ⁅⁅Q,W⁆,K⁆ = ⊥ := by
    rw [commutator_comm Q W,hcomm]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      ((le_centralizer_iff.mp h.H_centralizes).trans (centralizer_le hKJ))
  have h₃ : ⁅⁅W,K⁆,Q⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h₁ h₂
  rw [hmove,hcomm] at h₃
  have hz : Nat.card Z = 2 := h.point_card
  change Z = ⊥ at h₃
  rw [h₃,card_bot] at hz
  omega

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
