module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialFourFusion

/-!
# Reduction of the outside involution centralizers

An outside centralizer escaping H cannot act irreducibly through its actual
Sylow subgroup on K/O₂(K) modulo Frattini. The complete intrinsic Ξ embedding
theorem would make K normal there: all its nonnormal alternatives, including
the Held alternative, require a complement of order nine, whereas the marked
Heisenberg complement has order 27. The proved N_G(K) = H then contradicts
escape. Thus the original action has a proper nontrivial invariant subgroup.

The same centralizer is SQTK for the full known-simple class and satisfies
1.1.5 with the original point involution and literal Sylow inclusion. Its
point-residual normalizer is exactly its intersection with H. The final
application chooses an actual escaping centralizer whenever the original
selected four-group is not TI, retaining both the invariant subgroup and
these genuine earlier-source hypotheses.

The reducible overgroup analysis and the TI conclusion of 14.7.26 remain
open, as do the subsequent extraspecial exclusion and 14.7.52 assembly.
Source: Aschbacher–Smith, refs/quasithin.pdf, printed pp.1052–1053;
1.1.6, p.503, and 1.3.4, pp.509–511.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- If an outside involution centralizer escapes H, its actual Sylow
centralizer acts reducibly on the marked extraspecial Frattini quotient.
The full intrinsic embedding theorem excludes every irreducible alternative,
including the Held alternative, by the actual complement order 27. -/
theorem extraspecial_four_frattini_reducible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1)
    (hout : ¬ centralizer ({x} : Set G) ≤ F.H) :
    let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
    let hn : S ≤ normalizer (K F : Set G) :=
      inf_le_left.trans ((F.invariant 1).trans (H_normalizes_K F))
    ∃ A : Subgroup (XiFrattiniQuotient (K F)), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ s : S, ∀ a ∈ A, xiFrattiniAction S (K F) hn s a ∈ A := by
  classical
  let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
  let C := centralizer ({x} : Set G)
  have hn : S ≤ normalizer (K F : Set G) :=
    inf_le_left.trans ((F.invariant 1).trans (H_normalizes_K F))
  change ∃ A : Subgroup (XiFrattiniQuotient (K F)), A ≠ ⊥ ∧ A ≠ ⊤ ∧
    ∀ s : S, ∀ a ∈ A, xiFrattiniAction S (K F) hn s a ∈ A
  by_contra hnot
  have hirr : ∀ A : Subgroup (XiFrattiniQuotient (K F)),
      (∀ s : S, ∀ a ∈ A, xiFrattiniAction S (K F) hn s a ∈ A) → A = ⊥ ∨ A = ⊤ := by
    intro A hA
    by_contra! ha
    exact hnot ⟨A,ha.1,ha.2,hA⟩
  have hDK' : D ≤ K F := hDK.trans (map_subtype_le _)
  have hDcentral : D ≤ centralizer (K F : Set G) := by
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    exact hDK.trans inf_le_right
  have hKC : K F ≤ C := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr ((hDcentral hx) k hk)
  have hgenC : K F ⊔ S ≤ C := sup_le hKC inf_le_right
  have hgenH : K F ⊔ S ≤ F.H := sup_le (K_le_H F) (inf_le_left.trans (F.invariant 1))
  have hDcore : D ≤ (K F ⊔ S).pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 D) (hDK'.trans le_sup_left) (hgenH.trans hND.ge)
  have hjoin : K F ⊔ S ∈ H G := by
    intro hc
    have hh : D = ⊥ := le_antisymm (hc ▸ hDcore) bot_le
    simp only [hh, Subgroup.card_bot] at hcard
    omega
  obtain ⟨e⟩ := he
  have hq : XiOddQuotient 3 (XiQuotient (K F)) := Or.inr
    ⟨(HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm,
      (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)),
      (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))⟩
  have hX : K F ∈ Xi G S := ⟨K_twoPerfect F,hn,hjoin,⟨3,by decide,by decide,hq⟩,hirr⟩
  have hS : IsSylowIn 2 S C :=
    (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier ⟨e⟩
      D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
  have hxorder : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := D) x hx)
    (fun hx1 => hxZ (hx1 ▸ (F.Vi 1).one_mem))
  let b := XiEmbedding.localInput_of_mem_Xi hX hS hgenC
    (by decide : Odd 3) hq (default : Sylow 3 (K F))
  rcases b.adequate_knownSimple (d.qtke.involution_centralizer_sqtk hxorder) hS with
    hnormal | ⟨J,_,_,_,ha⟩
  · have hN : C ≤ normalizer (K F : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hKC).mp hnormal
    exact hout (hN.trans (extraspecial_normalizer_eq_H d h hab structural previous faithful earlier ⟨e⟩).1.le)
  · have hplane : Nonempty (((default : Sylow 3 (K F)) : Subgroup (K F)).map (K F).subtype ≃*
        XiEmbedding.Plane 3) := by
      rcases ha with ha | ha
      · exact ha.1
      · exact ha.2.1
    obtain ⟨ep⟩ := hplane
    have h27 : Nat.card (((default : Sylow 3 (K F)) : Subgroup (K F)).map (K F).subtype) = 27 :=
      (Nat.card_congr b.complementQuotientEquiv.toEquiv).trans
        ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
    have h9 := (Nat.card_congr ep.toEquiv).trans (XiEmbedding.plane_card 3)
    omega

/-- The outside centralizer has the full known-simple local hypothesis and
satisfies the original 1.1.5 hypotheses with the literal source point. -/
theorem extraspecial_four_centralizer_source_setup
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
    let C := centralizer ({x} : Set G)
    IsSQTK KnownSimple.IsKnownSimple C ∧
      C ⊓ normalizer (F.Li L 1 : Set G) = F.H ⊓ C ∧
      ∃ z : G, orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
        ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = (T : Subgroup G) ⊓ C ∧
          Lemma115Hypotheses C P F.H z := by
  let C := centralizer ({x} : Set G)
  have hx1 : x ≠ 1 := fun he => hxZ (he ▸ (F.Vi 1).one_mem)
  have hxo : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := D) x hx) hx1
  obtain ⟨hNK,hHC,hmax,_⟩ := extraspecial_source_14721 d h hab structural previous faithful earlier he
  have hNpoint : normalizer (F.Li L 1 : Set G) = F.H :=
    (extraspecial_core_normalizer_eq d h hab structural previous faithful he).2.trans hNK
  refine ⟨d.qtke.involution_centralizer_sqtk hxo,?_,?_⟩
  · rw [hNpoint,inf_comm]
  have hZcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z,hz1,_⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp hZcard
  have hzne : (z : G) ≠ 1 := fun hh => hz1 (Subtype.ext hh)
  have hzo : orderOf (z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := D) (z : G) (hZD z.property)) hzne
  have hzpow : zpowers (z : G) = F.Vi 1 := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr z.property)
    rw [Nat.card_zpowers,hzo,hZcard]
  have hzC : centralizer ({(z : G)} : Set G) = F.H := calc
    centralizer ({(z : G)} : Set G) = centralizer (zpowers (z : G) : Set G) := by
      rw [zpowers_eq_closure,centralizer_closure]
    _ = centralizer (F.Vi 1 : Set G) :=
      congrArg (fun A : Subgroup G => centralizer (A : Set G)) hzpow
    _ = F.H := hHC.symm
  obtain ⟨P,hP⟩ := (extraspecial_four_centralizer_sylow
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
  refine ⟨z,hzo,hzpow,P,hP,?_⟩
  have hB : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hxo]; decide)
  have hBC : zpowers x ≤ C := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCC : centralizer (zpowers x : Set G) = C := by
    rw [zpowers_eq_closure,centralizer_closure]
  apply lemma_1_1_6 (B := zpowers x)
    (fun hb => hx1 (zpowers_eq_bot.mp hb)) hB hBC hCC.le
    (hCC ▸ Subgroup.centralizer_le_normalizer (zpowers x : Set G)) P T
    (hP ▸ inf_le_left) hzo (hDT (hZD z.property)) ?_ hmax hzC.le
    (fun N hN hTN => mem_He_iff.mpr (d.qtke.evenCharacteristic T N hN hTN))
  intro t ht
  exact ((normalizer_le_centralizer_of_card_two (F.Vi 1) hZcard)
    (F.invariant 1 ht) z z.property).symm

/-- A selected non-TI four-group supplies an actual escaping involution
centralizer and a proper invariant subgroup of the original Frattini section.
This is the reducible branch of the remaining 14.7.26 analysis. -/
theorem extraspecial_center_four_escaping_reducible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H ∧
      (IsTISubgroup D ∨ (IsElementaryAbelian 2 D ∧
        ∃ x ∈ D, x ∉ F.Vi 1 ∧ ¬ centralizer ({x} : Set G) ≤ F.H ∧
          let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
          let hn : S ≤ normalizer (K F : Set G) :=
            inf_le_left.trans ((F.invariant 1).trans (H_normalizes_K F))
          (∃ A : Subgroup (XiFrattiniQuotient (K F)), A ≠ ⊥ ∧ A ≠ ⊤ ∧
            ∀ s : S, ∀ a ∈ A, xiFrattiniAction S (K F) hn s a ∈ A) ∧
          (∃ z : G, orderOf z = 2 ∧ zpowers z = F.Vi 1 ∧
            ∃ P : Sylow 2 (centralizer ({x} : Set G)),
              (P : Subgroup (centralizer ({x} : Set G))).map
                (centralizer ({x} : Set G)).subtype = S ∧
              Lemma115Hypotheses (centralizer ({x} : Set G)) P F.H z))) := by
  classical
  obtain ⟨D,hZD,hDK,hcard,hDT,hND,hcases⟩ := extraspecial_center_four_ti_reduction
    d h hab structural previous faithful earlier he
  refine ⟨D,hZD,hDK,hcard,hDT,hND,?_⟩
  rcases hcases with ht | ⟨hele,_,hnc⟩
  · exact Or.inl ht
  let := hele
  by_cases ht : IsTISubgroup D
  · exact Or.inl ht
  have hout := (extraspecial_four_ti_iff_centralizer_containment
    d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hnc).not.mp ht
  push Not at hout
  obtain ⟨x,hx,hxZ,hout⟩ := hout
  exact Or.inr ⟨hele,x,hx,hxZ,hout,
    extraspecial_four_frattini_reducible d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ hout,
    (extraspecial_four_centralizer_source_setup d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hx hxZ).2.2⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
