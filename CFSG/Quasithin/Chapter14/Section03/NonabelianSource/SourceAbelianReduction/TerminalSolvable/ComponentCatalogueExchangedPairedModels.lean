module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedLinearThree
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentModels
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentExclusions
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentSharpExclusions
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.SharpDegree
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.UnitarySource
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.SourceModels
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedPairedAction
public import Theory.SpecificGroups.SymplecticFour.Sylow.FrattiniBound
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SylowExponent

/-!
# A5 recognition for the paired constituent image

The actual single-component G.9 hypothesis, self-duality for that same
component, degree at most m+2 and elementary Sylow two-subgroups leave A5.
The full known-simple and central-three-cover catalogue is exhausted. The
Sylow condition excludes the additional sharp-degree rows A6, A7, A8,
Sp4(4) and the derived binary G2 group.

Source: Aschbacher--Smith G.9.3 and G.10.15, printed pp.356 and 362--363.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
set_option linter.unusedSectionVars false
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
namespace PairedA5Models

private def sixEmbedding (n : ℕ) (hn : 6 ≤ n) :
    alternatingGroup (Fin 6) →* alternatingGroup (Fin n) :=
  (((Equiv.Perm.extendDomainHom (Fin.castLEEmb hn).toEquivRange).comp
    (alternatingGroup (Fin 6)).subtype)).codRestrict _ (by
      intro x
      change Equiv.Perm.sign (x.val.extendDomain _) = 1
      rw [Equiv.Perm.sign_extendDomain]
      exact x.prop)

private theorem sixEmbedding_injective (n : ℕ) (hn : 6 ≤ n) :
    Function.Injective (sixEmbedding n hn) := by
  intro x y h
  apply Subtype.ext
  exact Equiv.Perm.extendDomainHom_injective (Fin.castLEEmb hn).toEquivRange
    (congrArg Subtype.val h)

private theorem not_alternating_elementary {S : Type*} [Group S] [Finite S]
    (he : ∀ P : Sylow 2 S, IsElementaryAbelian 2 P)
    {n : ℕ} (hn : 6 ≤ n) (e : S ≃* alternatingGroup (Fin n)) : False := by
  let P : Sylow 2 S := Classical.choice inferInstance
  let : IsElementaryAbelian 2 P := he P
  exact alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute P
    (fun a b _ _ => show Commute a b from mul_comm a b)
    (e.symm.toMonoidHom.comp (sixEmbedding n hn))
    (e.symm.injective.comp (sixEmbedding_injective n hn))

private theorem not_native_g2_elementary {S : Type*} [Group S] [Finite S]
    (he : ∀ P : Sylow 2 S, IsElementaryAbelian 2 P)
    (e : S ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) : False := by
  have hE : IsElementaryAbelian 2 Atlas.G2.BinaryParabolicPair.derivedSylow :=
    Theory.GroupTheory.ExchangedOrbit.elementary_sylow_image e.toMonoidHom e.surjective he _
  exact Atlas.G2.BinaryParabolicPair.derivedSylow_not_commutative hE.toIsMulCommutative

open ChapterG.Section09 ChapterG.Section09.DefiningCharacteristic
open Chapter1.Section02.LocalModels
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {A L : Subgroup D} {m : ℕ}
  (h : ComponentHypothesis KnownSimple.IsKnownSimple ρ A L L m)
  (hd : finrank (ZMod 2) V ≤ m+2)
  (he : ∀ P : Sylow 2 L, IsElementaryAbelian 2 P)
  (hs : Nonempty (Representation.Equiv (ρ.comp L.subtype) (Representation.dual (ρ.comp L.subtype))))
include h hd
include hs in
private theorem not_linear_three_cover {k : Type*} [Field k] [Finite k] [CharP k 2]
    (π : SL(3,k) →* L) (hπ : Function.Surjective π) (hz : π.ker ≤ center SL(3,k))
    {n : ℕ} (hn : 0 < n) (hcard : Nat.card k = 2^n) : False :=
  MarkedLinearThree.not_two_copy_linear_three h hs (by omega) π hπ hz n hn hcard

include hs in
private theorem not_linear_three {n : ℕ} (hn : 0 < n)
    (model : ClassicalGroup.IsPSL L 3 (2^n) ∨ IsSL L 3 (2^n)) : False := by
  rcases model with model | model
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    exact not_linear_three_cover h hd hs (e.symm.toMonoidHom.comp (Matrix.PSL3.projection k))
      (e.symm.surjective.comp (Matrix.PSL3.projection_surjective k))
      (by rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective, Matrix.PSL3.projection_ker]) hn hcard
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
    let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    exact not_linear_three_cover h hd hs e.symm.toMonoidHom e.symm.surjective
      (by rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]; exact bot_le) hn hcard

private theorem rank_one_binary {n : ℕ} (hn : 2 ≤ n)
    (model : ClassicalGroup.IsPSL L 2 (2^n)) : Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  have hm := rank_one_module_alternatives h
    (e.trans (Theory.PSL2.sl2QuotientEquiv k).symm) n hn hcard
  have hactor := hm.1
  have hn2 : n=2 := by
    rcases hm.2 with ⟨hdeg,_,_⟩ | ⟨a,ha,hna,hdeg,_⟩ | ⟨hna,hdeg,_⟩ <;> omega
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (hn2 ▸ hcard)
  exact ⟨e.trans a⟩

include he in
private theorem not_symplectic {n : ℕ} (hn : 2 ≤ n)
    (model : ClassicalGroup.IsPSp L 2 (2^n)) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  let E := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  let P : Sylow 2 L := Classical.choice inferInstance
  let : IsElementaryAbelian 2 P := he P
  let : Fact (IsPGroup 2 P) := ⟨P.isPGroup'⟩
  apply Theory.SpecificGroups.SymplecticFour.FrattiniBound.not_equiv_of_small_sylow_frattini
    hcard (by omega) E P
  rw [frattini_eq_bot_of_isElementaryAbelian (p:=2)]
  simp

private theorem not_g2 {n : ℕ} (hn : 2 ≤ n)
    (model : ClassificationModels.IsG2At L (2^n)) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  exact G2Recognition.not_nonbinary_of_sharp_degree h (by omega)
    (e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hcard).symm) hn hcard

include he in
private theorem not_binary_linear {n : ℕ} (hn : n=4 ∨ n=5)
    (model : ClassicalGroup.IsPSL L n 2) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : Fintype k := Fintype.ofFinite k
  let a : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  let E := ((e.trans (Atlas.fieldEquivPSL n a)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by rcases hn with rfl|rfl <;> decide))).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)).symm
  let : Finite (LinearMap.GeneralLinearGroup (ZMod 2) (Fin n → ZMod 2)) :=
    Finite.of_surjective E E.surjective
  exact _root_.BinaryLinear.not_elementary_sylow_of_finrank_ge_three
    (by simp only [Module.finrank_pi,Fintype.card_fin]; rcases hn with rfl|rfl <;> decide)
    (Theory.GroupTheory.ExchangedOrbit.elementary_sylow_image E.toMonoidHom E.surjective he)

include he in
private theorem native_g2 (e : L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Nonempty (L ≃* alternatingGroup (Fin 5)) :=
  (not_native_g2_elementary he e).elim

include he in
private theorem binary_symplectic (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) :
    Nonempty (L ≃* alternatingGroup (Fin 5)) :=
  (not_alternating_elementary he (by decide : 6 ≤ 6) (e.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))).elim

include hs he in
private theorem odd_two {p e : ℕ} (hp : p.Prime) (ho : Odd p) (hepos : 0 < e)
    (model : ClassicalGroup.IsPSL L 2 (p^e)) : Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  let : IsQuasisimple L := h.component.2
  rcases ChapterG.Section07.OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) hp ho hepos model
    h.single_component_degree_bound with hb | ht | hex
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := hb
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard
    exact ⟨e.trans a⟩
  · exact (not_linear_three h hd hs (n := 1) (by decide) (Or.inl (by simpa using ht))).elim
  · exact binary_symplectic h hd he hex.some

include he in
private theorem odd_three {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (model : ChapterG.Section07.OddCharacteristic.IsLinearUnitaryThree L p) :
    Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  let : IsQuasisimple L := h.component.2
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  obtain ⟨e,_⟩ := ChapterG.Section07.OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) hp ho model h.single_component_degree_bound
  exact native_g2 h hd he e.some

include hs he in
private theorem alternating {n : ℕ} (hn : 5≤n ∧ n≤8)
    (e : L ≃* alternatingGroup (Fin n)) : Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  by_cases hn5 : n = 5
  · exact ⟨hn5 ▸ e⟩
  · exact (not_alternating_elementary he (by omega) e).elim

private theorem rank_one (model : ClassificationModels.IsBenderModel L) : Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  cases model with
  | linear n hn hm => exact rank_one_binary h hd hn hm
  | unitary n hn hm =>
    obtain ⟨k,_,_,J,hcard,hconj,e⟩ := hm
    exact (TwistedExclusions.not_unitary_three_positive_exponent h J (by omega) hcard hconj (Or.inr e)).elim
  | suzuki k hk e => exact (h.not_suzuki hk e.some).elim

include hs he in
private theorem rank_two (model : RankTwoTheoremC L) : Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  cases model with
  | linear n hn hm => exact (not_linear_three h hd hs hn (Or.inl hm)).elim
  | symplectic n hn hm => exact (not_symplectic h hd he hn hm).elim
  | g2 n hn hm => exact (not_g2 h hd hn hm).elim
  | triality n hn hm => exact (TwistedExclusions.not_triality_positive_exponent h hn hm).elim
  | ree k hk hm =>
    obtain ⟨d,e⟩ := hm
    exact (TwistedExclusions.not_ree_of_local_block h hk d e.some).elim
  | symplectic_derived e =>
    exact (not_alternating_elementary he (by decide : 6 ≤ 6) (e.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).elim
  | g2_derived e => exact native_g2 h hd he e.some
  | tits e => exact (TwistedExclusions.not_tits_of_source_component h e.some).elim

omit h hd in
private theorem simple_center_eq_bot {S : Type*} [Group S] [IsSimpleGroup S] [Group.IsPerfect S] :
    center S = ⊥ := by
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp ht)).elim

include hs he in
private theorem simple_models (hsimple : IsSimpleGroup L) (model : TheoremCModel L) :
    Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  let : IsSimpleGroup L := hsimple
  let : IsQuasisimple L := h.component.2
  let q : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq simple_center_eq_bot).trans QuotientGroup.quotientBot
  have hsharp : finrank (ZMod 2) V ≤ m+2 := by omega
  cases model with
  | alternating n hn e => exact alternating h hd he hs hn e.some
  | linear_odd p e hp ho hep _ hm => exact odd_two h hd he hs hp ho (by rcases hep with rfl | rfl <;> decide) hm
  | three_odd p hp ho unitary hm =>
    apply odd_three h hd he hp ho
    cases unitary with
    | false => exact Or.inl hm
    | true => exact Or.inr (Or.inr (Or.inl hm))
  | rank_one hm => exact rank_one h hd hm
  | rank_two hm => exact rank_two h hd he hs hm
  | binary_linear n hn hm => exact (not_binary_linear h hd he hn hm).elim
  | sporadic name hne e =>
    cases name with
    | m11 => exact (h.not_m11_central_quotient (q.trans e.some)).elim
    | m12 => exact (h.not_m12_of_sharp_degree hsharp e.some).elim
    | m22 => exact (h.not_m22_of_sharp_degree hsharp e.some).elim
    | m23 => exact (h.not_m23_of_sharp_degree hsharp e.some).elim
    | m24 => exact (h.not_m24_of_sharp_degree hsharp e.some).elim
    | j2 => exact (h.not_janko_two_of_sharp_degree hsharp e.some).elim
    | j3 => exact (hne rfl).elim
    | j4 => exact (h.not_janko_four e.some).elim
    | hs => exact (h.not_higman_sims e.some).elim
    | he => exact (h.not_held e.some).elim
    | ru => exact (h.not_rudvalis e.some).elim
  | janko_one e => exact (h.not_j1_central_quotient (q.trans e.some)).elim

include hs he in
private theorem cover_models (model : ThreeCoverModel L) : Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  have hsharp : finrank (ZMod 2) V ≤ m+2 := by omega
  cases model with
  | classical unitary q hq hm =>
    cases unitary with
    | false =>
      change IsSL L 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · exact (not_linear_three h hd hs hn (Or.inr hm)).elim
      · exact odd_three h hd he hp ho (Or.inr (Or.inl hm))
    | true =>
      change IsSU L 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · obtain ⟨k,_,_,J,hcard,hconj,e⟩ := hm
        exact (TwistedExclusions.not_unitary_three_positive_exponent h J hn hcard hconj (Or.inl e)).elim
      · exact odd_three h hd he hp ho (Or.inr (Or.inr (Or.inr hm)))
  | alternating_six hm => exact (h.not_triple_alternating_six_of_sharp_degree hsharp hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | alternating_seven hm => exact (h.not_triple_alternating_seven hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | mathieu hm => exact (h.not_m22_central_quotient_of_sharp_degree hsharp hm.2.2.some).elim

include hs he in
/-- The exact sharp degree bound and elementary Sylow two-subgroups force A5. -/
theorem alternating_five_of_selfDual_sharp_elementary : Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  rcases h.single_component_models with ⟨hi,hm⟩ | ⟨_,hm⟩
  · exact simple_models h hd he hs hi hm
  · exact cover_models h hd he hs hm
end PairedA5Models
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
