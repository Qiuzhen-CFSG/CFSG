module
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceNonrootCatalogue
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.SourceNonrootBenderExtensions
public import CFSG.Quasithin.ChapterE.Section02.Structure.SymplecticFour.NonrootSymplecticExclusion
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.NonrootAlternatingSixSocle
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SymplecticFour.SuzukiSource
public import CFSG.Quasithin.ChapterG.Section04.NativeTransvectionRecognition.CarrierRows
public import Theory.SpecificGroups.SL2.CardFourEquiv
/-!
# Original root-free source reduction to the remaining native models

The original opposite pair supplies a simple perfect socle, its actual
Theorem C catalogue and a faithful four-dimensional action. The odd-order
theorem supplies an involution in that same socle, so the proved one-centralizer
model dispatcher applies. The A6 socle and symplectic rows are excluded;
A5 becomes binary PSL2. Binary PSL2 and Suzuki outer extensions are eliminated
on the actual pair, and the Suzuki row constructs the original marked witness.

The only remaining outputs are the literal binary pair or the three explicit
exceptional socle families whose independent native-model proofs are pending.
This theorem does not assume a rank-one normalizing actor or assert the final
E.2.7 classification. Source: Aschbacher--Smith E.2.7, printed pp.220--221.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour TwoConjugate InvolutionTypes
open Witnesses.SymplecticFour
open ChapterG.Section04.NativeTransvectionRecognition
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The full original root-free branch, with the completed Suzuki witness
and every completed native exclusion applied to the same source data. -/
theorem source_nonroot_recognized_or_binary_or_exceptional {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hJ : ChapterB.minimalParabolicCore T hP=⊥)
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (e : Sp F≃*L)
    (hmark : (T : Subgroup G).comap (L.subtype.comp e.toMonoidHom)=unipotent)
    (hgen : L⊔(T : Subgroup G)=⊤)
    (V : Subgroup G) [IsElementaryAbelian 2 V] (hVT : V≤T)
    (hVM : V≤(ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hVN : (T : Subgroup G)≤normalizer (V : Set G)) (hr : 2<Nat.card V)
    (hnr : ∀ g ∈ oppositePair (V.comap (L.subtype.comp e.toMonoidHom)),
      ¬IsRootElement g) :
    let P := oppositePair (V.comap (L.subtype.comp e.toMonoidHom))
    HasRecognizedPair T (ChapterB.minimalParabolicMax T hP) V ∨
      (∃ r : ℕ, 2≤r ∧ Nonempty (P ≃* Theory.PSL2.BinaryGroup r)) ∨
      IsExceptionalDegreeFourCarrier (generalizedFitting P) := by
  let f := L.subtype.comp e.toMonoidHom
  let W := V.comap f
  let P := oppositePair W
  let I := generalizedFitting P
  have hf : Function.Injective f := L.subtype_injective.comp e.injective
  obtain ⟨_,hmap,hc,_,h2⟩ := source_geometry hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr
  have hcard : Nat.card W=Nat.card V := by rw [←hmap,card_map_of_injective hf]
  let wj : W →* V := (f.comp W.subtype).codRestrict V (fun x => x.property)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective wj (by
    intro x y h
    exact Subtype.ext (hf (congrArg (fun z : V => (z:G)) h)))
  have hW := hcard.symm ▸ hr
  have hcent : W≤(CentralRootGeometry.parameter (F := F)).range :=
    CentralRootGeometry.parameter_range (F := F) ▸ hc
  obtain ⟨hm,hns,_⟩ := source_geometry_nonroot_socle_catalogue hF hn hG T hP hJ L e hmark hgen V hVT hVM hVN hr hnr
  let j : I →* Sp F := P.subtype.comp I.subtype
  have hj : Function.Injective j := P.subtype_injective.comp I.subtype_injective
  have hC (t : I) (ht : orderOf t=2) : IsPGroup 2 (centralizer ({t} : Set I)) := by
    have hp := isPGroup_centralizer_of_nonroot_involution hF (j t)
      ((orderOf_injective j hj t).trans ht) (hnr (j t) t.val.property)
    have he : centralizer ({t} : Set I) = (centralizer ({j t} : Set (Sp F))).comap j := by
      ext x
      rw [mem_centralizer_singleton_iff,mem_comap,mem_centralizer_singleton_iff,
        ←map_mul,←map_mul,hj.eq_iff]
    rw [he]
    exact hp.comap_of_injective j hj
  have heven : Even (Nat.card I) := Nat.not_odd_iff_even.mp
    (fun ho => hns (_root_.odd_order_theorem I ho))
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 heven.two_dvd
  rcases native_or_exceptional_of_theoremC hns hm t ht (hC t ht) j hj with hnat|hex
  · rcases hnat with h5|h6|⟨r,hrank,hlin⟩|⟨m,hm,⟨em⟩⟩|⟨r,_,hsp⟩
    · obtain ⟨a⟩ := h5
      obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
        (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
      exact .inr (.inl ⟨2,by decide,nonroot_pair_binary_of_socle hF W hW hcent h2 hnr
        (by decide) (a.trans b.symm)⟩)
    · exact (source_original_pair_socle_not_alternating_six hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr hnr h6).elim
    · obtain ⟨K,_,_,hK,⟨a⟩⟩ := hlin
      let : CharP K 2 := EvenProjective.charTwo_of_card hK
      have hnsK : ¬Group.IsSolvable (Theory.PSL2.Group K) := by
        intro hs
        let := hs
        exact hns (Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective)
      obtain ⟨d,hd,⟨b⟩⟩ := Theory.PSL2.OuterSolvable.binary_model_of_not_isSolvable hnsK
      exact .inr (.inl ⟨d,hd,nonroot_pair_binary_of_socle hF W hW hcent h2 hnr hd (a.trans b)⟩)
    · obtain ⟨a⟩ := nonroot_pair_suzuki_of_socle hF W hW hcent h2 hnr hm em
      exact .inl (source_hasRecognizedPair_of_suzuki_pair hF hn T hP hJ L e hmark hgen V hVT hVM hVN hr (by omega) a)
    · exact (not_symplectic_model_of_all_two_centralizers hC hsp).elim
  · exact .inr (.inr hex)
end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
