module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Quotient

/-!
# Elementary and order conditions for the local pairing seed

The actual local span is elementary abelian when b > 4. Every quotient seed
inside it therefore generates a group with trivial Frattini subgroup.
A seed supported on Z_a modulo C(Q_c) inherits the source order-four
commutator bound. If it generates W modulo C(Q_c), the original displacement
hypothesis forces its commutator to be nontrivial. These verify three numerical
and structural fields of SourceData without a trapped-radius assumption.

Source: Meierfrankenfeld--Stellmacher (1993), the application of (1.7)(i)
in (4.4.1), printed pp.890--891.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase
open RankOnePairing Escape.PairingControl.FirstPairing
variable {M : Type*} [Group M] {L R : Subgroup M}
variable [Finite M] {source : LocalSource L R} {geometry : Geometry R}

/-- Taking an actual local quotient cannot increase subgroup order. -/
theorem quotientImage_card_le (c : Vertex R) (H : Subgroup (FreeAmalgam R))
    (hH : H ≤ stabilizer R c) : Nat.card (quotientImage c H) ≤ Nat.card H := by
  let := finite_stabilizer R c
  let q : H.subgroupOf (stabilizer R c) → quotientImage c H :=
    fun x => ⟨quotientMap c x, mem_map_of_mem _ x.property⟩
  have hq : Function.Surjective q := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact (Nat.card_le_card_of_surjective q hq).trans_eq
    (Nat.card_congr (subgroupOfEquivOfLe hH).toEquiv)

/-- Every seed in the actual local span generates an elementary abelian
subgroup of G_c/D_c, so its Frattini subgroup is trivial. -/
theorem generated_frattini_eq_bot {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 4 < geometry.b R)
    (seed : Subgroup (LocalQuotient c))
    (hs : seed ≤ quotientImage c (localZSpan R a c)) : frattini (generated seed) = ⊥ := by
  let := localZSpan_elementary R hc hd.le hb
  have hWS : localZSpan R a c ≤ stabilizer R c :=
    (localZSpan_le_Q R hc hd.le (by omega : 2 < geometry.b R)).trans (fun _ hx => hx.1)
  let := IsElementaryAbelian.subgroupOf (p := 2) hWS
  let : IsElementaryAbelian 2 (quotientImage c (localZSpan R a c)) :=
    IsElementaryAbelian.map (quotientMap c)
  let := quotientImage_normal c (localZSpan R a c) (localZSpan_normalized R a c)
  let := IsElementaryAbelian.of_le (p := 2) (generated_le _ _ hs)
  let : Fact (IsPGroup 2 (generated seed)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

/-- The source q² bound also holds for any seed with the indicated origin,
even if it contains additional elements centralizing Q_c. -/
theorem seed_commutator_card_le_four (common : CommonFacts R source geometry)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 4 < geometry.b R)
    (seed : Subgroup (LocalQuotient c))
    (hs : seed ≤ quotientImage c (Z R a) ⊔
      centralizer (quotientImage c (Q R c) : Set (LocalQuotient c))) :
    Nat.card (⁅seed, quotientImage c (Q R c)⁆ : Subgroup (LocalQuotient c)) ≤ 4 := by
  let := quotientImage_normal c (Q R c) (Q_normalized R c)
  have hQS : Q R c ≤ stabilizer R c := fun _ hx => hx.1
  have hAS : Z R a ≤ stabilizer R c := (Z_le_localZSpan R a c).trans
    ((localZSpan_le_Q R hc hd.le (by omega : 2 < geometry.b R)).trans hQS)
  have he := commutator_eq_of_centralizing_sup
    (V := quotientImage c (Q R c))
    (C := centralizer (quotientImage c (Q R c) : Set (LocalQuotient c)))
    (X := quotientImage c (Z R a)) (sup_comm _ _) le_rfl le_normalizer_of_normal
  have hbound : ⁅seed, quotientImage c (Q R c)⁆ ≤ quotientImage c ⁅Z R a, Q R c⁆ := by
    rw [quotientImage_commutator c _ _ hAS hQS,
      commutator_comm seed, commutator_comm (quotientImage c (Z R a)), he]
    exact commutator_mono le_rfl hs
  exact (card_le_of_le hbound).trans
    ((quotientImage_card_le c _ ((Subgroup.commutator_le_sup _ _).trans (sup_le hAS hQS))).trans
      (displacement_card_le_four common ha hd))

omit [Finite M] in
/-- A seed generating W modulo C(Q_c) has nontrivial displacement whenever
the original Z_a does. Normal closure propagates a vanishing displacement. -/
theorem seed_commutator_nontrivial {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 4 < geometry.b R)
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c)
    (seed : Subgroup (LocalQuotient c))
    (hspan : quotientImage c (localZSpan R a c) ≤ generated seed ⊔
      centralizer (quotientImage c (Q R c) : Set (LocalQuotient c))) :
    Nat.card (⁅seed, quotientImage c (Q R c)⁆ : Subgroup (LocalQuotient c)) ≠ 1 := by
  intro hone
  let := quotientImage_normal c (Q R c) (Q_normalized R c)
  have hzero := card_eq_one.mp hone
  have hgen : ⁅generated seed, quotientImage c (Q R c)⁆ = ⊥ :=
    le_bot_iff.mp (generated_commutator_le _ _ ⊥ hzero.le)
  have hW := commutator_eq_bot_iff_le_centralizer.mpr
    (hspan.trans (sup_le (commutator_eq_bot_iff_le_centralizer.mp hgen) le_rfl))
  have hQS : Q R c ≤ stabilizer R c := fun _ hx => hx.1
  have hWS : localZSpan R a c ≤ stabilizer R c :=
    (localZSpan_le_Q R hc hd.le (by omega : 2 < geometry.b R)).trans hQS
  exact hn ((commutator_mono (Z_le_localZSpan R a c) le_rfl).trans
    ((quotient_commutator_eq_bot_iff c _ _ hWS hQS).mp hW))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase
