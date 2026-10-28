module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitIndex
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitChoice
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.RadiusImages
public import Theory.Representation.AlternatingSixStrictOffender

/-!
# Full edge images of the ordered critical orbits

The genuine opposite orbit acts as an elementary subgroup of the edge image.
Faithfulness and the strict fixed-index inequality force order eight and fixed
codimension two. Equality of relative indices then fills both edge quotients.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), p.871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

private theorem sup_eq_of_relIndex_eq {G : Type*} [Group G]
    (A N P : Subgroup G) (hAP : A ≤ P) (hNP : N ≤ P)
    (hn : P ≤ normalizer (N : Set G))
    (hindex : N.relIndex A = N.relIndex P) (hne : N.relIndex P ≠ 0) : A ⊔ N = P := by
  let C := N.subgroupOf P
  let D := A.subgroupOf P
  let : C.Normal := normal_subgroupOf_of_le_normalizer hn
  have hrel : C.relIndex D = N.relIndex P :=
    (relIndex_subgroupOf hAP).trans hindex
  have hi : C.relIndex (D ⊔ C) = N.relIndex P := by
    rw [relIndex_sup_right]
    exact hrel
  have hmul := relIndex_mul_index (show C ≤ D ⊔ C from le_sup_right)
  rw [hi] at hmul
  have htop : D ⊔ C = ⊤ := index_eq_one.mp (by
    change N.relIndex P * (D ⊔ C).index = N.relIndex P at hmul
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (by simpa using hmul))
  have hm := congrArg (Subgroup.map P.subtype) htop
  simpa only [Subgroup.map_sup,D,C,map_subgroupOf_eq_of_le hAP,
    map_subgroupOf_eq_of_le hNP,←MonoidHom.range_eq_map,range_subtype] using hm

variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem criticalOrbit_images_full (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (B : Subgroup (FreeAmalgam R)) (hBQ : B ≤ Q R c)
    (hcommB : ⁅Q R c,B⁆ ≤ Z R b)
    (hcomp : (Q R c).relIndex (criticalOrbit R c b) ≤ (Q R (alpha R)).relIndex B) :
    B ⊔ Q R (alpha R) = Q R b ∧
      criticalOrbit R c b ⊔ Q R c = Q R b ∧
      (commutatorPreimage (criticalOrbit R c b) B (Z R (alpha R))).relIndex
        (criticalOrbit R c b) = 4 := by
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hlarge
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  let := s.orbitQuotient_elementary hb hc hab hcb hne
  have hsurj : Function.Surjective s.projection :=
    s.projection_surjective_of_radical_image_le_conjugate t (by
      simpa only [Model.pointCore_eq_exceptional] using hfull.le)
  let ρ := s.orbitFullRepresentation hb hc hab hcb hsurj
  let E := s.orbitActorImage B
  have hbcol := DistanceTwo.NaturalCore.edge_color hab
  have hQab : Q R (alpha R) ≤ Q R b := Q_le_adjacent_h R hbcol hab
  have hQcb : Q R c ≤ Q R b := Q_le_adjacent_h R hbcol hcb
  have hBG : B ≤ stabilizer R (alpha R) :=
    (hBQ.trans hQcb).trans (fun _ hx => hx.2 _ (adjacent_symm R hab))
  have hBE : E ≤ s.orbitActorImage (Q R b) := map_mono (comap_mono (hBQ.trans hQcb))
  let := s.orbit_edge_image_elementary t hfull hab
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le hBE
  have hsmall : Nat.card E ≤ 8 := by
    have hi := Nat.card_le_card_of_injective (inclusion hBE) (inclusion_injective hBE)
    rwa [s.orbit_edge_image_card t hfull hab] at hi
  have hfixed := s.criticalOrbit_fixed_index_mul_two_le h t hfull hb hlarge hc hab hcb B hBQ hcommB
  have hstrict : 2 * 2 ^ fixedCodim ρ E ≤ Nat.card E := by
    have hi := hfixed.trans hcomp
    rw [s.orbit_fixed_index hb hc hab hcb hsurj B hBG,←s.orbitActorImage_card B hBG] at hi
    exact hi
  obtain ⟨hE,hcodim⟩ := AlternatingSixInvolutionDisplacement.strict_small_elementary_card ρ
    (s.orbitFullRepresentation_injective hb hc hab hcb hsurj h t hfull hlarge) E hsmall hstrict
  have hfour : (commutatorPreimage (criticalOrbit R c b) B (Z R (alpha R))).relIndex
      (criticalOrbit R c b) = 4 := by
    rw [s.orbit_fixed_index hb hc hab hcb hsurj B hBG]
    change 2 ^ fixedCodim ρ E = 4
    rw [hcodim]
    norm_num
  have hB8 : (Q R (alpha R)).relIndex B = 8 :=
    (s.orbitActorImage_card B hBG).symm.trans hE
  have hA8 : (Q R c).relIndex (criticalOrbit R c b) = 8 := by
    rw [hfour] at hfixed
    rw [hB8] at hcomp
    omega
  have hedge8 (a : Vertex R) (ha : color R a = false) (hae : Adjacent R a b) :
      (Q R a).relIndex (Q R b) = 8 := by
    rw [s.edge_kernel_index a b ha hae,hfull,
      card_map_of_injective (MulAut.conj t).injective,pointCore_card]
  have hAQ : criticalOrbit R c b ≤ Q R (alpha R) :=
    (s.criticalOrbit_le_Q_iff hb hc b).mpr
      (s.criticalPlane_le_Q_of_core_ne hb hc hab hcb hne)
  refine ⟨?_,?_,hfour⟩
  · exact sup_eq_of_relIndex_eq B _ _ (hBQ.trans hQcb) hQab
      ((show Q R b ≤ stabilizer R (alpha R) from
        fun _ hx => hx.2 _ (adjacent_symm R hab)).trans (Q_normalized R (alpha R)))
      (hB8.trans (hedge8 (alpha R) rfl hab).symm) (by rw [hedge8 (alpha R) rfl hab];decide)
  · have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
    exact sup_eq_of_relIndex_eq _ _ _ (hAQ.trans hQab) hQcb
      ((show Q R b ≤ stabilizer R c from
        fun _ hx => hx.2 _ (adjacent_symm R hcb)).trans (Q_normalized R c))
      (hA8.trans (hedge8 c hc0 hcb).symm) (by rw [hedge8 c hc0 hcb];decide)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
