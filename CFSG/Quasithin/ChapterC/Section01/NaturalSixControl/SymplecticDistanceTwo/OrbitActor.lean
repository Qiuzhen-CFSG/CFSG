module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitOffender

/-!
# The literal critical-orbit actor is an odd strict offender

The source index comparison bounds the elementary actor by the edge group of
order eight. Faithful A6 displacement forces equality and fixed codimension two.
Equality with the conjugate edge image supplies an odd permutation, as required
by the B.5 natural-section selection.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Stellmacher.PushingUp.AmalgamGraph CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem orbitActorImage_offender (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    [IsElementaryAbelian 2 (OrbitQuotient R c b)]
    (hsurj : Function.Surjective s.projection)
    (B : Subgroup (FreeAmalgam R)) (hBQ : B ≤ Q R c)
    (hcommB : ⁅Q R c,B⁆ ≤ Z R b)
    (hcomp : (Q R c).relIndex (criticalOrbit R c b) ≤ (Q R (alpha R)).relIndex B) :
    IsElementaryAbelian 2 (s.orbitActorImage B) ∧ Nat.card (s.orbitActorImage B) = 8 ∧
      fixedCodim (s.orbitFullRepresentation hb hc hab hcb hsurj) (s.orbitActorImage B) = 2 ∧
      ¬ s.orbitActorImage B ≤ alternatingGroup (Fin 6) := by
  have hbcol := DistanceTwo.NaturalCore.edge_color hab
  have hBedge : B ≤ Q R b := hBQ.trans (Q_le_adjacent_h R hbcol hcb)
  have hBG : B ≤ stabilizer R (alpha R) :=
    hBedge.trans (fun _ hx => hx.2 _ (adjacent_symm R hab))
  have hBE : s.orbitActorImage B ≤ s.orbitActorImage (Q R b) :=
    map_mono (comap_mono hBedge)
  let := s.orbit_edge_image_elementary t hfull hab
  let : IsElementaryAbelian 2 (s.orbitActorImage B) := IsElementaryAbelian.of_le hBE
  have hsmall : Nat.card (s.orbitActorImage B) ≤ 8 := by
    have hh := Nat.card_le_card_of_injective (inclusion hBE) (inclusion_injective hBE)
    rwa [s.orbit_edge_image_card t hfull hab] at hh
  have hi := (s.criticalOrbit_fixed_index_mul_two_le h t hfull hb hlarge hc hab hcb B hBQ hcommB).trans hcomp
  rw [s.orbit_fixed_index hb hc hab hcb hsurj B hBG,←s.orbitActorImage_card B hBG] at hi
  obtain ⟨hcard,hcodim⟩ := AlternatingSixInvolutionDisplacement.strict_small_elementary_card _
    (s.orbitFullRepresentation_injective hb hc hab hcb hsurj h t hfull hlarge)
    (s.orbitActorImage B) hsmall hi
  refine ⟨inferInstance,hcard,hcodim,?_⟩
  have hE : s.orbitActorImage B = s.orbitActorImage (Q R b) :=
    eq_of_le_of_card_ge hBE (by rw [hcard,s.orbit_edge_image_card t hfull hab])
  rw [hE]
  obtain ⟨m,hm⟩ := s.orbit_edge_image_conjugate hab
  rw [hm,hfull]
  intro he
  have step (C : Subgroup S) (g : S)
      (hh : C.map (MulAut.conj g).toMonoidHom ≤ alternatingGroup (Fin 6)) :
      C ≤ alternatingGroup (Fin 6) := by
    exact (map_le_map_iff_of_injective
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mp
      (by simpa only [conjugate_alternating] using hh)
  have hp := step pointCore t (step _ _ he)
  have hswap : swap45 ∈ pointCore := by
    rw [pointCore_eq_closure]
    exact subset_closure (by simp)
  have hn : swap45 ∉ alternatingGroup (Fin 6) := by decide
  exact hn (hp hswap)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
