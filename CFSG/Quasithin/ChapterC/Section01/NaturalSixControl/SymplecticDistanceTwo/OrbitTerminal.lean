module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitMovement
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitChoice
public import Theory.ElementaryAbelian.Join

/-!
# The paired-orbit contradiction at critical distance two

The fixed-kernel preimage is central in the actual orbit group. Its containment
in the paired commutator times Z-alpha makes it elementary, since the selected
orbits have elementary intersection. A transitive nonzero-vector action on the
fixed quotient then forces the entire orbit group to be elementary. This
contradicts the already proved movement of its generating plane.

The two representation-theoretic inputs remain explicit: the transitive fixed
quotient section and the fixed-kernel displacement bound. They are the outputs
of the natural-section and augmentation-cover recognition of the literal orbit
action, not an assumption that the orbit group itself is elementary.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

theorem orbitFixedKernel_elementary_of_paired_bound
    (hb : s.geometry.b R = 2) {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R))
    (B : Subgroup (FreeAmalgam R)) (hBQ : B ≤ Q R c)
    (hnB : stabilizer R c ≤ normalizer (B : Set (FreeAmalgam R)))
    (helem : IsElementaryAbelian 2 (criticalOrbit R c b ⊓ B : Subgroup (FreeAmalgam R)))
    (hD : (orbitFixedKernel L R c b).map (embedM R) ≤
      ⁅criticalOrbit R c b,B⁆ ⊔ Z R (alpha R)) :
    IsElementaryAbelian 2 (orbitFixedKernel L R c b) := by
  let A := criticalOrbit R c b
  have hAQ : A ≤ Q R (alpha R) := (s.criticalOrbit_le_Q_iff hb hc b).mpr
    (s.criticalPlane_le_Q_of_core_ne hb hc hab hcb hne)
  have hBA : B ≤ normalizer (A : Set (FreeAmalgam R)) :=
    (hBQ.trans ((Q_le_adjacent_h R (DistanceTwo.NaturalCore.edge_color hab) hcb).trans
      (fun _ hx => hx.2 _ (adjacent_symm R hab)))).trans (criticalOrbit_normalized c b)
  have hAB : A ≤ normalizer (B : Set (FreeAmalgam R)) :=
    (hAQ.trans (DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer hab hcb)).trans hnB
  have hcomm : ⁅A,B⁆ ≤ A ⊓ B := le_inf
    (le_normalizer_iff_commutator_le_left.mp hBA)
    (le_normalizer_iff_commutator_le_right.mp hAB)
  let := helem
  let : IsElementaryAbelian 2 (⁅A,B⁆ : Subgroup (FreeAmalgam R)) := IsElementaryAbelian.of_le hcomm
  let := s.Z_elementary
  have hZC : Z R (alpha R) ≤ centralizer ((⁅A,B⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)).trans
      (centralizer_le (hcomm.trans inf_le_left |>.trans hAQ))
  let : IsElementaryAbelian 2 (⁅A,B⁆ ⊔ Z R (alpha R) : Subgroup (FreeAmalgam R)) :=
    IsElementaryAbelian.sup_of_le_centralizer hZC
  let : IsElementaryAbelian 2 ((orbitFixedKernel L R c b).map (embedM R)) :=
    IsElementaryAbelian.of_le hD
  let e := (orbitFixedKernel L R c b).equivMapOfInjective (embedM R) (embedM_injective R)
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

/-- The actual paired-orbit section contradiction. Only the transitive quotient
and its fixed-kernel displacement bound remain for the natural-cover producer. -/
theorem false_of_criticalOrbit_paired_section
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (himage : criticalOrbit R c b ⊔ Q R c = Q R b)
    (B : Subgroup (FreeAmalgam R)) (hBQ : B ≤ Q R c)
    (hnB : stabilizer R c ≤ normalizer (B : Set (FreeAmalgam R)))
    (helem : IsElementaryAbelian 2 (criticalOrbit R c b ⊓ B : Subgroup (FreeAmalgam R)))
    (hD : (orbitFixedKernel L R c b).map (embedM R) ≤
      ⁅criticalOrbit R c b,B⁆ ⊔ Z R (alpha R))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (⊤ : Subgroup M) V}
    (d : Representation.BinaryConjugationSection ⊤ (criticalOrbitNative R c b)
      (orbitFixedKernel L R c b) ρ)
    (htrans : ∀ u v : V, u ≠ 0 → v ≠ 0 → ∃ m : (⊤ : Subgroup M), ρ m u = v) : False := by
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hlarge
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  have hcent := s.orbitFixedKernel_centralizes_of_full_image h t hfull hb hlarge hc hab hcb himage
  have hkernel := s.orbitFixedKernel_elementary_of_paired_bound hb hc hab hcb hne B hBQ hnB helem hD
  have hseed := s.criticalPlane_not_le_orbitFixedKernel h t hfull hb hlarge hc hab hcb
  exact s.criticalOrbit_plane_commutator_ne_bot_of_full_image h t hfull hb hlarge hc hab hcb himage
    (s.criticalOrbit_commutator_plane_eq_bot_of_fixed_section hb hc d hcent hkernel hseed htrans)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
