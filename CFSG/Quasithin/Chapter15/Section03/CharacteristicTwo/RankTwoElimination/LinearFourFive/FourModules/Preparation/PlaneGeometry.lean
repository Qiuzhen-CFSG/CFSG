module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.PlaneGeometry.Transport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.PlaneGeometry.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation.PlaneGeometry.Recognition

/-!
# The actual marked plane parabolic in 15.3.24

For every supplied isomorphism L/O₂(L) ≃ PSL₄(2), the solvable image of
Y₊(S ∩ L) contains a Sylow two-subgroup and has three-part nine. Bruhat
exhaustion and the endpoint block orders identify it with a maximal plane
stabilizer. Since L is outside M, lifting through the two-core gives
M ∩ L = Y₊(S ∩ L) and the literal plane preimage in L.

Relative normalization identifies R ∩ L with the two-core of that base
product. Its actual marked image is the plane's unipotent radical, and
the first-isomorphism map gives the required elementary section of order
sixteen. The denominator and representative formula are those of
`radical_denominator` and `coreSectionEquiv_apply` in `LocalSetup`.

The result uses only the stated earlier inputs and the supplied quotient
marking. It assumes neither plane recognition nor diagram innerness.
Source: Aschbacher–Smith, 15.3.24, first two paragraphs of the proof,
combined manuscript (1 March 2004), printed pp.1129–1130.
-/

public section

open Subgroup BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation

variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
variable {c : ComponentWitness d I}

/-- The marked plane and actual order-sixteen radical in the second paragraph
of 15.3.24, for any supplied component-quotient marking. -/
theorem nonempty_parabolicData (h : Earlier d c)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Projective 4) :
    Nonempty (ParabolicData d c.L e) := by
  let B := modelImage (by decide : 0 < 4) e (d.Yplus ⊔ (d.S ⊓ c.L))
  obtain ⟨P, hP⟩ := exists_model_sylow h (by decide : 0 < 4) e
  have hPB : (P : Subgroup (LinearGroup 4)) ≤ B := by
    rw [hP]
    exact map_mono (subgroupOf_mono _ le_sup_right)
  have hBsol : Group.IsSolvable B := baseImage_solvable h (Or.inl rfl) e
  have h3 : (Nat.card B).factorization 3 = 2 := baseImage_three_part h (Or.inl rfl) e
  let : Finite (LinearGroup 4) := Finite.of_injective
    (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective
  have h9 : 9 ∣ Nat.card B := by
    apply (Nat.prime_three.pow_dvd_iff_le_factorization (k := 2) Nat.card_pos.ne').mpr
    rw [h3]
  obtain ⟨W, hdim, hW, hmax⟩ := PlaneGeometry.solvable_sylow_overgroup_plane P B hPB hBsol h9
  have hj := intersection_join_of_coatom h (by decide) e (hW.symm ▸ hmax)
  obtain ⟨p⟩ := planeParabolic_of_base_image h e W hdim hW hmax
  have hp : modelImage (by decide) e (d.Yplus ⊔ (d.S ⊓ c.L)) =
      BinaryLinear.parabolic p.plane := by
    rw [← hj]
    exact planeParabolic_image p
  have hr := radical_image_of_base_image h e p.plane hp
  exact ⟨{
    marking := p
    intersection_join := hj
    radical_image := hr
    radical_coordinates := ((coreSectionEquiv (by decide) e (d.R ⊓ c.L)).trans
      (MulEquiv.subgroupCongr hr)).trans (PlaneGeometry.radicalCoordinates p.plane p.dimension)
  }⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Preparation
