module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.Center
public import Theory.GroupTheory.PGroup.AnisotropicFactors

/-!
# The two anisotropic factors of the source root product

Outside their common four-group, every element of the first factor squares
to z and every element of the second squares to u. Thus the two factors
supply anisotropic binary planes with distinct square values in R/E.
The first plane has no additional centralizer, even in the ambient group.
These are intrinsic inputs to recognizing the multiplication of R; no root
coordinates or normalizer action are assumed here.

The proof transports the involution-centralizer calculation in the genuine
minus-extraspecial core to each of the two literal core intersections.
The common core calculations are adapted from the J₂ `SourceFrame`
implementation; reciprocity here uses only H-type, not its two-class census.
Source: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.2–46.3 and the proof
of 46.14, printed pp.29–30,251,257–258.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.Geometry.Coordinates

variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

private noncomputable def coreEquiv : ambientCore D.z ≃* MinusExtraspecial.Model :=
  ((localCore D.z).equivMapOfInjective (involutionCentralizer D.z).subtype
    (involutionCentralizer D.z).subtype_injective).symm.trans D.localType.core_equiv.some

private noncomputable def conjugateCoreEquiv : P.conjugateCore ≃* MinusExtraspecial.Model :=
  ((ambientCore D.z).equivMapOfInjective (MulAut.conj P.g).toMonoidHom
    (MulAut.conj P.g).injective).symm.trans coreEquiv

private theorem z_center :
    (⟨D.z, HTypeAt.involution_mem_core⟩ : ambientCore D.z) ∈ center (ambientCore D.z) := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (ambientCore_le D.z x.property))

private theorem u_center :
    (⟨P.u, P.u_mem_conjugateCore⟩ : P.conjugateCore) ∈ center P.conjugateCore := by
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (P.conjugateCore_le x.property))

private theorem z_ne_one : D.z ≠ 1 := by
  intro h
  have hz := D.localType.involution
  simp [h] at hz

private theorem u_ne_one : P.u ≠ 1 := by
  intro h
  have hu := P.u_order
  simp [h] at hu

/-- The marked center has exponent two, in the actual ambient group. -/
theorem E_square_eq_one {x : G} (hx : x ∈ P.E) : x ^ 2 = 1 := by
  let := P.E_elementary
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 P.E) (⟨x, hx⟩ : P.E)
  exact congrArg Subtype.val h

/-- The square-one locus of the first factor is exactly E. -/
theorem leftCore_square_eq_one_iff {x : G} (hx : x ∈ P.leftCore) :
    x ^ 2 = 1 ↔ x ∈ P.E := by
  constructor
  · intro hs
    have h := MinusExtraspecial.commuting_square_one_of_equiv coreEquiv z_center
      (by exact fun h => z_ne_one (congrArg Subtype.val h))
      (u := (⟨P.u, P.mem_core⟩ : ambientCore D.z))
      (x := (⟨x, hx.1⟩ : ambientCore D.z))
      (Subtype.ext (P.u_order ▸ pow_orderOf_eq_one P.u))
      (by exact fun h => u_ne_one P (congrArg Subtype.val h))
      (by exact fun h => P.ne (congrArg Subtype.val h))
      (Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)) (Subtype.ext hs)
    rcases h with h | h | h | h
    · simpa only [show x = 1 from congrArg Subtype.val h] using P.E.one_mem
    · simpa only [show x = D.z from congrArg Subtype.val h] using P.z_mem_E
    · simpa only [show x = P.u from congrArg Subtype.val h] using P.u_mem_E
    · simpa only [show x = D.z * P.u from congrArg Subtype.val h] using
        P.E.mul_mem P.z_mem_E P.u_mem_E
  · exact E_square_eq_one P

/-- The square-one locus of the returning factor is also exactly E. -/
theorem rightCore_square_eq_one_iff {x : G} (hx : x ∈ P.rightCore) :
    x ^ 2 = 1 ↔ x ∈ P.E := by
  constructor
  · intro hs
    have h := MinusExtraspecial.commuting_square_one_of_equiv (conjugateCoreEquiv P)
      (u_center P) (by exact fun h => u_ne_one P (congrArg Subtype.val h))
      (u := (⟨D.z, P.z_mem_conjugateCore ⟩ : P.conjugateCore))
      (x := (⟨x, hx.1⟩ : P.conjugateCore))
      (Subtype.ext (D.localType.involution ▸ pow_orderOf_eq_one D.z))
      (by exact fun h => z_ne_one (congrArg Subtype.val h))
      (by exact fun h => P.ne (congrArg Subtype.val h).symm)
      (Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)) (Subtype.ext hs)
    rcases h with h | h | h | h
    · simpa only [show x = 1 from congrArg Subtype.val h] using P.E.one_mem
    · simpa only [show x = P.u from congrArg Subtype.val h] using P.u_mem_E
    · simpa only [show x = D.z from congrArg Subtype.val h] using P.z_mem_E
    · simpa only [show x = P.u * D.z from congrArg Subtype.val h] using
        P.E.mul_mem P.u_mem_E P.z_mem_E
  · exact E_square_eq_one P

/-- Every noncentral element of the first factor has the same nontrivial square. -/
theorem leftCore_square_of_not_mem_E {x : G} (hx : x ∈ P.leftCore) (he : x ∉ P.E) :
    x ^ 2 = D.z := by
  have h := MinusExtraspecial.square_eq_one_or_of_equiv coreEquiv z_center
    (by exact fun h => z_ne_one (congrArg Subtype.val h)) (⟨x, hx.1⟩ : ambientCore D.z)
  rcases h with h | h
  · exact False.elim (he ((leftCore_square_eq_one_iff P hx).mp (congrArg Subtype.val h)))
  · exact congrArg Subtype.val h

/-- The second anisotropic plane has the other marked nontrivial square. -/
theorem rightCore_square_of_not_mem_E {x : G}
    (hx : x ∈ P.rightCore) (he : x ∉ P.E) : x ^ 2 = P.u := by
  have h := MinusExtraspecial.square_eq_one_or_of_equiv (conjugateCoreEquiv P) (u_center P)
    (by exact fun h => u_ne_one P (congrArg Subtype.val h)) (⟨x, hx.1⟩ : P.conjugateCore)
  rcases h with h | h
  · exact False.elim (he ((rightCore_square_eq_one_iff P  hx).mp (congrArg Subtype.val h)))
  · exact congrArg Subtype.val h

/-- Literal identification of the intrinsic marked center, before recognition. -/
theorem E_subgroupOf_eq_center : P.E.subgroupOf P.R = center P.R := by
  apply Subgroup.map_injective P.R.subtype_injective
  rw [map_subgroupOf_eq_of_le P.E_le_R, E_center P]

/-- The centralizer condition on the first anisotropic plane inside R. -/
theorem centralizer_leftFactor :
    centralizer (P.leftCore.subgroupOf P.R : Set P.R) = P.E.subgroupOf P.R := by
  ext x
  constructor
  · intro hx
    apply (centralizer_leftCore_eq_E P).le
    intro y hy
    exact congrArg Subtype.val (hx (⟨y, (le_sup_left : P.leftCore ≤ P.R) hy⟩ : P.R) hy)
  · intro hx y _
    exact (mem_center_iff.mp (P.E_subgroupOf_le_center hx) y)

/-- The two marked involutions, viewed in the intrinsic center of R. -/
def zRoot : center P.R :=
  ⟨⟨D.z, P.E_le_R P.z_mem_E⟩, P.E_subgroupOf_le_center P.z_mem_E⟩

def uRoot : center P.R :=
  ⟨⟨P.u, P.E_le_R P.u_mem_E⟩, P.E_subgroupOf_le_center P.u_mem_E⟩

/-- All factor and square hypotheses for intrinsic multiplication recognition
are supplied by the literal source cores. The action on the center remains
an independent source obligation. -/
noncomputable def rootFactors : AnisotropicFactors P.R where
  card := P.R_card
  center_card := by
    rw [← E_subgroupOf_eq_center P]
    exact (Nat.card_congr (subgroupOfEquivOfLe P.E_le_R).toEquiv).trans P.E_card
  center_elementary := by
    rw [← E_subgroupOf_eq_center P]
    let := P.E_elementary
    exact IsElementaryAbelian.subgroupOf P.E_le_R
  square_central x := P.E_subgroupOf_le_center (P.R_square_mem_E  x.property)
  A := P.leftCore.subgroupOf P.R
  B := P.rightCore.subgroupOf P.R
  A_card := (Nat.card_congr
    (subgroupOfEquivOfLe (le_sup_left : P.leftCore ≤ P.R)).toEquiv).trans P.leftCore_card
  B_card := (Nat.card_congr
    (subgroupOfEquivOfLe (le_sup_right : P.rightCore ≤ P.R)).toEquiv).trans (P.rightCore_card )
  inf_eq := by
    rw [← E_subgroupOf_eq_center P]
    change (P.leftCore ⊓ P.rightCore).comap P.R.subtype = P.E.comap P.R.subtype
    rw [P.leftCore_inf_rightCore ]
  sup_eq := by
    exact (subgroupOf_sup (B := P.R) (show P.leftCore ≤ P.R from le_sup_left)
      (show P.rightCore ≤ P.R from le_sup_right)).symm.trans (subgroupOf_self P.R)
  z := zRoot P
  u := uRoot P
  z_ne_one := by
    intro h
    have he : D.z = 1 := congrArg (fun x : center P.R => ((x : P.R) : G)) h
    have ho := D.localType.involution
    simp [he] at ho
  u_ne_one := by
    intro h
    have he : P.u = 1 := congrArg (fun x : center P.R => ((x : P.R) : G)) h
    have ho := P.u_order
    simp [he] at ho
  distinct := fun h => P.ne
    (congrArg (fun x : center P.R => ((x : P.R) : G)) h).symm
  A_square x hx he := Subtype.ext (leftCore_square_of_not_mem_E P hx
    (fun h => he (P.E_subgroupOf_le_center h)))
  B_square x hx he := Subtype.ext (rightCore_square_of_not_mem_E P  hx
    (fun h => he (P.E_subgroupOf_le_center h)))
  centralizer_A := (centralizer_leftFactor P).trans (E_subgroupOf_eq_center P)

/-- Conjugate central elements have equally many square roots in the literal R. -/
theorem squareFiber_card_eq_of_conjugate (a : normalizer (P.R : Set G))
    (c d : P.R) (h : (a : G) * (c : G) * (a : G)⁻¹ = (d : G)) :
    Nat.card {x : P.R // x ^ 2 = c} = Nat.card {x : P.R // x ^ 2 = d} := by
  have he : P.R.normalizerMonoidHom a c = d := Subtype.ext h
  simpa only [he] using squareFiber_card_eq (P.R.normalizerMonoidHom a) c

/-- The exact source action input required by the multiplication recognition
route: ambient normalizer elements fuse all nonidentity elements of E. -/
def CenterTransitive : Prop :=
  ∀ e ∈ P.E, e ≠ 1 → ∀ f ∈ P.E, f ≠ 1 →
    ∃ a : normalizer (P.R : Set G), (a : G) * e * (a : G)⁻¹ = f

/-- The literal ambient action supplies automorphisms of the intrinsic root
center, with no choice of model coordinates. -/
theorem center_transitive_intrinsic (h : CenterTransitive P) :
    ∀ c d : center P.R, c ≠ 1 → d ≠ 1 →
      ∃ a : MulAut P.R, a (c : P.R) = (d : P.R) := by
  intro c d hc hd
  have hcE : ((c : P.R) : G) ∈ P.E := (E_center P) ▸ mem_map_of_mem P.R.subtype c.property
  have hdE : ((d : P.R) : G) ∈ P.E := (E_center P) ▸ mem_map_of_mem P.R.subtype d.property
  have hc1 : ((c : P.R) : G) ≠ 1 := fun he => hc (Subtype.ext (Subtype.ext he))
  have hd1 : ((d : P.R) : G) ≠ 1 := fun he => hd (Subtype.ext (Subtype.ext he))
  obtain ⟨a, ha⟩ := h _ hcE hc1 _ hdE hd1
  exact ⟨P.R.normalizerMonoidHom a, Subtype.ext ha⟩

/-- Applying the source action to square fibers provides the remaining
numerical restriction on the intrinsic quadratic map. This is conditional
until `CenterTransitive` is proved from the two cores. -/
theorem squareFibers_balanced (h : CenterTransitive P)
    (c d : center P.R) (hc : c ≠ 1) (hd : d ≠ 1) :
    Nat.card {x : P.R // x ^ 2 = (c : P.R)} =
      Nat.card {x : P.R // x ^ 2 = (d : P.R)} :=
  squareFiber_card_eq_of_center_transitive (center_transitive_intrinsic P h) c d hc hd

end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.Geometry.Coordinates
