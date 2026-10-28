module

public import CFSG.Quasithin.Chapter16.Section04To05.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.Fusion
public import CFSG.Quasithin.Chapter16.Section04To05.Terminal
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Models
public import Theory.GroupAction.OddFourGroupLine
public import Theory.PGroupCore
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.GroupTheory.Frattini
public import Theory.ElementaryAbelian.Basic

/-!
# Covering data and characteristic transport for the central sporadic branch

The marked setup retains the genuine Δ₀ Sylow condition and the factorization
u = cv with c in C_G(L) and v in L. The tested projection is in L/Z(L).
The common subgroup X is the two-residual of C_L(u), whereas the square roots
and the Rudvalis construction use the two-core of X.

For Rudvalis we construct Y₁ = C_{O₂(X)}(Φ(O₂(X))) and Y = [Y₁,Y₁],
and prove characteristic transport through each inclusion. For the other
covers we retain the unique-square condition as a set condition. A normalized
coset has its unique square fixed, so fixing z forces u to be fixed as well;
the square is never identified with u.

`CoverRestrictions`, `QuotientGeometry` and `LocalCoverData` specify remaining
outputs, not proved source assertions. Their construction from the sporadic
models and the exact earlier source inputs remains a separate obligation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.5.11, printed p.1199; I.2.2(5c),(6b),(7c), pp.409–410. Conjugation is left
conjugation, so the printed exponent g corresponds to our g⁻¹.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.CentralCovers
variable {G : Type*} [Group G]

/-- The image of the genuine two-residual of the relative centralizer C_L(u). -/
def involutionResidual (L : Subgroup G) (u : G) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer ({u} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({u} : Set G)).subtype

/-- The quotient projection belongs to the center of some Sylow two-subgroup. -/
def QuotientTwoCentral (L : Subgroup G) (v : L) : Prop :=
  let q := QuotientGroup.mk' (center L) v
  orderOf q = 2 ∧ ∃ S : Sylow 2 (L ⧸ center L),
    q ∈ S ∧ (S : Subgroup (L ⧸ center L)) ≤ centralizer ({q} : Set (L ⧸ center L))

/-- A marked member of Δ₀, with the actual factorization u = cv. The
projection is an element of L, and its image is tested in L/Z(L). -/
structure MarkedDeltaZero [Finite G] (T : Sylow 2 G) (z : G)
    (L : Subgroup G) (g : G) (R : Subgroup G) (u c v : G) : Prop
    extends IntersectionSetup T z L g R where
  omega_inner : omegaOneAmbient R ≤ centralizer (L : Set G) ⊔ L
  u_mem : u ∈ R
  u_order : orderOf u = 2
  c_mem : c ∈ centralizer (L : Set G)
  v_mem : v ∈ L
  projection : u = c * v

/-- Earlier §16.4 and §16.5 outputs used by the common obstruction. Their
source proofs are separate; none of the central-cover conclusions is a field. -/
structure EarlierInputs [Finite G] (T : Sylow 2 G) (L : Subgroup G)
    (g : G) (R : Subgroup G) (u : G) : Prop where
  faithful : Disjoint R (centralizer (L : Set G))
  sylow_conjugate : SylowIn R ((centralizer (L : Set G)).conjBy g)
  transport : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
    (T : Subgroup G).conjBy g
  normalizes_residual : g ∈ normalizer (involutionResidual L u : Set G)

/-- Required output of the covering reduction, not an asserted classification.
Every name is attached to an isomorphism of the actual quotient, and the
exceptional order-four R case is attached to the HS quotient. -/
structure CoverRestrictions (T : Sylow 2 G) (z : G) (L R : Subgroup G) (u : G) : Prop where
  model : ∃ name : ClassificationModels.SporadicName,
    (name = .m12 ∨ name = .m22 ∨ name = .j2 ∨ name = .hs ∨ name = .ru) ∧
      Nonempty ((L ⧸ center L) ≃* name.Carrier)
  r_shape : Nonempty (R ≃* Multiplicative (ZMod 2)) ∨
    (Nonempty ((L ⧸ center L) ≃* ClassificationModels.SporadicName.hs.Carrier) ∧
      Nonempty (R ≃* Multiplicative (ZMod 4)))
  omega_r : omegaOneAmbient R = zpowers u
  omega_commuting : omegaOneAmbient (commutingSylow T L) = zpowers z
  center_eq : (center L).map L.subtype = zpowers z
  center_card : Nat.card (center L) = 2

/-- The actual omega subgroup of the Sylow center, viewed in G. -/
def sylowOmegaCenter (T : Sylow 2 G) : Subgroup G :=
  ((omega₁ (center (T : Subgroup G)) (p := 2)).map
    (center (T : Subgroup G)).subtype).map (T : Subgroup G).subtype

/-- Required quotient calculation before applying the local covering data.
These conclusions remain separate obligations of the source assembly. -/
structure QuotientGeometry (T : Sylow 2 G) (L : Subgroup G) (u z : G) : Prop where
  u_mem_component : u ∈ L
  coset_fixed : ∀ t ∈ T, MulAut.conj t u = u ∨ MulAut.conj t u = u * z
  omega_center_bound : Nat.card (sylowOmegaCenter T) ≤ 4

instance sylowOmegaCenter_elementary (T : Sylow 2 G) :
    IsElementaryAbelian 2 (sylowOmegaCenter T) := by
  let := IsElementaryAbelian.omega₁_of_isMulCommutative (p := 2)
    (center (T : Subgroup G))
  let := IsElementaryAbelian.map (p := 2) (A := omega₁ (center (T : Subgroup G)) (p := 2))
    (center (T : Subgroup G)).subtype
  exact IsElementaryAbelian.map (T : Subgroup G).subtype

theorem normalizer_sylow_le_normalizer_omegaCenter (T : Sylow 2 G) :
    normalizer (T : Set G) ≤ normalizer (sylowOmegaCenter T : Set G) := by
  let := omega₁_characteristic (center (T : Subgroup G)) (p := 2)
  exact normalizer_le_normalizer_characteristic_image (T : Subgroup G) _

theorem sylow_centralizes_omegaCenter (T : Sylow 2 G) :
    (T : Subgroup G) ≤ centralizer (sylowOmegaCenter T : Set G) := by
  intro t ht
  rw [mem_centralizer_iff]
  rintro x ⟨y, ⟨w, hw, rfl⟩, rfl⟩
  exact congrArg Subtype.val ((mem_center_iff.mp w.property) ⟨t, ht⟩).symm

theorem mem_sylowOmegaCenter (T : Sylow 2 G) {x : G}
    (hxT : x ∈ T) (hx2 : x ^ 2 = 1)
    (hxC : x ∈ centralizer (T : Set G)) : x ∈ sylowOmegaCenter T := by
  have hxZ : (⟨x, hxT⟩ : (T : Subgroup G)) ∈ center (T : Subgroup G) := by
    rw [mem_center_iff]
    intro t
    apply Subtype.ext
    exact mem_centralizer_iff.mp hxC t t.property
  refine ⟨⟨x, hxT⟩, ⟨⟨⟨x, hxT⟩, hxZ⟩, ?_, rfl⟩, rfl⟩
  apply Subgroup.subset_closure
  change (⟨⟨x, hxT⟩, hxZ⟩ : center (T : Subgroup G)) ^ (2 ^ 1) = 1
  apply Subtype.ext
  apply Subtype.ext
  change x ^ (2 ^ 1) = 1
  simpa only [pow_one] using hx2

/-- The relative centralizer inside the two-core, before mapping into X. -/
def rudvalisYOne (X : Subgroup G) : Subgroup (pCore 2 X) :=
  centralizer (frattini (pCore 2 X) : Set (pCore 2 X))

/-- [Y₁,Y₁], with both commutators formed in the genuine two-core. -/
def rudvalisY (X : Subgroup G) : Subgroup X :=
  (⁅rudvalisYOne X, rudvalisYOne X⁆).map (pCore 2 X).subtype

instance rudvalisYOne_characteristic (X : Subgroup G) :
    (rudvalisYOne X).Characteristic := by
  unfold rudvalisYOne
  infer_instance

instance rudvalisY_characteristic (X : Subgroup G) :
    (rudvalisY X).Characteristic := by
  unfold rudvalisY
  infer_instance

/-- The square set meets the two-element coset in exactly one point. -/
def UniqueSquareCoset (Q : Subgroup G) (u z : G) : Prop :=
  ∃! w : G, (w = u ∨ w = u * z) ∧ ∃ x ∈ Q, x ^ 2 = w

theorem square_mem_conj {Q : Subgroup G} {g w : G}
    (hg : g ∈ normalizer (Q : Set G)) (hw : ∃ x ∈ Q, x ^ 2 = w) :
    ∃ x ∈ Q, x ^ 2 = MulAut.conj g w := by
  obtain ⟨x, hx, he⟩ := hw
  exact ⟨MulAut.conj g x, (mem_normalizer_iff.mp hg x).mp hx,
    (map_pow (MulAut.conj g) x 2).symm.trans (congrArg (MulAut.conj g) he)⟩

/-- Uniqueness fixes the distinguished square; fixing z then fixes u as well.
No identification of that square with u is used. -/
theorem fixes_of_uniqueSquareCoset {Q : Subgroup G} {g u z : G}
    (hQ : g ∈ normalizer (Q : Set G)) (hz2 : z * z = 1)
    (hz : MulAut.conj g z = z)
    (hu : MulAut.conj g u = u ∨ MulAut.conj g u = u * z)
    (hsq : UniqueSquareCoset Q u z) : MulAut.conj g u = u := by
  obtain ⟨w, ⟨hwcoset, hwsquare⟩, hwuniq⟩ := hsq
  have hcoset : MulAut.conj g w = u ∨ MulAut.conj g w = u * z := by
    rcases hwcoset with rfl | rfl
    · exact hu
    · rw [map_mul, hz]
      rcases hu with he | he <;> rw [he]
      · exact Or.inr rfl
      · exact Or.inl (by rw [mul_assoc, hz2, mul_one])
  have hwfix := hwuniq (MulAut.conj g w) ⟨hcoset, square_mem_conj hQ hwsquare⟩
  rcases hwcoset with rfl | rfl
  · exact hwfix
  · rw [map_mul, hz] at hwfix
    exact mul_right_cancel hwfix

/-- An invariant characteristic subgroup of order two is centralized. -/
theorem centralizes_characteristic_two [Finite G]
    (X : Subgroup G) (Y : Subgroup X) [Y.Characteristic]
    (hY : Nat.card Y = 2) :
    normalizer (X : Set G) ≤ centralizer (Y.map X.subtype : Set G) := by
  intro g hg
  rw [mem_centralizer_iff]
  rintro x ⟨y, hy, rfl⟩
  let ha : MulAut X := X.normalizerMonoidHom ⟨g, hg⟩
  have haY : ha y ∈ Y := (characteristic_iff_le_comap.mp inferInstance ha) hy
  have hfix : ha y = y := by
    by_cases hy1 : y = 1
    · simp [hy1]
    · obtain ⟨a, ha1, hauniq⟩ := (Nat.card_eq_two_iff' (1 : Y)).mp hY
      have hy1' : (⟨y, hy⟩ : Y) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
      have hay1 : (⟨ha y, haY⟩ : Y) ≠ 1 := by
        intro h
        exact hy1 (ha.injective ((congrArg Subtype.val h).trans (map_one ha).symm))
      exact congrArg Subtype.val ((hauniq _ hay1).trans (hauniq _ hy1').symm)
  have he : g * (y : G) * g⁻¹ = y := congrArg Subtype.val hfix
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The actual core is preserved by every normalizer of X. -/
theorem normalizer_le_normalizer_twoCore (X : Subgroup G) :
    normalizer (X : Set G) ≤
      normalizer ((pCore 2 X).map X.subtype : Set G) :=
  normalizer_le_normalizer_characteristic_image X (pCore 2 X)

/-- A central two-element coset fixed in the quotient makes the actual
relative centralizer, and therefore its two-residual, T-invariant. -/
theorem normalizes_involutionResidual (T : Subgroup G) (L : Subgroup G) (u z : G)
    (hTL : T ≤ normalizer (L : Set G))
    (hzL : z ∈ centralizer (L : Set G))
    (hcoset : ∀ t ∈ T, MulAut.conj t u = u ∨ MulAut.conj t u = u * z) :
    T ≤ normalizer (involutionResidual L u : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (L ⊓ centralizer ({u} : Set G)) (pResidual 2 _))
  apply le_normalizer_iff.mpr
  intro t ht x hx
  refine ⟨(mem_normalizer_iff.mp (hTL ht) x).mp hx.1, ?_⟩
  have hcom : MulAut.conj t x * MulAut.conj t u =
      MulAut.conj t u * MulAut.conj t x := by
    simpa only [map_mul] using congrArg (MulAut.conj t)
      (mem_centralizer_singleton_iff.mp hx.2)
  change MulAut.conj t x ∈ centralizer ({u} : Set G)
  rw [mem_centralizer_singleton_iff]
  rcases hcoset t ht with he | he
  · rwa [he] at hcom
  · rw [he] at hcom
    have hzcom : z * MulAut.conj t x = MulAut.conj t x * z :=
      (mem_centralizer_iff.mp hzL _ ((mem_normalizer_iff.mp (hTL ht) x).mp hx.1)).symm
    apply mul_right_cancel (b := z)
    calc
      (MulAut.conj t x * u) * z = MulAut.conj t x * (u * z) := mul_assoc _ _ _
      _ = (u * z) * MulAut.conj t x := hcom
      _ = u * (z * MulAut.conj t x) := mul_assoc _ _ _
      _ = u * (MulAut.conj t x * z) := by rw [hzcom]
      _ = (u * MulAut.conj t x) * z := (mul_assoc _ _ _).symm

/-- The two intrinsic covering outputs, kept separate from their construction.
The second clause is the ambient version of ZY = Z<u>, not an unspecified line. -/
def LocalCoverData (X : Subgroup G) (u z : G) : Prop :=
  UniqueSquareCoset ((pCore 2 X).map X.subtype) u z ∨
    (Nat.card (rudvalisY X) = 2 ∧
      zpowers z ⊔ (rudvalisY X).map X.subtype = zpowers z ⊔ zpowers u)

/-- Both covering outputs force u into the actual Sylow center. -/
theorem centralizes_of_localCoverData [Finite G]
    (T X : Subgroup G) (u z : G)
    (hTX : T ≤ normalizer (X : Set G))
    (hz2 : z * z = 1) (hzC : z ∈ centralizer (T : Set G))
    (hcoset : ∀ t ∈ T, MulAut.conj t u = u ∨ MulAut.conj t u = u * z)
    (hdata : LocalCoverData X u z) : u ∈ centralizer (T : Set G) := by
  rcases hdata with hsq | ⟨hY, hspan⟩
  · rw [mem_centralizer_iff]
    intro t ht
    have hzfix : MulAut.conj t z = z :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hzC t ht)
    have hfix := fixes_of_uniqueSquareCoset (normalizer_le_normalizer_twoCore X (hTX ht))
      hz2 hzfix (hcoset t ht) hsq
    exact mul_inv_eq_iff_eq_mul.mp hfix
  · have hYC : (rudvalisY X).map X.subtype ≤ centralizer (T : Set G) := by
      intro y hy
      rw [mem_centralizer_iff]
      intro t ht
      exact (mem_centralizer_iff.mp
        (centralizes_characteristic_two X (rudvalisY X) hY (hTX ht)) y hy).symm
    have hspanC : zpowers z ⊔ zpowers u ≤ centralizer (T : Set G) := by
      rw [← hspan]
      exact sup_le (zpowers_le.mpr hzC) hYC
    exact hspanC (mem_sup_right (mem_zpowers u))

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.CentralCovers
