module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.CommutatorRows
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center

public import Theory.SpecificGroups.PSL2.BinarySylowEmbedding
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import CFSG.Quasithin.ClassificationModels.Families


/-!
# Centralization in the classical and Bender component Sylows

The faithful moving sixteen is already placed in the canonical quotient
image of the original component Sylow. In PSL₃, a noncentral involution
has centralizer index equal to the field order. In Sp₄, either nonzero
outer root coordinate gives an injective field-sized family of centralizer
cosets. Thus an index at most two forces centralization in every nonbinary
linear or symplectic model. In Bender groups the elementary Sylow subgroups
already lie in the Sylow center.

The order sixteen then forces degree at least four for PSL₂, PSU₃ and
PSL₃, and excludes Sz(8). Each assertion retains the field parameter of
the supplied actual model. The symplectic statement makes no unsupported
claim that degree three is excluded. The chosen-module application is
NonFFSourceDoubledBinaryRootCentralization.
Source: Aschbacher–Smith, proof of 7.7.6, printed p.706,
refs/quasithin.pdf. Exceptional root groups, central-cover lifting and
ambient Cartan placement remain with qt-d-1222-nonff-doubled.
-/

public noncomputable section
open Subgroup
open BenderSuzuki.MatrixGroups.HermitianForm
open scoped IsMulCommutative
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryRootCentralization

private theorem index_comap_le {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (C : Subgroup Y) (f : X →* Y) : (C.comap f).index ≤ C.index := by
  rw [C.index_comap]
  exact (relIndex_le_of_le_right (H := C) (le_top : f.range ≤ ⊤)
    (by simpa using C.index_ne_zero_of_finite)).trans_eq C.relIndex_top_right

private theorem center_of_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (x : X) (hy : e x ∈ center Y) : x ∈ center X := by
  apply mem_center_iff.mpr
  intro y
  apply e.injective
  simpa only [map_mul] using mem_center_iff.mp hy (e y)

private theorem centralizer_comap_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (x : X) :
    (centralizer ({e x} : Set Y)).comap e.toMonoidHom = centralizer ({x} : Set X) := by
  ext y
  simp only [mem_comap, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← map_mul, e.injective.eq_iff]

/-- A Sylow coordinate calculation applies to an elementary subgroup in the
original Sylow, using the relative centralizer index in that Sylow. -/
private theorem centralizes_of_sylow_coordinates
    {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    (P : Subgroup G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAP : A ≤ P) (hi : ((centralizer (A : Set G)).subgroupOf P).index ≤ 2)
    (e : P ≃* X)
    (hX : ∀ x : X, x ^ 2 = 1 → (centralizer ({x} : Set X)).index ≤ 2 →
      x ∈ center X) : A ≤ (center P).map P.subtype := by
  intro a ha
  let x : P := ⟨a,hAP ha⟩
  have hx2 : x ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a ha)
  have hC : (centralizer ({x} : Set P)) = (centralizer ({a} : Set G)).subgroupOf P := by
    ext y
    simp only [mem_centralizer_singleton_iff, mem_subgroupOf, x]
    exact Subtype.ext_iff
  have hidx : (centralizer ({x} : Set P)).index ≤ 2 := by
    rw [hC]
    apply le_trans _ hi
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (index_ne_zero_of_finite))
      (index_dvd_of_le (comap_mono (centralizer_le (Set.singleton_subset_iff.mpr ha))))
  have heidx : (centralizer ({e x} : Set X)).index ≤ 2 := by
    rw [← (centralizer ({e x} : Set X)).index_comap_of_surjective (f := e.toMonoidHom) e.surjective,
      centralizer_comap_equiv]
    exact hidx
  exact ⟨x,center_of_equiv e x (hX (e x) (by rw [←map_pow,hx2,map_one]) heidx),rfl⟩

private theorem linear_coordinate_central {F : Type*} [Finite F] [Field F] [CharP F 2]
    (hF : 2 < Nat.card F) (x : Matrix.PSL3Even.UnipotentGeometry.U F)
    (hx : x ^ 2 = 1) (hi : (centralizer ({x} : Set _)).index ≤ 2) : x ∈ center _ := by
  by_contra hn
  have he := Matrix.PSL3Even.UnipotentGeometry.involution_centralizer_index x hx hn
  omega

private def lastRoot {F : Type*} [Field F] [CharP F 2] :
    Multiplicative F →* Theory.SpecificGroups.SymplecticFour.unipotent (F := F) where
  toFun t := Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element 0 0 0 t.toAdd
  map_one' := Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_zero
  map_mul' x y := by
    simp [Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_mul]

private def firstRoot {F : Type*} [Field F] [CharP F 2] :
    Multiplicative F →* Theory.SpecificGroups.SymplecticFour.unipotent (F := F) where
  toFun t := Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element t.toAdd 0 0 0
  map_one' := Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_zero
  map_mul' x y := by
    simp [Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_mul]

private theorem symplectic_coordinate_central {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (x : Theory.SpecificGroups.SymplecticFour.unipotent (F := F))
    (hi : (centralizer ({x} : Set _)).index ≤ 2) : x ∈ center _ := by
  open Theory.SpecificGroups.SymplecticFour.CentralRootGeometry in
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    change (centralizer ({element b u w v} : Set _)).index ≤ 2 at hi
    apply (mem_center_iff_coordinates b u w v).mpr
    have hb : b = 0 := by
      by_contra hb
      have hk : (centralizer ({element b u w v} : Set _)).comap (lastRoot (F := F)) = ⊥ := by
        apply bot_unique
        intro t ht
        have hh := mem_centralizer_singleton_iff.mp ht
        change element 0 0 0 t.toAdd * element b u w v =
          element b u w v * element 0 0 0 t.toAdd at hh
        rw [element_mul,element_mul,element_eq_iff] at hh
        have hz : t.toAdd * b = 0 := by simpa using hh.2.2.1
        exact (mul_eq_zero.mp hz).resolve_right hb
      have hc := index_comap_le (centralizer ({element b u w v} : Set _)) (lastRoot (F := F))
      rw [hk,index_bot] at hc
      change Nat.card F ≤ _ at hc
      omega
    refine ⟨hb,?_⟩
    by_contra hv
    have hk : (centralizer ({element b u w v} : Set _)).comap (firstRoot (F := F)) = ⊥ := by
      apply bot_unique
      intro t ht
      have hh := mem_centralizer_singleton_iff.mp ht
      change element t.toAdd 0 0 0 * element b u w v =
        element b u w v * element t.toAdd 0 0 0 at hh
      rw [element_mul,element_mul,element_eq_iff] at hh
      have hz : v * t.toAdd = 0 := by simpa using hh.2.2.1.symm
      exact (mul_eq_zero.mp hz).resolve_left hv
    have hc := index_comap_le (centralizer ({element b u w v} : Set _)) (firstRoot (F := F))
    rw [hk,index_bot] at hc
    change Nat.card F ≤ _ at hc
    omega
/-- The original Sylow subgroup in a nonbinary PSL₃ model centralizes
an elementary subgroup whose relative centralizer has index at most two. -/
theorem linear_centralizes {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL G 3 (2 ^ n))
    (P : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAP : A ≤ (P : Subgroup G))
    (hi : ((centralizer (A : Set G)).subgroupOf (P : Subgroup G)).index ≤ 2) :
    A ≤ (center P).map (P : Subgroup G).subtype := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let c : P ≃* Matrix.PSL3Even.UnipotentGeometry.U F :=
    ((e.subgroupMap (P : Subgroup G)).trans
      (Q.equiv (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF))).trans
      (Matrix.PSL3.LinearThree.unipotentEquiv F).symm
  apply centralizes_of_sylow_coordinates (P : Subgroup G) A hAP hi c
  have hbig : 2 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
    norm_num at hh
    omega
  exact linear_coordinate_central hbig

/-- The symplectic root calculation uses the specified full Sylow, over the
same field as its projective model. -/
theorem symplectic_centralizes {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp G 2 (2 ^ n))
    (P : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAP : A ≤ (P : Subgroup G))
    (hi : ((centralizer (A : Set G)).subgroupOf (P : Subgroup G)).index ≤ 2) :
    A ≤ (center P).map (P : Subgroup G).subtype := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let e' := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
  let Q := P.mapSurjective (f := e'.toMonoidHom) e'.surjective
  let c : P ≃* Theory.SpecificGroups.SymplecticFour.unipotent (F := F) :=
    (e'.subgroupMap (P : Subgroup G)).trans
      (Q.equiv (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF (by omega)))
  apply centralizes_of_sylow_coordinates (P : Subgroup G) A hAP hi c
  have hbig : 2 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
    norm_num at hh
    omega
  exact fun x _ => symplectic_coordinate_central hbig x

/-- Every elementary subgroup of a Bender Sylow lies in its center. -/
theorem bender_centralizes {G : Type*} [Group G] [Finite G]
    (hm : ClassificationModels.IsBenderModel G)
    (P : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAP : A ≤ (P : Subgroup G)) :
    A ≤ (center P).map (P : Subgroup G).subtype := by
  have hp (a : G) (ha : a ∈ A) : a ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian a ha
  cases hm with
  | linear n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let := Theory.PSL2.binary_sylow_commutative_of_injective e.toMonoidHom e.injective P
    rw [center_eq_top, ←MonoidHom.range_eq_map, range_subtype]
    exact hAP
  | unitary n hn hm =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    have hfixed : Nat.card {a : F // J.conj a = a} = 2 ^ n :=
      FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
    obtain ⟨d⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hF hfixed
    let J' := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
    have hw := (SylowOmega.omega_of_projective_equiv J' hn hF hfixed rfl (e.trans d) P).1
    intro a ha
    exact (omegaOneAmbient_le_iff _ _).mp hw.le a (hAP ha) (hp a ha)
  | suzuki m hm he =>
    have hw := BenderSuzuki.MatrixGroups.suzukiSylow_omega_eq_center (by omega) he.some P
    intro a ha
    exact (omegaOneAmbient_le_iff _ _).mp hw.le a (hAP ha) (hp a ha)

private theorem degree_ge_four {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (A : Subgroup G)
    (hA : Nat.card A = 16) (hAZ : A ≤ (center P).map (P : Subgroup G).subtype)
    {n : ℕ} (hc : Nat.card (center P) = 2 ^ n) : 4 ≤ n := by
  have hsize := Nat.card_le_card_of_injective (inclusion hAZ) (inclusion_injective hAZ)
  rw [card_map_of_injective (P : Subgroup G).subtype_injective, hc,hA] at hsize
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hsize

/-- Sixteen central elements in the original PSL₃ Sylow force its original
field degree to be at least four. -/
theorem linear_degree_ge_four {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL G 3 (2 ^ n))
    (P : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAP : A ≤ (P : Subgroup G)) (hA : Nat.card A = 16)
    (hi : ((centralizer (A : Set G)).subgroupOf (P : Subgroup G)).index ≤ 2) : 4 ≤ n := by
  have hAZ := linear_centralizes hn hm P A hAP hi
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact degree_ge_four P A hA hAZ
    (Matrix.PSL3.LinearThree.card_center_sylow_of_equiv F (by omega) hF e P)

/-- The field degree remains the one in the given binary PSL₂ model. -/
theorem linearTwo_degree_ge_four {G : Type*} [Group G] [Finite G]
    {n : ℕ} (_hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL G 2 (2 ^ n))
    (P : Sylow 2 G) (A : Subgroup G)
    (hAP : A ≤ (P : Subgroup G)) (hA : Nat.card A = 16) : 4 ≤ n := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨c⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF Q
  have hc : Nat.card P = 2 ^ n := by
    rw [Nat.card_congr (e.subgroupMap (P : Subgroup G)).toEquiv]
    change Nat.card Q = _
    rw [←Nat.card_congr c.toEquiv, Nat.card_congr Multiplicative.toAdd]
    exact hF
  have hsize := Nat.card_le_card_of_injective (inclusion hAP) (inclusion_injective hAP)
  rw [hA,hc] at hsize
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hsize

/-- The fixed-field degree remains the one in the given unitary model. -/
theorem unitary_degree_ge_four {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSU G 3 (2 ^ n))
    (P : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAP : A ≤ (P : Subgroup G)) (hA : Nat.card A = 16) : 4 ≤ n := by
  have hAZ := bender_centralizes (.unitary n hn hm) P A hAP
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  have hfixed : Nat.card {a : F // J.conj a = a} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
  obtain ⟨d⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J (2^n) hF hfixed
  let J' := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨hw,_,hc⟩ := SylowOmega.omega_of_projective_equiv J' hn hF hfixed rfl (e.trans d) P
  rw [hw,card_map_of_injective (P : Subgroup G).subtype_injective] at hc
  exact degree_ge_four P A hA hAZ hc

/-- The original Suzuki parameter excludes Sz(8), whose Sylow center has
only eight elements. -/
theorem suzuki_parameter_ge_two {G : Type*} [Group G] [Finite G]
    {m : ℕ} (hm : 1 ≤ m)
    (he : Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (P : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAP : A ≤ (P : Subgroup G)) (hA : Nat.card A = 16) : 2 ≤ m := by
  have hAZ := bender_centralizes (.suzuki m hm he) P A hAP
  have hc := BenderSuzuki.MatrixGroups.suzukiSylow_omega_card (by omega) he.some P
  rw [BenderSuzuki.MatrixGroups.suzukiSylow_omega_eq_center (by omega) he.some P,
    card_map_of_injective (P : Subgroup G).subtype_injective] at hc
  have hn := degree_ge_four P A hA hAZ hc
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryRootCentralization
