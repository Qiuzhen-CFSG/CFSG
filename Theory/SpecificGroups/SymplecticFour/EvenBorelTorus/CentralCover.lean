module

public import Theory.GroupTheory.Commutator.CentralExtensionPairing
public import Theory.GroupTheory.Hall.TwoClosedTransport
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup

/-!
# Central covers of the even symplectic Borel

The quotient of a central Borel preimage by its two-core is abelian. Choose
lifts of generators of the two cyclic diagonal factors. The Weyl matrix
interchanging the first hyperbolic pair inverts the first factor and fixes
the second. Their lifted commutator is central; conjugation therefore both
fixes and inverts it. Its square is one, so it belongs to the two-core.

The normal Sylow two-subgroup maps onto the unipotent character kernel.
Consequently, modulo the two-core, every element is a central kernel element
times a product of powers of the two chosen lifts. Those lifts commute in
the quotient, proving the claim without a multiplier computation.

For the derived carrier over a field of order greater than two, the proved
matrix-inclusion equivalence transports the literal Borel. This discharges
the central-cover abelianness premise of the covered-Borel calculation in
Aschbacher--Smith, `refs/quasithin.pdf`, E.2.2(2b), printed pp.215--216,
and 4.4.13, printed pp.623--624. Original-overlap transport and Hall control
remain with their separate assembly owner.
-/

open Subgroup
open scoped commutatorElement

namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CentralCover
variable {E G : Type*} [Group E] [Group G]

private lemma commutator_sq (f : E →* G) (hk : f.ker ≤ center E)
    (x y w : E) (hxy : Commute (f x) (f y))
    (hx : f (w*x*w⁻¹) = f x⁻¹) (hy : f (w*y*w⁻¹) = f y) :
    ⁅x,y⁆ ^ 2 = 1 := by
  have hc : ⁅x,y⁆ ∈ center E := hk (by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact hxy.commutator_eq)
  have hinv : ⁅x,y⁆ = ⁅x,y⁆⁻¹ := by
    calc
      ⁅x,y⁆ = w * ⁅x,y⁆ * w⁻¹ := by
        rw [mem_center_iff.mp hc w]
        simp [mul_assoc]
      _ = ⁅w*x*w⁻¹,w*y*w⁻¹⁆ := conjugate_commutatorElement _ _ _
      _ = ⁅x⁻¹,y⁆ := CentralExtension.commutator_eq_of_image_eq f hk hx hy
      _ = ⁅x,y⁆⁻¹ := by
        rw [commutatorElement_inv_left, ← commutatorElement_inv,
          mem_center_iff.mp ((center E).inv_mem hc) x⁻¹]
        simp [mul_assoc]
  rw [pow_two]
  conv_lhs => lhs; rw [hinv]
  exact inv_mul_cancel _

private lemma central_square_mem_core [Finite E] (x : E) (hc : x ∈ center E) (hs : x^2=1) :
    x ∈ pCore 2 E := by
  have hZ : zpowers x ≤ center E := zpowers_le.mpr hc
  let : (zpowers x).Normal := ⟨by
    intro a ha b
    simpa only [mem_center_iff.mp (hZ ha) b, mul_assoc, mul_inv_cancel, mul_one] using ha⟩
  have hp : IsPGroup 2 (zpowers x) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hs
  exact (show zpowers x ≤ pCore 2 E from le_sSup ⟨inferInstance, hp⟩) (mem_zpowers x)


private lemma quotient_commutative [Finite E] {A : Type*} [CommGroup A]
    (r : E →* G) (hr : Function.Surjective r) (hk : r.ker ≤ center E)
    (c : G →* A × A) (hc : IsPGroup 2 c.ker)
    (hi : Odd (pCore 2 E).index)
    (a : A) (ha : ∀ b : A, b ∈ zpowers a)
    (x y : E) (hx : c (r x) = (a,1)) (hy : c (r y) = (1,a))
    (hxy : Commute (QuotientGroup.mk' (pCore 2 E) x)
      (QuotientGroup.mk' (pCore 2 E) y)) :
    IsMulCommutative (E ⧸ pCore 2 E) := by
  let q := QuotientGroup.mk' (pCore 2 E)
  let P : Sylow 2 E := (pCore_isPGroup (p := 2) (G := E)).toSylow
    (Nat.not_even_iff_odd.mpr hi ∘ even_iff_two_dvd.mpr)
  have hker : c.ker ≤ (pCore 2 E).map r := hc.le_sylow_of_normal (P.mapSurjective hr)
  have hform (b : E) : ∃ (k : E) (i j : ℤ), k ∈ center E ∧
      q b = q k * ((q x)^i * (q y)^j) := by
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (ha (c (r b)).1)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (ha (c (r b)).2)
    let t := x^i*y^j
    have ht : c (r t) = c (r b) := by
      apply Prod.ext <;> simp [t, hx, hy, hi, hj]
    have hz : r (b*t⁻¹) ∈ c.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_inv, ht, mul_inv_cancel]
    obtain ⟨u, hu, heu⟩ := hker hz
    let k := u⁻¹*(b*t⁻¹)
    have hk0 : k ∈ r.ker := by
      rw [MonoidHom.mem_ker]
      simp only [k, map_mul, map_inv, heu]
      simp
    refine ⟨k, i, j, hk hk0, ?_⟩
    have hqu : q u = 1 := (QuotientGroup.eq_one_iff _).mpr hu
    simp only [k, map_mul, map_inv, hqu, inv_one, one_mul, t, map_zpow]
    simp [mul_assoc]
  have hcent (k : E) (hk : k ∈ center E) (z : E ⧸ pCore 2 E) : Commute (q k) z := by
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ z
    exact (show Commute k b from (mem_center_iff.mp hk b).symm).map q
  apply IsMulCommutative.of_comm
  intro b d
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ b
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective _ d
  obtain ⟨k, i, j, hk, hb⟩ := hform b
  obtain ⟨l, m, n, hl, hd⟩ := hform d
  rw [hb, hd]
  apply Commute.eq
  apply (hcent k hk _).mul_left
  apply (hcent l hl _).symm.mul_right
  exact ((Commute.zpow_zpow_self ..).mul_right (hxy.zpow_zpow i n)).mul_left
    ((hxy.symm.zpow_zpow j m).mul_right (Commute.zpow_zpow_self ..))
end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CentralCover

namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CentralCover
open Matrix
open scoped CharTwo
variable {F : Type*} [Field F] [CharP F 2]
private def reflectionMatrix : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![0,0;0,1] !![1,0;0,0] !![1,0;0,0] !![0,0;0,1]
private theorem reflectionMatrix_mem : reflectionMatrix (F := F) ∈ Sp F := by
  rw [SymplecticGroup.mem_iff]
  simp [reflectionMatrix, Matrix.J, fromBlocks_multiply, fromBlocks_transpose]
  (repeat' apply And.intro) <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
private def reflection : Sp F := ⟨reflectionMatrix, reflectionMatrix_mem⟩
private lemma reflection_conjugate (a b : Fˣ) :
    reflection * diagonalTorus a b * reflection⁻¹ = diagonalTorus a⁻¹ b := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  change reflectionMatrix * (diagonalTorus a b).val =
    (diagonalTorus a⁻¹ b).val * reflectionMatrix
  simp only [diagonalTorus]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [reflectionMatrix, Matrix.fromBlocks]

omit [CharP F 2] in
private noncomputable def diagonalCharacters : borel (F := F) →* Fˣ × Fˣ where
  toFun g := ((borelCharacters g).1, (borelCharacters g).1⁻¹ * (borelCharacters g).2)
  map_one' := by simp only [map_one, Prod.fst_one, Prod.snd_one, inv_one, one_mul]; rfl
  map_mul' x y := by
    simp only [map_mul, Prod.fst_mul, Prod.snd_mul, Prod.mk_mul_mk, _root_.mul_inv_rev]
    congr 1
    ac_rfl

omit [CharP F 2] in
private lemma diagonalCharacters_diagonal (a b : Fˣ) :
    diagonalCharacters (⟨diagonalTorus a b, diagonalTorus_mem_borel a b⟩ : borel) = (a,b) := by
  have h : borelCharacters (⟨diagonalTorus a b, diagonalTorus_mem_borel a b⟩ : borel) =
      (a,a*b) := Prod.ext (diagonalTorus_point_character a b) (diagonalTorus_plane_character a b)
  change ((borelCharacters _).1, (borelCharacters _).1⁻¹ * (borelCharacters _).2) = _
  simp [h]

omit [CharP F 2] in
private lemma diagonalCharacters_ker : (diagonalCharacters (F := F)).ker =
    (borelCharacters (F := F)).ker := by
  ext g
  simp only [MonoidHom.mem_ker]
  change ((borelCharacters g).1, (borelCharacters g).1⁻¹ * (borelCharacters g).2) = (1,1) ↔
    borelCharacters g = (1,1)
  constructor
  · intro h
    have h1 : (borelCharacters g).1 = 1 := congrArg Prod.fst h
    have h2 : (borelCharacters g).1⁻¹ * (borelCharacters g).2 = 1 := congrArg Prod.snd h
    apply Prod.ext h1
    simpa only [h1, inv_one, one_mul] using h2
  · intro h
    simp [h]

variable [Finite F]
variable {E : Type*} [Group E] [Finite E]
/-- In a finite central cover of the full symplectic group, the Borel preimage
has abelian quotient by its two-core, including over the binary field. -/
public theorem full_preimage_quotient_abelian {n : ℕ} (hF : Nat.card F = 2^n)
    (f : E →* Sp F) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    IsMulCommutative ((borel.comap f) ⧸ pCore 2 (borel.comap f)) := by
  let B := borel.comap f
  let r : B →* borel := (f.comp B.subtype).codRestrict _ (fun b => b.property)
  have hr : Function.Surjective r := by
    intro b
    obtain ⟨e, he⟩ := hf b.val
    exact ⟨⟨e, show f e ∈ borel from he.symm ▸ b.property⟩, Subtype.ext he⟩
  have hkr : r.ker ≤ center B := by
    intro b hb
    apply mem_center_iff.mpr
    intro d
    apply Subtype.ext
    exact mem_center_iff.mp (hk (congrArg (fun z : borel (F := F) => z.val) hb)) d.val
  have hi : Odd (pCore 2 B).index := by
    apply OddHall.odd_pCore_index_comap_of_central_kernel f hf hk
    rw [index_eq_card, Nat.card_congr (quotientTorusEquiv hF).toEquiv]
    exact Nat.coprime_two_left.mp (torus_odd hF)
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨x0, hx0⟩ := hf (diagonalTorus a 1)
  obtain ⟨y0, hy0⟩ := hf (diagonalTorus 1 a)
  obtain ⟨w, hw⟩ := hf (reflection (F := F))
  let x : B := ⟨x0, show f x0 ∈ borel from hx0.symm ▸ diagonalTorus_mem_borel a 1⟩
  let y : B := ⟨y0, show f y0 ∈ borel from hy0.symm ▸ diagonalTorus_mem_borel 1 a⟩
  have hrx : r x = ⟨diagonalTorus a 1, diagonalTorus_mem_borel a 1⟩ := Subtype.ext hx0
  have hry : r y = ⟨diagonalTorus 1 a, diagonalTorus_mem_borel 1 a⟩ := Subtype.ext hy0
  have hcomm : Commute (f x0) (f y0) := by
    rw [hx0, hy0]
    exact (Commute.all (a,1) (1,a)).map CentralRootGeometry.diagonalTorusHom
  have hc0 : ⁅x0,y0⁆ ∈ center E := hk (by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact hcomm.commutator_eq)
  have hs : ⁅x0,y0⁆^2 = 1 := commutator_sq f hk x0 y0 w hcomm (by
      simp only [map_mul, map_inv, hw, hx0]
      rw [reflection_conjugate]
      simpa only [Prod.inv_mk, inv_one, CentralRootGeometry.diagonalTorusHom_apply] using
        (CentralRootGeometry.diagonalTorusHom (F := F)).map_inv (a,1)) (by
      simp only [map_mul, map_inv, hw, hy0]
      rw [reflection_conjugate, inv_one])
  have hc : ⁅x,y⁆ ∈ center B := by
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (mem_center_iff.mp hc0 b.val)
  have hsq : ⁅x,y⁆^2 = 1 := Subtype.ext hs
  have hcore := central_square_mem_core ⁅x,y⁆ hc hsq
  have hpc : IsPGroup 2 (diagonalCharacters (F := F)).ker := by
    rw [diagonalCharacters_ker, characters_ker]
    exact (isPGroup_unipotent hF).comap_subtype
  apply quotient_commutative r hr hkr diagonalCharacters hpc hi a ha x y
      (hrx ▸ diagonalCharacters_diagonal a 1) (hry ▸ diagonalCharacters_diagonal 1 a)
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr hcore
end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CentralCover

namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {E : Type*} [Group E] [Finite E]
/-- The literal derived Borel in a finite central cover has abelian quotient by
its two-core. The nonbinary derived-to-full comparison is the actual matrix inclusion. -/
public theorem central_preimage_quotient_abelian {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2^n) (f : E →* commutator (Sp F))
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    IsMulCommutative ((((borel (F := F)).subgroupOf (commutator (Sp F))).comap f) ⧸
      pCore 2 (((borel (F := F)).subgroupOf (commutator (Sp F))).comap f)) := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hn
  let e := derivedEquivFull_of_card_gt_two hq
  let g := e.toMonoidHom.comp f
  have hg : Function.Surjective g := e.surjective.comp hf
  have hkg : g.ker ≤ center E := by
    intro x hx
    apply hk
    apply e.injective
    exact (show e (f x) = 1 from hx).trans (map_one e).symm
  have hg_eq : g = (commutator (Sp F)).subtype.comp f := by
    apply MonoidHom.ext
    intro x
    exact derivedEquivFull_of_card_gt_two_apply hq (f x)
  have h := CentralCover.full_preimage_quotient_abelian hF g hg hkg
  rw [hg_eq] at h
  exact h
end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
