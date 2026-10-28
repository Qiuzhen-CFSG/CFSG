module

public import Theory.AtlasPort.LinearGroups.G2.BinarySecondParabolic
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.GroupTheory.PrimeRankNonabelianCube

/-!
# The three-rank of the binary octonion automorphism group

Two explicit conjugates of the cubic `rootE 1 * weylR` generate a nonabelian
subgroup of order 27. Their commutator is central of order dividing three;
the resulting Heisenberg-coordinate homomorphism has nonabelian image, so
that image has order 27. The checked order of G₂(2) makes it a Sylow subgroup.
Every abelian subgroup of a nonabelian group of prime-cube order is proper,
giving three-rank at most two in full G₂(2), and hence in its derived group.

All matrix identities are checked by kernel reduction on the eight octonion
basis vectors. No exceptional isomorphism or derived-group order is used.
The root conventions come from the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1), printed pp.3–4, repeated on pp.481–482.
-/

namespace Atlas.G2.BinaryThreeRank
open Atlas.G2.Explicit Atlas.SplitOctonion

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem model_ext (g h : Model (ZMod 2))
    (he : ∀ i j, g.val (basisVector i) j = h.val (basisVector i) j) : g = h := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact linearMap_ext _ _ (fun i => funext (he i))

def x : Model (ZMod 2) := BinaryCore.movingActor
def conjugator : Model (ZMod 2) := rootD 1 * rootF 1 * weylS * rootF 1
def y : Model (ZMod 2) := conjugator * x * conjugator⁻¹

def z : Model (ZMod 2) := x * y * x⁻¹ * y⁻¹

theorem z_cube : z ^ 3 = 1 := by
  apply model_ext
  exact (by decide +kernel : ∀ i j, (z ^ 3).val (basisVector i) j = (1 : Model (ZMod 2)).val (basisVector i) j)

theorem x_z : x * z = z * x := by
  apply model_ext
  exact (by decide +kernel : ∀ i j, (x*z).val (basisVector i) j = (z*x).val (basisVector i) j)

theorem y_z : y * z = z * y := by
  apply model_ext
  exact (by decide +kernel : ∀ i j, (y*z).val (basisVector i) j = (z*y).val (basisVector i) j)

theorem x_y_ne : x * y ≠ y * x := by
  intro h
  have he := congrArg (fun g : Model (ZMod 2) => g.val (basisVector 0) 1) h
  exact (by decide +kernel : (x*y).val (basisVector 0) 1 ≠ (y*x).val (basisVector 0) 1) he

@[ext] structure Parameters where
  i : ZMod 3
  j : ZMod 3
  k : ZMod 3
deriving DecidableEq

def tripleEquiv : (ZMod 3 × ZMod 3 × ZMod 3) ≃ Parameters where
  toFun a := ⟨a.1, a.2.1, a.2.2⟩
  invFun a := (a.i, a.j, a.k)
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Parameters := Fintype.ofEquiv _ tripleEquiv
instance : Mul Parameters := ⟨fun a b => ⟨a.i+b.i, a.j+b.j, a.k+b.k-a.j*b.i⟩⟩
instance : One Parameters := ⟨⟨0,0,0⟩⟩
instance : Inv Parameters := ⟨fun a => ⟨-a.i,-a.j,-a.k-a.j*a.i⟩⟩
instance : Group Parameters where
  mul_assoc a b c := by
    apply Parameters.ext
    · exact add_assoc a.i b.i c.i
    · exact add_assoc a.j b.j c.j
    · change (a.k + b.k - a.j*b.i) + c.k - (a.j+b.j)*c.i =
        a.k + (b.k+c.k-b.j*c.i) - a.j*(b.i+c.i)
      ring
  one_mul a := by
    apply Parameters.ext
    · exact zero_add a.i
    · exact zero_add a.j
    · change 0+a.k-0*a.i=a.k
      ring
  mul_one a := by
    apply Parameters.ext
    · exact add_zero a.i
    · exact add_zero a.j
    · change a.k+0-a.j*0=a.k
      ring
  inv_mul_cancel a := by
    apply Parameters.ext
    · exact neg_add_cancel a.i
    · exact neg_add_cancel a.j
    · change (-a.k-a.j*a.i)+a.k-(-a.j)*a.i=0
      ring

theorem card_parameters : Nat.card Parameters = 27 := by
  rw [← Nat.card_congr tripleEquiv]
  simp

def eval (a : Parameters) : Model (ZMod 2) := x ^ a.i.val * y ^ a.j.val * z ^ a.k.val

theorem pow_add_three (g : Model (ZMod 2)) (hg : g^3=1) (a b : ZMod 3) :
    g ^ (a+b).val = g ^ a.val * g ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hg).symm

theorem y_cube : y^3=1 := by
  rw [y, conj_pow, show x^3=1 from BinaryCore.movingActor_cube]
  group

theorem twist (a b : ZMod 3) :
    y ^ a.val * x ^ b.val = x ^ b.val * y ^ a.val * z ^ (-a*b).val := by
  apply model_ext
  exact (by decide +kernel : ∀ (a b : ZMod 3) i j,
    (y ^ a.val * x ^ b.val).val (basisVector i) j =
    (x ^ b.val * y ^ a.val * z ^ (-a*b).val).val (basisVector i) j) a b

theorem zx_pow (a b : ZMod 3) : z ^ a.val * x ^ b.val = x ^ b.val * z ^ a.val :=
  (Commute.pow_pow (show Commute z x from x_z.symm) _ _).eq

theorem zy_pow (a b : ZMod 3) : z ^ a.val * y ^ b.val = y ^ b.val * z ^ a.val :=
  (Commute.pow_pow (show Commute z y from y_z.symm) _ _).eq

theorem eval_mul (a b : Parameters) :
    eval (a*b) =
      eval a * eval b := by
  rcases a with ⟨ai, aj, ak⟩
  rcases b with ⟨bi, bj, bk⟩
  change
    x ^ (ai + bi).val *
        y ^ (aj + bj).val *
        z ^ (ak + bk - aj * bi).val =
      (x ^ ai.val * y ^ aj.val *
          z ^ ak.val) *
        (x ^ bi.val * y ^ bj.val *
          z ^ bk.val)
  let t : ZMod 3 := -aj * bi
  have hcoord : ak + bk - aj * bi = ak + bk + t := by
    dsimp [t]
    ring
  rw [hcoord, (pow_add_three x BinaryCore.movingActor_cube) ai bi,
    (pow_add_three y y_cube) aj bj,
    (pow_add_three z z_cube) (ak + bk) t,
    (pow_add_three z z_cube) ak bk]
  have hZB := zx_pow ak bi
  have hZX := zy_pow ak bj
  have hTX := zy_pow t bj
  have htwist := twist aj bi
  have hTCX :
      (z ^ t.val * z ^ ak.val) *
          y ^ bj.val =
        y ^ bj.val *
          (z ^ t.val * z ^ ak.val) := by
    calc
      (z ^ t.val * z ^ ak.val) *
          y ^ bj.val =
          z ^ t.val *
            (z ^ ak.val * y ^ bj.val) := by group
      _ = z ^ t.val *
            (y ^ bj.val * z ^ ak.val) := by
          rw [hZX]
      _ = (z ^ t.val * y ^ bj.val) *
            z ^ ak.val := by group
      _ = (y ^ bj.val * z ^ t.val) *
            z ^ ak.val := by rw [hTX]
      _ = y ^ bj.val *
            (z ^ t.val * z ^ ak.val) := by group
  have hZreorder :
      (z ^ t.val * z ^ ak.val) *
          z ^ bk.val =
        (z ^ ak.val * z ^ bk.val) *
          z ^ t.val := by
    rw [← (pow_add_three z z_cube) t ak,
      ← (pow_add_three z z_cube) (t + ak) bk]
    rw [show t + ak + bk = ak + bk + t by ring]
    rw [(pow_add_three z z_cube) (ak + bk) t,
      (pow_add_three z z_cube) ak bk]
  symm
  calc
    (x ^ ai.val * y ^ aj.val *
          z ^ ak.val) *
        (x ^ bi.val * y ^ bj.val *
          z ^ bk.val) =
      x ^ ai.val * y ^ aj.val *
        (z ^ ak.val * x ^ bi.val) *
        y ^ bj.val * z ^ bk.val := by group
    _ = x ^ ai.val * y ^ aj.val *
        (x ^ bi.val * z ^ ak.val) *
        y ^ bj.val * z ^ bk.val := by rw [hZB]
    _ = x ^ ai.val *
        (y ^ aj.val * x ^ bi.val) *
        z ^ ak.val * y ^ bj.val *
        z ^ bk.val := by group
    _ = x ^ ai.val *
        (x ^ bi.val * y ^ aj.val *
          z ^ t.val) *
        z ^ ak.val * y ^ bj.val *
        z ^ bk.val := by rw [htwist]
    _ = (x ^ ai.val * x ^ bi.val) *
        y ^ aj.val *
        ((z ^ t.val * z ^ ak.val) *
          y ^ bj.val) *
        z ^ bk.val := by group
    _ = (x ^ ai.val * x ^ bi.val) *
        y ^ aj.val *
        (y ^ bj.val *
          (z ^ t.val * z ^ ak.val)) *
        z ^ bk.val := by rw [hTCX]
    _ = (x ^ ai.val * x ^ bi.val) *
        (y ^ aj.val * y ^ bj.val) *
        ((z ^ t.val * z ^ ak.val) *
          z ^ bk.val) := by group
    _ = (x ^ ai.val * x ^ bi.val) *
        (y ^ aj.val * y ^ bj.val) *
        ((z ^ ak.val * z ^ bk.val) *
          z ^ t.val) := by rw [hZreorder]


def embedding : Parameters →* Model (ZMod 2) where
  toFun := eval
  map_one' := by simp [eval]; rfl
  map_mul' := eval_mul


open scoped IsMulCommutative

theorem image_noncommutative : ¬ IsMulCommutative embedding.range := by
  intro h
  let : IsMulCommutative embedding.range := h
  let a : embedding.range := ⟨x, ⟨⟨1,0,0⟩, by change x ^ 1 * y ^ 0 * z ^ 0 = x; simp⟩⟩
  let b : embedding.range := ⟨y, ⟨⟨0,1,0⟩, by change x ^ 0 * y ^ 1 * z ^ 0 = y; simp⟩⟩
  exact x_y_ne (congrArg Subtype.val (mul_comm a b))

theorem card_image : Nat.card embedding.range = 27 := by
  have hd : Nat.card embedding.range ∣ 3^3 := by
    have h := Subgroup.card_range_dvd embedding
    rw [card_parameters] at h
    exact h
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have hcases : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hc : Nat.card embedding.range ∣ 3 := by rw [he]; norm_num
    let : IsCyclic embedding.range := isCyclic_of_card_dvd_prime hc
    exact False.elim (image_noncommutative inferInstance)
  · let : IsCyclic embedding.range := isCyclic_of_prime_card (show Nat.card embedding.range = 3 from he)
    exact False.elim (image_noncommutative inferInstance)
  · exact False.elim (image_noncommutative (IsPGroup.isMulCommutative_of_card_eq_prime_sq he))
  · exact he

noncomputable def threeSylow : Sylow 3 (Model (ZMod 2)) :=
  (IsPGroup.of_card (show Nat.card embedding.range = 3^3 from card_image)).toSylow (by
    have h := embedding.range.card_mul_index
    rw [card_image, Atlas.G2.card_Model, Nat.card_zmod] at h
    have hi : embedding.range.index = 448 := by omega
    rw [hi]
    decide)

/-- The actual binary octonion automorphism group has three-rank at most two. -/
public theorem primeRank_le_two : primeRank 3 (Model (ZMod 2)) ≤ 2 :=
  primeRank_le_two_of_nonabelian_sylow_cube threeSylow card_image image_noncommutative

end Atlas.G2.BinaryThreeRank
