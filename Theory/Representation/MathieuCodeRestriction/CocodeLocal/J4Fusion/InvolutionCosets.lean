module
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Transport
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage

/-!
# The two involution cosets in the native Todd module

For the marked 2A and 2B involutions, decompose the fixed space into the
image of s-1 and a complement of dimension three or one. A certified word
in the existing M24 generators cycles all seven nonzero classes in the
first complement. Small matrix identities and eight vector identities
certify the calculation; no new involution classification is assumed.

The returned native actors and displacement witnesses lift to actual Todd
group conjugators in SourceFusion.ToddInvolutions. The representative probe
including import preparation took 48.95 seconds and 2,161,684 KiB maximum
RSS. The evaluated permutation replaces repeated expansion of its word.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), proof of (6.4), p.602.
-/

public section
open Sporadic.Mathieu Representation.BinaryOffender
open scoped BigOperators
namespace MathieuCode.J4Fusion.InvolutionCosets
open CocodeOctad.Involutions
noncomputable section

private def bits {n : ℕ} (v : BitVec n) : Fin n → ZMod 2 :=
  fun i => if v.getLsb i then 1 else 0

private def columns {m n : ℕ} (v : Fin n → BitVec m) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => bits (v j) i

private def actionMatrix (g : M24) : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  fun i j => reduce (fullRepresentation g (coordinateWord j).val) i

private lemma actionMatrix_eq (g : M24) :
    (actionMatrix g).mulVecLin = (coordinates.comp (cocodeRepresentation g)).comp sectionMap := by
  apply pi_ext_one
  intro j
  ext i
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    LinearMap.comp_apply, sectionMap_single, cocodeRepresentation_mk, coordinates_mk]
  rfl

private lemma actionMatrix_apply (g : M24) (v : Cocode) :
    (actionMatrix g).mulVec (coordinates v) = coordinates (cocodeRepresentation g v) := by
  have hh := LinearMap.congr_fun (actionMatrix_eq g) (coordinates v)
  change _ = coordinates (cocodeRepresentation g (sectionMap (coordinates v))) at hh
  have he : sectionMap (coordinates v) = v := LinearMap.congr_fun sectionMap_coordinates v
  rw [he] at hh
  exact hh

private lemma actionMatrix_pow (g : M24) (k : ℕ) (v : Cocode) :
    ((actionMatrix g)^k).mulVec (coordinates v) = coordinates (cocodeRepresentation (g^k) v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ',←Matrix.mulVec_mulVec,ih,actionMatrix_apply,pow_succ',map_mul,Module.End.mul_apply]

private def actorWord : List (Fin 3) := [1,0,1,0,2,0,2,0,1,0,1,0,1,0,1,0,1,0,1,0,2,0,1]
private def actorPoint : Fin 24 → Fin 24 :=
  ![11,1,17,2,3,0,18,10,13,12,19,4,9,21,7,23,14,5,15,8,6,20,16,22]
private def actorInverse : Fin 24 → Fin 24 :=
  ![5,1,3,4,11,17,20,14,19,12,7,0,9,8,16,18,22,2,6,10,21,13,23,15]
private def actorPerm : Equiv.Perm (Fin 24) where
  toFun := actorPoint
  invFun := actorInverse
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private lemma actorPerm_eq_word : actorPerm =
    (M24InvolutionCentralizers.FusionData.evaluate actorWord).val := by
  apply Equiv.ext
  intro i
  rw [M24InvolutionCentralizers.FusionData.evaluate_apply]
  revert i
  decide +kernel

def actor : M24 := ⟨actorPerm, by
  rw [actorPerm_eq_word]
  exact (M24InvolutionCentralizers.FusionData.evaluate actorWord).property⟩

lemma actor_commutes : Commute actor z := by
  apply Subtype.ext
  decide +kernel

private def actorMatrix : Matrix (Fin 11) (Fin 11) (ZMod 2) :=
  columns ![1152,1879,283,1024,1028,1780,1032,1485,962,1280,1040]

set_option maxRecDepth 4096 in
private lemma actionMatrix_actor : actionMatrix actor = actorMatrix := by
  decide +kernel

private def zD : Matrix (Fin 11) (Fin 11) (ZMod 2) := columns ![396,664,201,325,989,461,396,325,201,989,593]
private def zW : Matrix (Fin 11) (Fin 11) (ZMod 2) := columns ![0,0,0,0,0,0,33,37,36,39,0]
private def zT : Matrix (Fin 11) (Fin 3) (ZMod 2) := columns ![13,23,1030]
private def zQ : Matrix (Fin 3) (Fin 11) (ZMod 2) := columns ![0,0,0,1,2,0,0,1,0,2,4]

private lemma z_decomposition : (1 : Matrix (Fin 11) (Fin 11) (ZMod 2)) =
    zD * zW + zT * zQ + zW * zD := by decide +kernel

set_option maxRecDepth 4096 in
private lemma displacement_z : displacementMatrix z = zD := by decide +kernel

private def tD : Matrix (Fin 11) (Fin 11) (ZMod 2) := columns ![1153,1538,1044,1477,1044,465,570,1153,1582,1538,0]
private def tW : Matrix (Fin 11) (Fin 11) (ZMod 2) := columns ![0,0,0,0,0,70,0,5,9,6,4]
private def tT : Matrix (Fin 11) (Fin 1) (ZMod 2) := columns ![20]
private def tQ : Matrix (Fin 1) (Fin 11) (ZMod 2) := columns ![0,0,0,0,1,0,0,1,0,1,1]

private lemma t_decomposition : (1 : Matrix (Fin 11) (Fin 11) (ZMod 2)) =
    tD * tW + tT * tQ + tW * tD := by decide +kernel

set_option maxRecDepth 4096 in
private lemma displacement_t : displacementMatrix t = tD := by decide +kernel

private def orbitWords : Fin 7 → BitVec 11 := ![13,411,1500,1800,1746,902,1347]
private lemma orbit_step (k : Fin 6) : actorMatrix.mulVec (bits (orbitWords k.castSucc)) =
    bits (orbitWords k.succ) := by revert k; decide +kernel

private lemma orbit_pow (k : Fin 7) :
    (actorMatrix^k.val).mulVec (bits 13) = bits (orbitWords k) := by
  induction k using Fin.induction with
  | zero => simp [orbitWords]
  | succ k ih =>
    simp only [Fin.val_castSucc] at ih
    rw [Fin.val_succ,pow_succ',←Matrix.mulVec_mulVec,ih]
    exact orbit_step k

private def orbitIndex (q : Fin 3 → ZMod 2) : Fin 7 :=
  (![0,0,1,5,6,4,2,3] : Fin 8 → Fin 7)
    ⟨(q 0).val + 2*(q 1).val + 4*(q 2).val, by
      have h0 := (q 0).val_lt; have h1 := (q 1).val_lt; have h2 := (q 2).val_lt
      omega⟩
private def orbitCorrection (q : Fin 3 → ZMod 2) : BitVec 11 :=
  (![0,2011,2010,2045,2014,2040,2043,2008] : Fin 8 → BitVec 11)
    ⟨(q 0).val + 2*(q 1).val + 4*(q 2).val, by
      have h0 := (q 0).val_lt; have h1 := (q 1).val_lt; have h2 := (q 2).val_lt
      omega⟩

private lemma nonzero_cosets : ∀ q : Fin 3 → ZMod 2, q ≠ 0 →
    zT.mulVec q = zD.mulVec (bits (orbitCorrection q)) + bits (orbitWords (orbitIndex q)) := by
  decide +kernel

private lemma one_coset : ∀ q : Fin 1 → ZMod 2, q ≠ 0 → tT.mulVec q = bits 20 := by
  decide +kernel

private lemma coordinates_section (v : Coordinates) : coordinates (sectionMap v) = v :=
  LinearMap.congr_fun coordinates_sectionMap v

private lemma displacement_apply (s : M24) (v : Cocode) :
    (displacementMatrix s).mulVec (coordinates v) =
      coordinates (cocodeRepresentation s v - v) := by
  have hh := LinearMap.congr_fun (displacementMatrix_eq s) (coordinates v)
  change _ = coordinates (cocodeRepresentation s (sectionMap (coordinates v)) - sectionMap (coordinates v)) at hh
  have he : sectionMap (coordinates v) = v := LinearMap.congr_fun sectionMap_coordinates v
  rw [he] at hh
  exact hh

def zVector : Cocode := sectionMap (bits 13)
def tVector : Cocode := sectionMap (bits 20)

lemma zVector_fixed : cocodeRepresentation z zVector = zVector := by
  apply coordinateEquiv.injective
  change coordinates (cocodeRepresentation z zVector) = coordinates zVector
  apply sub_eq_zero.mp
  rw [←map_sub,←displacement_apply,displacement_z]
  change zD.mulVec (coordinates (sectionMap (bits 13))) = 0
  rw [coordinates_section]
  decide +kernel

lemma tVector_fixed : cocodeRepresentation t tVector = tVector := by
  apply coordinateEquiv.injective
  change coordinates (cocodeRepresentation t tVector) = coordinates tVector
  apply sub_eq_zero.mp
  rw [←map_sub,←displacement_apply,displacement_t]
  change tD.mulVec (coordinates (sectionMap (bits 20))) = 0
  rw [coordinates_section]
  decide +kernel

/-- The seven nonzero classes of the first fixed quotient form one orbit.
The returned actor is an actual power of a certified native M24 word. -/
lemma fixed_coset_z (v : Cocode) (hv : cocodeRepresentation z v = v) :
    (∃ w, v = cocodeRepresentation z w - w) ∨
    ∃ (k : Fin 7) (w : Cocode),
      v = cocodeRepresentation z w - w + cocodeRepresentation (actor^k.val) zVector := by
  have hd : zD.mulVec (coordinates v) = 0 := by
    rw [←displacement_z,displacement_apply,hv,sub_self,map_zero]
  have he : coordinates v = zD.mulVec (zW.mulVec (coordinates v)) +
      zT.mulVec (zQ.mulVec (coordinates v)) := by
    have he := congrArg (fun A => A.mulVec (coordinates v)) z_decomposition
    simpa only [Matrix.one_mulVec,Matrix.add_mulVec,←Matrix.mulVec_mulVec,hd,
      Matrix.mulVec_zero,add_zero] using he
  by_cases hq : zQ.mulVec (coordinates v) = 0
  · rw [hq,Matrix.mulVec_zero,add_zero] at he
    refine Or.inl ⟨sectionMap (zW.mulVec (coordinates v)),?_⟩
    apply coordinateEquiv.injective
    change coordinates v = coordinates _
    rw [←displacement_apply,displacement_z,coordinates_section]
    exact he
  · rw [nonzero_cosets _ hq] at he
    refine Or.inr ⟨orbitIndex (zQ.mulVec (coordinates v)),
      sectionMap (zW.mulVec (coordinates v) + bits (orbitCorrection (zQ.mulVec (coordinates v)))),?_⟩
    apply coordinateEquiv.injective
    change coordinates v = coordinates _
    rw [map_add,←displacement_apply,displacement_z,coordinates_section,
      ←actionMatrix_pow,actionMatrix_actor]
    change coordinates v = _ + (actorMatrix ^ _).mulVec (coordinates (sectionMap (bits 13)))
    rw [coordinates_section,orbit_pow,Matrix.mulVec_add,add_assoc]
    exact he

/-- The second fixed quotient has just its zero and nonzero class. -/
lemma fixed_coset_t (v : Cocode) (hv : cocodeRepresentation t v = v) :
    (∃ w, v = cocodeRepresentation t w - w) ∨
    ∃ w, v = cocodeRepresentation t w - w + tVector := by
  have hd : tD.mulVec (coordinates v) = 0 := by
    rw [←displacement_t,displacement_apply,hv,sub_self,map_zero]
  have he : coordinates v = tD.mulVec (tW.mulVec (coordinates v)) +
      tT.mulVec (tQ.mulVec (coordinates v)) := by
    have he := congrArg (fun A => A.mulVec (coordinates v)) t_decomposition
    simpa only [Matrix.one_mulVec,Matrix.add_mulVec,←Matrix.mulVec_mulVec,hd,
      Matrix.mulVec_zero,add_zero] using he
  by_cases hq : tQ.mulVec (coordinates v) = 0
  · rw [hq,Matrix.mulVec_zero,add_zero] at he
    refine Or.inl ⟨sectionMap (tW.mulVec (coordinates v)),?_⟩
    apply coordinateEquiv.injective
    change coordinates v = coordinates _
    rw [←displacement_apply,displacement_t,coordinates_section]
    exact he
  · rw [one_coset _ hq] at he
    refine Or.inr ⟨sectionMap (tW.mulVec (coordinates v)),?_⟩
    apply coordinateEquiv.injective
    change coordinates v = coordinates _
    rw [map_add,←displacement_apply,displacement_t,coordinates_section]
    change coordinates v = _ + coordinates (sectionMap (bits 20))
    rw [coordinates_section]
    exact he

end
end MathieuCode.J4Fusion.InvolutionCosets
