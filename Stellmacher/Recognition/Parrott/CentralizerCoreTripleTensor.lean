module

public import Stellmacher.Recognition.Parrott.CentralizerCoreCoordinatesData
public import Theory.GroupTheory.Commutator.ThirdInverseConvention

/-!
# The actual core triple commutator in binary coordinates

The central third commutator is multiplicative in each variable. Transport it
from the intrinsic core to its literal ambient image and compare it with the
binary tensor on the supplied four generators, using the actual bracket and
derived pairing tables. This realizes the tensor without assuming a model or
constructing coordinates.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.678–681, equations (2), (3), (5), (10)–(15), and (23).
-/

open scoped commutatorElement IsMulCommutative
open Subgroup
variable {G : Type*} [Group G]

open Theory.GroupAction.BinaryFourTripleOrientation

private def bitPower (z : G) (hz : z ^ 2 = 1) :
    Multiplicative (ZMod 2) →* zpowers z where
  toFun x := ⟨z ^ x.toAdd.val, pow_mem (mem_zpowers z) _⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    change z ^ (x.toAdd + y.toAdd).val = z ^ x.toAdd.val * z ^ y.toAdd.val
    have hb : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    have h11 : (1+1 : ZMod 2) = 0 := by decide
    rcases hb x.toAdd with hx | hx <;> rcases hb y.toAdd with hy | hy <;>
      simp [hx, hy, h11, ZMod.val_one, ← pow_two, hz]

private def tensorHom :
    Multiplicative V →* (Multiplicative V →* (Multiplicative V →* Multiplicative (ZMod 2))) where
  toFun x := {
    toFun := fun y => {
      toFun := fun z => Multiplicative.ofAdd (tensor x.toAdd y.toAdd z.toAdd)
      map_one' := by apply Multiplicative.toAdd.injective; simp [tensor, pairing]
      map_mul' := by
        intro z w
        change tensor x.toAdd y.toAdd (z.toAdd+w.toAdd) =
          tensor x.toAdd y.toAdd z.toAdd + tensor x.toAdd y.toAdd w.toAdd
        simp only [tensor, pairing, Pi.add_apply]
        ring }
    map_one' := by ext z; simp [tensor, pairing, bracket]
    map_mul' := by
      intro y w
      apply MonoidHom.ext
      intro z
      change tensor x.toAdd (y.toAdd+w.toAdd) z.toAdd =
        tensor x.toAdd y.toAdd z.toAdd + tensor x.toAdd w.toAdd z.toAdd
      simp only [tensor, pairing, bracket, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.add_apply]
      ring }
  map_one' := by ext y z; simp [tensor, pairing, bracket]
  map_mul' := by
    intro x w
    apply MonoidHom.ext
    intro y
    apply MonoidHom.ext
    intro z
    change tensor (x.toAdd+w.toAdd) y.toAdd z.toAdd =
      tensor x.toAdd y.toAdd z.toAdd + tensor w.toAdd y.toAdd z.toAdd
    simp only [tensor, pairing, bracket, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.add_apply]
    ring

namespace Stellmacher.Recognition
open Theory.GroupAction.BinaryFourTripleOrientation
variable {z : G} {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
variable (f : ParrottSylowGeneratorData n)

private theorem core_triple_hom [Finite G] (h : ParrottCentralizerHypotheses z) :
    ∃ F : ParrottCore.Core z →* (ParrottCore.Core z →*
      (ParrottCore.Core z →* zpowers z)),
    ∀ x y w, (F x y w : G) =
      Tits.parrottCommutator (Tits.parrottCommutator (x:G) (y:G)) (w:G) := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let ι : J →* G := H.subtype.comp J.subtype
  let E : J ≃* ParrottCore.Core z := J.equivMapOfInjective H.subtype H.subtype_injective
  obtain ⟨hZ, _, _, _, hU, _, _, _⟩ := parrott_centralizer_structure z h
  have hc : ⁅commutator J, (⊤ : Subgroup J)⁆ ≤ center J := by
    rw [hU]
    simpa using commutator_upperCentralSeries_top_le J 1
  obtain ⟨F, hF⟩ := Subgroup.exists_inverse_first_third_commutator_hom hc
  let ψ : center J →* zpowers z := (ι.comp (center J).subtype).codRestrict _ (by
    intro x
    rw [← hZ]
    exact mem_map_of_mem ι x.property)
  let F' : ParrottCore.Core z →* (ParrottCore.Core z →*
      (ParrottCore.Core z →* zpowers z)) := {
    toFun := fun x => {
      toFun := fun y => ψ.comp ((F (E.symm x) (E.symm y)).comp E.symm.toMonoidHom)
      map_one' := by ext w; simp
      map_mul' := by intro y y'; ext w; simp }
    map_one' := by ext y w; simp
    map_mul' := by intro x x'; ext y w; simp }
  refine ⟨F', ?_⟩
  intro x y w
  have he (x : ParrottCore.Core z) : ι (E.symm x) = (x : G) := by
    exact congrArg Subtype.val (E.apply_symm_apply x)
  change ι (F (E.symm x) (E.symm y) (E.symm w)) = _
  rw [hF]
  simp only [Tits.parrottCommutator, map_mul, map_inv, he]

private def generators (i : Fin 4) : ParrottCore.Core z :=
  ⟨![f.a,f.b,f.c,f.d] i, by
    have hm := f.core_orientation_mem_core
    fin_cases i <;> simp_all⟩

private theorem hom_ext {C : Type*} [Group C] (F F' : ParrottCore.Core z →* C)
    (hh : ∀ i, F (generators f i) = F' (generators f i)) : F = F' := by
  have hle : ParrottCore.Core z ≤ (F.eqLocus F').map (ParrottCore.Core z).subtype := by
    apply f.core_generators.ge.trans

    apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨generators f 0, hh 0, rfl⟩
    · exact ⟨generators f 1, hh 1, rfl⟩
    · exact ⟨generators f 2, hh 2, rfl⟩
    · exact ⟨generators f 3, hh 3, rfl⟩
  ext x
  obtain ⟨y, hy, he⟩ := hle x.property
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy

private theorem map_generators (q : ParrottCore.Coordinates f) (i : Fin 4) :
    (q.toHom (generators f i)).toAdd =
      (![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]] i : V) := by
  fin_cases i
  · exact q.map_a _ rfl
  · exact q.map_b _ rfl
  · exact q.map_c _ rfl
  · exact q.map_d _ rfl

private def coordinateTensor (q : ParrottCore.Coordinates f) :
    ParrottCore.Core z →* (ParrottCore.Core z →* (ParrottCore.Core z →* zpowers z)) where
  toFun x := {
    toFun := fun y => (bitPower z f.z_sq).comp
      ((tensorHom (q.toHom x) (q.toHom y)).comp q.toHom)
    map_one' := by ext w; simp
    map_mul' := by intro y y'; ext w; simp }
  map_one' := by ext y w; simp
  map_mul' := by intro x x'; ext y w; simp

private theorem reverse (x y : G) :
    Tits.parrottCommutator x y = (Tits.parrottCommutator y x)⁻¹ := by
  simp only [Tits.parrottCommutator, mul_inv_rev, inv_inv]
  group

private theorem mul_left (x y w : G) :
    Tits.parrottCommutator (x*y) w =
      y⁻¹ * Tits.parrottCommutator x w * y * Tits.parrottCommutator y w := by
  simp only [Tits.parrottCommutator]
  group

set_option linter.unusedSimpArgs false in
private theorem generator_triple (i j k : Fin 4) :
    Tits.parrottCommutator
      (Tits.parrottCommutator (![f.a,f.b,f.c,f.d] i) (![f.a,f.b,f.c,f.d] j))
      (![f.a,f.b,f.c,f.d] k) =
    z ^ (tensor
      (![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]] i)
      (![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]] j)
      (![![1,0,0,0], ![0,1,0,0], ![0,0,1,0], ![0,0,0,1]] k)).val := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using f.z_sq)
  have hp (k r : Fin 4) :
      Tits.parrottCommutator (![n.t,n.v,f.u,f.w] r) (![f.a,f.b,f.c,f.d] k) =
      z ^ (if k.val + r.val = 3 then 1 else 0) := by
    rw [reverse, f.core_derived_pairing_entries]
    split_ifs <;> simp [hz]
  have hp0 := hp k 0
  have hp1 := hp k 1
  have hp2 := hp k 2
  have hp3 := hp k 3
  change Tits.parrottCommutator n.t _ = _ at hp0
  change Tits.parrottCommutator n.v _ = _ at hp1
  change Tits.parrottCommutator f.u _ = _ at hp2
  change Tits.parrottCommutator f.w _ = _ at hp3
  rw [f.core_bracket_entries]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] at hp0 hp1 hp2 hp3 ⊢ <;>
    simp -failIfUnchanged only [mul_left, hp0, hp1, hp2, hp3] <;>
    norm_num [tensor, pairing, bracket, ZMod.val_one, Tits.parrottCommutator,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      f.comm_zt.symm.inv_left.eq, f.comm_zv.symm.inv_left.eq,
      f.comm_zu.symm.inv_left.eq, f.comm_zw.symm.inv_left.eq, mul_assoc]

/-- The binary tensor evaluates the actual inverse-first triple commutator on
the supplied core coordinates. No coordinate-existence assumption is hidden. -/
public theorem ParrottSylowGeneratorData.core_triple_tensor [Finite G]
    (f : ParrottSylowGeneratorData n) (h : ParrottCentralizerHypotheses z)
    (q : ParrottCore.Coordinates f) (g k l : ParrottCore.Core z) :
    Tits.parrottCommutator (Tits.parrottCommutator (g : G) (k : G)) (l : G) =
      z ^ (tensor (q.toHom g).toAdd (q.toHom k).toAdd (q.toHom l).toAdd).val := by
  obtain ⟨F, hF⟩ := core_triple_hom h
  have he : F = coordinateTensor f q := by
    apply hom_ext f
    intro i
    apply hom_ext f
    intro j
    apply hom_ext f
    intro k
    apply Subtype.ext
    rw [hF]
    change Tits.parrottCommutator
        (Tits.parrottCommutator (![f.a,f.b,f.c,f.d] i) (![f.a,f.b,f.c,f.d] j))
        (![f.a,f.b,f.c,f.d] k) =
      z ^ (tensor (q.toHom (generators f i)).toAdd
        (q.toHom (generators f j)).toAdd (q.toHom (generators f k)).toAdd).val
    rw [map_generators, map_generators, map_generators]
    exact generator_triple f i j k
  rw [← hF, he]
  rfl

/-- The triple commutator descends through the actual derived core in every
variable, using equality of the supplied coordinates. -/
public theorem ParrottSylowGeneratorData.core_triple_eq_of_derived_cosets [Finite G]
    (f : ParrottSylowGeneratorData n) (h : ParrottCentralizerHypotheses z)
    (q : ParrottCore.Coordinates f) (g g' k k' l l' : ParrottCore.Core z)
    (hg : (g : G)⁻¹ * (g' : G) ∈ ParrottCore.Derived z)
    (hk : (k : G)⁻¹ * (k' : G) ∈ ParrottCore.Derived z)
    (hl : (l : G)⁻¹ * (l' : G) ∈ ParrottCore.Derived z) :
    Tits.parrottCommutator (Tits.parrottCommutator (g : G) (k : G)) (l : G) =
      Tits.parrottCommutator (Tits.parrottCommutator (g' : G) (k' : G)) (l' : G) := by
  rw [f.core_triple_tensor h q, f.core_triple_tensor h q,
    (q.eq_iff g g').mpr hg, (q.eq_iff k k').mpr hk, (q.eq_iff l l').mpr hl]

end Stellmacher.Recognition
