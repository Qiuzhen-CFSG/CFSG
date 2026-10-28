module
public import Theory.Mathieu.M12.ExceptionalParabolics
public import Theory.Mathieu.M12.ExceptionalParabolics.SourceRecognitionFirstBound

/-!
# Recognition of the nonsplit M₁₂ parabolic from source relations

The marked elementary eight has basis z, leftI*rightI, leftJ*rightJ. Three
explicit involutions act on it by the source formulas and lift the A₃ chain
in the S₄ quotient. The outside end product squares to z. Short words in
these six elements give the existing quaternion and quotient generators,
so they generate the actual first parabolic.

The general order bound is applied to paired source and model generators.
The two projections are surjective, and the model order together with the
source lower bound makes them bijective. This recognizes the endpoint without
assuming an extension isomorphism or separately classifying GL₂(3) covers.
Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.12.6)
and the following paragraph, printed p.405; compare the model in (3.8), p.390.
-/

public section
noncomputable section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
open Subgroup

private theorem first_leftI : leftI ∈ firstParabolic :=
  core_le_firstParabolic ((mem_core _).mpr ⟨.a 1,.a 0,by decide +kernel⟩)
private theorem first_leftJ : leftJ ∈ firstParabolic :=
  core_le_firstParabolic ((mem_core _).mpr ⟨.xa 0,.a 0,by decide +kernel⟩)
private theorem first_rightI : rightI ∈ firstParabolic :=
  core_le_firstParabolic ((mem_core _).mpr ⟨.a 0,.a 1,by decide +kernel⟩)
private theorem first_rightJ : rightJ ∈ firstParabolic :=
  core_le_firstParabolic ((mem_core _).mpr ⟨.a 0,.xa 0,by decide +kernel⟩)

def firstE : firstParabolic := ⟨leftI * rightI,mul_mem first_leftI first_rightI⟩
def firstF : firstParabolic := ⟨leftJ * rightJ,mul_mem first_leftJ first_rightJ⟩
def firstA : firstParabolic := firstE * ⟨FirstCore.secondSwap,FirstCore.secondSwap_mem⟩
def firstB : firstParabolic :=
  ⟨cubicActor ^ 2 * FirstCore.secondSwap,
    mul_mem (pow_mem cubicActor_mem _) FirstCore.secondSwap_mem⟩
def firstC : firstParabolic :=
  ⟨leftJ * FirstCore.secondSwap * rightJ,
    mul_mem (mul_mem first_leftJ FirstCore.secondSwap_mem) first_rightJ⟩
def firstZ : firstParabolic := ⟨z,core_le_firstParabolic z_mem_core⟩

private def firstGenerator (i : Fin 6) : firstParabolic :=
  ![firstE,firstF,firstA,firstB,firstC,firstZ] i
private def firstEvaluate : List (Fin 6) → firstParabolic
  | [] => 1
  | i :: w => firstGenerator i * firstEvaluate w
private def firstOldWord (i : Fin 6) : List (Fin 6) :=
  ![[2,3,4,2,3,2], [3,2,4,3], [0,2,3,2,4,3,2],
    [1,3,4,2,3], [0,3,4,0], [0,2]] i
private theorem firstOld_eq_word (i : Fin 6) :
    (![leftI,leftJ,rightI,rightJ,FirstCore.secondCycle,FirstCore.secondSwap] i : M12) =
      (firstEvaluate (firstOldWord i) : M12) := by
  fin_cases i <;> decide +kernel

/-- The compact source generators generate the actual involution centralizer. -/
theorem first_generation :
    closure ({firstE,firstF,firstA,firstB,firstC,firstZ} : Set firstParabolic) = ⊤ := by
  let K := closure ({firstE,firstF,firstA,firstB,firstC,firstZ} : Set firstParabolic)
  let N := K.map firstParabolic.subtype
  have hs (i : Fin 6) : firstGenerator i ∈ K := by
    fin_cases i <;> exact subset_closure (by simp [firstGenerator])
  have hw (w : List (Fin 6)) : firstEvaluate w ∈ K := by
    induction w with
    | nil => exact K.one_mem
    | cons i w ih => exact K.mul_mem (hs i) ih
  have ho (i : Fin 6) :
      (![leftI,leftJ,rightI,rightJ,FirstCore.secondCycle,FirstCore.secondSwap] i : M12) ∈ N := by
    rw [firstOld_eq_word]
    exact mem_map.mpr ⟨_,hw _,rfl⟩
  have hl : leftFactor ≤ N := by
    rintro _ ⟨q,rfl⟩
    cases q with
    | a n => exact N.pow_mem (ho 0) _
    | xa n => exact N.mul_mem (ho 1) (N.pow_mem (ho 0) _)
  have hr : rightFactor ≤ N := by
    rintro _ ⟨q,rfl⟩
    cases q with
    | a n => exact N.pow_mem (ho 2) _
    | xa n => exact N.mul_mem (ho 3) (N.pow_mem (ho 2) _)
  have h : firstParabolic ≤ N := FirstCore.firstParabolic_le_of_core_cycle_swap
    N (sup_le hl hr) (ho 4) (ho 5)
  apply top_unique
  intro g _
  obtain ⟨u,hu,he⟩ := mem_map.mp (h g.property)
  exact (Subtype.ext he : u = g) ▸ hu

theorem first_relations : FirstRelations firstE firstF firstA firstB firstC firstZ where
  e_sq := by apply Subtype.ext; decide +kernel
  f_sq := by apply Subtype.ext; decide +kernel
  A_sq := by apply Subtype.ext; decide +kernel
  B_sq := by apply Subtype.ext; decide +kernel
  C_sq := by apply Subtype.ext; decide +kernel
  z_sq := by apply Subtype.ext; decide +kernel
  ef := by change firstE * firstF = firstF * firstE; apply Subtype.ext; decide +kernel
  ze := by change firstZ * firstE = firstE * firstZ; apply Subtype.ext; decide +kernel
  zf := by change firstZ * firstF = firstF * firstZ; apply Subtype.ext; decide +kernel
  zA := by change firstZ * firstA = firstA * firstZ; apply Subtype.ext; decide +kernel
  zB := by change firstZ * firstB = firstB * firstZ; apply Subtype.ext; decide +kernel
  zC := by change firstZ * firstC = firstC * firstZ; apply Subtype.ext; decide +kernel
  AB := by apply Subtype.ext; decide +kernel
  BC := by apply Subtype.ext; decide +kernel
  AC := by apply Subtype.ext; decide +kernel
  Ae := by apply Subtype.ext; decide +kernel
  Af := by apply Subtype.ext; decide +kernel
  Be := by apply Subtype.ext; decide +kernel
  Bf := by apply Subtype.ext; decide +kernel
  Ce := by apply Subtype.ext; decide +kernel
  Cf := by apply Subtype.ext; decide +kernel

variable {G H : Type*} [Group G] [Group H]

theorem FirstRelations.prod {e f A B C z : G} {e' f' A' B' C' z' : H}
    (r : FirstRelations e f A B C z) (q : FirstRelations e' f' A' B' C' z') :
    FirstRelations (e,e') (f,f') (A,A') (B,B') (C,C') (z,z') where
  e_sq := Prod.ext r.e_sq q.e_sq
  f_sq := Prod.ext r.f_sq q.f_sq
  A_sq := Prod.ext r.A_sq q.A_sq
  B_sq := Prod.ext r.B_sq q.B_sq
  C_sq := Prod.ext r.C_sq q.C_sq
  z_sq := Prod.ext r.z_sq q.z_sq
  ef := Prod.ext r.ef.eq q.ef.eq
  ze := Prod.ext r.ze.eq q.ze.eq
  zf := Prod.ext r.zf.eq q.zf.eq
  zA := Prod.ext r.zA.eq q.zA.eq
  zB := Prod.ext r.zB.eq q.zB.eq
  zC := Prod.ext r.zC.eq q.zC.eq
  AB := Prod.ext r.AB q.AB
  BC := Prod.ext r.BC q.BC
  AC := Prod.ext r.AC q.AC
  Ae := Prod.ext r.Ae q.Ae
  Af := Prod.ext r.Af q.Af
  Be := Prod.ext r.Be q.Be
  Bf := Prod.ext r.Bf q.Bf
  Ce := Prod.ext r.Ce q.Ce
  Cf := Prod.ext r.Cf q.Cf

/-- The compact elementary-eight extension relations uniquely identify the
first endpoint once its independently obtained lower order bound is 192. -/
theorem firstParabolic_equiv_of_relations [Finite G] (e f A B C z : G)
    (r : FirstRelations e f A B C z)
    (hgen : closure ({e,f,A,B,C,z} : Set G) = ⊤) (hcard : 192 ≤ Nat.card G) :
    Nonempty (G ≃* firstParabolic) := by
  let D := closure ({(e,firstE),(f,firstF),(A,firstA),(B,firstB),(C,firstC),(z,firstZ)} :
    Set (G × firstParabolic))
  let p : D →* G := (MonoidHom.fst G firstParabolic).domRestrict D
  let q : D →* firstParabolic := (MonoidHom.snd G firstParabolic).domRestrict D
  have hp : Function.Surjective p := by
    apply MonoidHom.range_eq_top.mp
    dsimp only [p]
    rw [MonoidHom.domRestrict_range]
    dsimp only [D]
    rw [MonoidHom.map_closure]
    simpa only [Set.image_insert_eq, Set.image_singleton, MonoidHom.coe_fst, Prod.fst] using hgen
  have hq : Function.Surjective q := by
    apply MonoidHom.range_eq_top.mp
    dsimp only [q]
    rw [MonoidHom.domRestrict_range]
    dsimp only [D]
    rw [MonoidHom.map_closure]
    simpa only [Set.image_insert_eq, Set.image_singleton, MonoidHom.coe_snd, Prod.snd] using first_generation
  have hd : Nat.card D ≤ 192 := (r.prod first_relations).card_le
  let ep := MulEquiv.ofBijective p (hp.bijective_of_nat_card_le (hd.trans hcard))
  let eqv := MulEquiv.ofBijective q (hq.bijective_of_nat_card_le
    (by simpa only [card_firstParabolic] using hd))
  exact ⟨ep.symm.trans eqv⟩

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.SourceRecognition
