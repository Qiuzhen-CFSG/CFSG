module

public import Theory.SpecificGroups.LinearHigher.OddCharacteristicCover.CommutingRoots

/-!
# Coherent root lifts in an odd central cover of PSL₄

Define each root lift as a commutator through an auxiliary index. Commuting root
preimages give additivity. Diagonal involutions then give exact sign covariance;
for a chain of three roots, a fourth coordinate supplies a torus element that
inverts both candidate lifts. Odd-kernel rigidity identifies them, proving all
relations of the actual Steinberg presentation.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, Theorems 8–9 and the
special linear example; Aschbacher–Smith, the odd linear cover case of §A.2.
-/

open scoped commutatorElement MatrixGroups
namespace Theory.SpecificGroups.LinearHigher.OddCharacteristicCover
open Subgroup SteinbergWords CentralExtension.OddKernel
variable {E : Type*} [Group E] {p : ℕ} [Fact p.Prime]

private noncomputable def auxiliary (r : Root 4) : Fin 4 :=
  Classical.choose (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 4))

private theorem auxiliary_ne_left (r : Root 4) : auxiliary r ≠ r.val.1 :=
  (Classical.choose_spec (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 4))).1

private theorem auxiliary_ne_right (r : Root 4) : auxiliary r ≠ r.val.2 :=
  (Classical.choose_spec (Fin.exists_ne_and_ne_of_two_lt r.val.1 r.val.2 (by decide : 2 < 4))).2

private noncomputable def leftRoot (r : Root 4) : Root 4 :=
  root r.val.1 (auxiliary r) (auxiliary_ne_left r).symm

private noncomputable def rightRoot (r : Root 4) : Root 4 :=
  root (auxiliary r) r.val.2 (auxiliary_ne_right r)

private noncomputable def rootPreimage (f : E →* PSL(4,ZMod p)) (hf : Function.Surjective f)
    (r : Root 4) (a : ZMod p) : E := Classical.choose (hf (projectiveRoot r a))

private theorem rootPreimage_map (f : E →* PSL(4,ZMod p)) (hf : Function.Surjective f)
    (r : Root 4) (a : ZMod p) : f (rootPreimage f hf r a)=projectiveRoot r a :=
  Classical.choose_spec (hf _)

public noncomputable def rootLift (f : E →* PSL(4,ZMod p)) (hf : Function.Surjective f)
    (r : Root 4) (a : ZMod p) : E :=
  ⁅rootPreimage f hf (leftRoot r) a,rootPreimage f hf (rightRoot r) 1⁆

public theorem rootLift_map (f : E →* PSL(4,ZMod p)) (hf : Function.Surjective f)
    (r : Root 4) (a : ZMod p) : f (rootLift f hf r a)=projectiveRoot r a := by
  rw [rootLift,map_commutatorElement,rootPreimage_map,rootPreimage_map]
  simpa only [mul_one,leftRoot,rightRoot,show root r.val.1 r.val.2 r.property=r from Subtype.ext rfl] using projectiveRoot_relations.chain
    r.val.1 (auxiliary r) r.val.2 (auxiliary_ne_left r).symm (auxiliary_ne_right r) r.property a (1:ZMod p)

variable (f : E →* PSL(4,ZMod p)) (hf : Function.Surjective f)
  (hc : f.ker ≤ center E) (hcop : (Nat.card f.ker).Coprime 2)
include hc hcop

private theorem preimage_commutes_left_lift (r : Root 4) (a b : ZMod p) :
    Commute (rootPreimage f hf (leftRoot r) a) (rootLift f hf r b) :=
  commuting_root_preimages f hf hc hcop (leftRoot r) r a b
    (rootPreimage_map _ _ _ _) (rootLift_map _ _ _ _) (auxiliary_ne_left r) r.property.symm

private theorem preimage_commutes_right_lift (r : Root 4) (a b : ZMod p) :
    Commute (rootPreimage f hf (rightRoot r) a) (rootLift f hf r b) :=
  commuting_root_preimages f hf hc hcop (rightRoot r) r a b
    (rootPreimage_map _ _ _ _) (rootLift_map _ _ _ _) r.property.symm (auxiliary_ne_right r).symm

private theorem rootLift_add (r : Root 4) (a b : ZMod p) :
    rootLift f hf r a * rootLift f hf r b=rootLift f hf r (a+b) := by
  have hh : rootLift f hf r (a+b)=rootLift f hf r b*rootLift f hf r a := by
    unfold rootLift
    rw [CentralExtension.commutator_eq_of_image_eq f hc (x':=
      rootPreimage f hf (leftRoot r) a*rootPreimage f hf (leftRoot r) b)
      (by rw [rootPreimage_map,map_mul,rootPreimage_map,rootPreimage_map,
        projectiveRoot_relations.add]) rfl,
      commutatorElement_mul_left_eq_conj_mul]
    change rootPreimage f hf (leftRoot r) a * rootLift f hf r b *
      (rootPreimage f hf (leftRoot r) a)⁻¹ * rootLift f hf r a = _
    rw [(preimage_commutes_left_lift f hf hc hcop r a b).eq,mul_inv_cancel_right]
    rfl
  rw [hh]
  exact (commuting_root_preimages f hf hc hcop r r a b
    (rootLift_map _ _ _ _) (rootLift_map _ _ _ _) r.property.symm r.property.symm).eq

omit hc hcop in
private theorem neg_one_ne_one (hp2 : p ≠ 2) : (-1:ZMod p) ≠ 1 := by
  intro he
  have h2 : (2:ZMod p)=0 := by linear_combination -he
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 p).mp h2))

private theorem rootLift_conj_torus (hp2 : p ≠ 2) (i j : Fin 4) (hij : i ≠ j)
    {t : E} (ht : f t=torusWord projectiveRoot i j hij (-1)) (r : Root 4) (a : ZMod p) :
    t*rootLift f hf r a*t⁻¹ =
      if (rootWeight i j (-1 : (ZMod p)ˣ) r : ZMod p)=1 then rootLift f hf r a
      else (rootLift f hf r a)⁻¹ := by
  classical
  obtain ⟨sx,hsx⟩ := rootWeight_sign (F:=ZMod p) i j (leftRoot r)
  obtain ⟨sy,hsy⟩ := rootWeight_sign (F:=ZMod p) i j (rightRoot r)
  have hconj (s : Root 4) (b : ZMod p) :
      f (t*rootPreimage f hf s b*t⁻¹)=
        projectiveRoot s ((rootWeight i j (-1 : (ZMod p)ˣ) s : ZMod p)*b) := by
    rw [map_mul,map_mul,map_inv,ht,rootPreimage_map,← MulAut.conj_apply,
      torusWord_conj_generator projectiveRoot_relations (by decide)]
  have hx : f (t*rootPreimage f hf (leftRoot r) a*t⁻¹)=
      f (if sx then (rootPreimage f hf (leftRoot r) a)⁻¹ else rootPreimage f hf (leftRoot r) a) := by
    rw [hconj,hsx]
    cases sx <;> simp [map_inv,rootPreimage_map,projectiveRoot_relations.neg]
  have hy : f (t*rootPreimage f hf (rightRoot r) 1*t⁻¹)=
      f (if sy then (rootPreimage f hf (rightRoot r) 1)⁻¹ else rootPreimage f hf (rightRoot r) 1) := by
    rw [hconj,hsy]
    cases sy <;> simp [map_inv,rootPreimage_map,projectiveRoot_relations.neg]
  have he := conjugate_commutator_of_signs f hc
    (preimage_commutes_left_lift f hf hc hcop r a a)
    (preimage_commutes_right_lift f hf hc hcop r 1 a) sx sy hx hy
  have hw : (rootWeight i j (-1 : (ZMod p)ˣ) r : ZMod p)=
      (if sx then -1 else 1)*(if sy then -1 else 1) := by
    have hh := rootWeight_chain r.val.1 (auxiliary r) r.val.2 i j
      (auxiliary_ne_left r).symm (auxiliary_ne_right r) r.property (-1 : (ZMod p)ˣ)
    change (rootWeight i j (-1 : (ZMod p)ˣ) (leftRoot r) : ZMod p)*
      (rootWeight i j (-1 : (ZMod p)ˣ) (rightRoot r) : ZMod p)=_ at hh
    rw [hsx,hsy] at hh
    exact hh.symm
  change t*rootLift f hf r a*t⁻¹=if sx=sy then rootLift f hf r a else (rootLift f hf r a)⁻¹ at he
  rw [hw]
  cases sx <;> cases sy <;> simpa [neg_one_ne_one hp2] using he

private theorem rootLift_chain (hp2 : p ≠ 2) (i j k : Fin 4)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : ZMod p) :
    ⁅rootLift f hf (root i j hij) a,rootLift f hf (root j k hjk) b⁆=
      rootLift f hf (root i k hik) (a*b) := by
  obtain ⟨l,hli,hlj,hlk⟩ := exists_fourth i j k
  obtain ⟨t,ht⟩ := hf (torusWord projectiveRoot i l hli.symm (-1))
  have hx : t*rootLift f hf (root i j hij) a*t⁻¹=(rootLift f hf (root i j hij) a)⁻¹ := by
    rw [rootLift_conj_torus f hf hc hcop hp2 i l hli.symm ht]
    simp [rootWeight,torusWeight,root,hij.symm,hlj.symm,neg_one_ne_one hp2]
  have hy : t*rootLift f hf (root j k hjk) b*t⁻¹=rootLift f hf (root j k hjk) b := by
    rw [rootLift_conj_torus f hf hc hcop hp2 i l hli.symm ht]
    simp [rootWeight,torusWeight,root,hij.symm,hik.symm,hlj.symm,hlk.symm]
  have hz : t*rootLift f hf (root i k hik) (a*b)*t⁻¹=(rootLift f hf (root i k hik) (a*b))⁻¹ := by
    rw [rootLift_conj_torus f hf hc hcop hp2 i l hli.symm ht]
    simp [rootWeight,torusWeight,root,hik.symm,hlk.symm,neg_one_ne_one hp2]
  have hm : f ⁅rootLift f hf (root i j hij) a,rootLift f hf (root j k hjk) b⁆=
      projectiveRoot (root i k hik) (a*b) := by
    rw [map_commutatorElement,rootLift_map,rootLift_map,
      projectiveRoot_relations.chain i j k hij hjk hik]
  apply eq_of_image_eq_of_inverted f hc hcop (hm.trans (rootLift_map _ _ _ _).symm) ?_ hz
  rw [conjugate_commutatorElement,hx,hy]
  apply commutator_inv_left_of_commute
  exact commuting_root_preimages f hf hc hcop (root i j hij) (root i k hik) a (a*b)
    (rootLift_map _ _ _ _) hm hij.symm hik.symm

public theorem rootLift_relations (hp2 : p ≠ 2) : Relations (rootLift f hf) where
  add := rootLift_add f hf hc hcop
  distant r s a b hrs hsr := (commuting_root_preimages f hf hc hcop r s a b
    (rootLift_map _ _ _ _) (rootLift_map _ _ _ _) hrs hsr).commutator_eq
  chain := rootLift_chain f hf hc hcop hp2

end Theory.SpecificGroups.LinearHigher.OddCharacteristicCover