module
public import Theory.ElementaryAbelian.Basic
public import Theory.SpecificGroups.SymmetricEight.SmallOrbitCertificate
public import Theory.Representation.BinaryPermutation.OrbitSizeSeparation
public import Theory.SpecificGroups.SymmetricEight.InvolutionActions
/-!
# Small-orbit movement in the binary eight-point augmentation core

Every elementary S8 actor of order at least eight has two vectors with
orbits of size at most four whose displacements under one actor add to
weight two or eight. The reduced Sylow certificate proves this in tree
coordinates; Sylow conjugacy transports both vectors and the same actor.
Every nonidentity involution also has an unrestricted displacement of
weight two or eight. These facts retain the full constant line and feed
the literal centralizer-span argument of source 12.6.22.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, p.829.
-/

@[expose] public section
open Subgroup BinaryPermutation
open BinaryPermutation.EightNonsingular
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace BinaryPermutation.EightSmallOrbits

/-- The actual orbit of a vector under the specified permutation subgroup. -/
def SmallOrbit (A : Subgroup S) (v : C) : Prop :=
  Nat.card (Set.range fun a : A => coreRepresentation (Fin 8) a.val v) ≤ 4

private theorem smallOrbit_of_cover {A : Subgroup S} {v : C} (c : Fin 4 → C)
    (hc : ∀ a : A, ∃ i, coreRepresentation (Fin 8) a.val v = c i) : SmallOrbit A v := by
  classical
  let X := Set.range fun a : A => coreRepresentation (Fin 8) a.val v
  have hh (x : X) : ∃ i, x.val = c i := by
    obtain ⟨a,ha⟩ := x.property
    obtain ⟨i,hi⟩ := hc a
    exact ⟨i,ha.symm.trans hi⟩
  let f : X → Fin 4 := fun x => (hh x).choose
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact (hh x).choose_spec.trans ((congrArg c h).trans (hh y).choose_spec.symm)
  exact (Nat.card_le_card_of_injective f hf).trans (by simp)

/-- The reduced Sylow calculation. Only twelve exceptional words survive
commuting-involution tests; closure reduces these to the even pair group. -/
theorem large_tree_witness (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hle : A ≤ treeGroup) (hcard : 8 ≤ Nat.card A) :
    ∃ a ∈ A, ∃ v w : C, SmallOrbit A v ∧ SmallOrbit A w ∧
      (let d := coreRepresentation (Fin 8) a v + v +
        (coreRepresentation (Fin 8) a w + w)
       hammingNorm d.val = 2 ∨ hammingNorm d.val = 8) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hex (a : A) : ∃ i : Fin 128, treeWord i = a.val :=
    (mem_treeGroup _).mp (hle a.property)
  let f : A → Fin 128 := fun a => (hex a).choose
  have hf (a : A) : treeWord (f a) = a.val := (hex a).choose_spec
  have hfi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    rw [← hf a, ← hf b,h]
  let P := Finset.univ.image f
  have hP : 8 ≤ P.card := by
    rw [Finset.card_image_of_injective _ hfi]
    simpa only [Finset.card_univ,Nat.card_eq_fintype_card] using hcard
  have hmem {i} (hi : i ∈ P) : treeWord i ∈ A := by
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
    rw [hf]
    exact a.property
  have hall (a : A) : f a ∈ P := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hm {i j} (hi : i ∈ P) (hj : j ∈ P) :
      treeWord i * treeWord j = treeWord j * treeWord i :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm
      ⟨_,hmem hi⟩ ⟨_,hmem hj⟩)
  by_cases hp : ∃ i ∈ P, i ∉ bad
  · obtain ⟨i,hi,hbad⟩ := hp
    obtain ⟨j,hj⟩ := (involution_cover i
      (elemPow_eq_one_of_isElementaryAbelian _ (hmem hi))).resolve_left hbad
    subst i
    refine ⟨treeWord (actors j),hmem hi,first j,second j,?_,?_,(rows j).2⟩
    · apply smallOrbit_of_cover (firstCover j)
      intro a
      have hh := ((rows j).1 (f a)
        (hf a ▸ elemPow_eq_one_of_isElementaryAbelian _ a.property)
        (hm (hall a) hi)).1
      simpa only [hf] using hh
    · apply smallOrbit_of_cover (secondCover j)
      intro a
      have hh := ((rows j).1 (f a)
        (hf a ▸ elemPow_eq_one_of_isElementaryAbelian _ a.property)
        (hm (hall a) hi)).2
      simpa only [hf] using hh
  · push Not at hp
    have hno : ∀ i ∈ P, i ∉ exceptional := by
      intro i hi hie
      obtain ⟨j,hj⟩ := exceptional_exhaustive i hie
      subst i
      have hsub : P ⊆ Finset.univ.image (exceptionalCover j) := by
        intro k hk
        let a : A := ⟨treeWord k * treeWord (exceptionalActor j),
          A.mul_mem (hmem hk) (hmem hi)⟩
        obtain ⟨b,hb⟩ := bad_index k (hp k hk)
        obtain ⟨c,hc⟩ := bad_index (f a) (hp _ (hall a))
        obtain ⟨r,hr⟩ := exceptional_small j b (hb.symm ▸ hm hk hi)
          ⟨c,by rw [hb,hc]; exact (hf a).symm⟩
        rw [hb] at hr
        exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,hr.symm⟩
      have hsmall := (Finset.card_le_card hsub).trans (Finset.card_image_le)
      have hfour : (Finset.univ : Finset (Fin 4)).card = 4 := by simp
      omega
    have hsub : P ⊆ base := by
      intro i hi
      exact (bad_split i (hp i hi)).resolve_right (hno i hi)
    have he : P = base := Finset.eq_of_subset_of_card_le hsub
      ((by decide : base.card = 8) ▸ hP)
    have h15 : (15 : Fin 128) ∈ P := he.symm ▸ (by decide : (15 : Fin 128) ∈ base)
    refine ⟨treeWord 15,hmem h15,finalFirst,finalSecond,?_,?_,Or.inr final_weight⟩
    · apply smallOrbit_of_cover finalFirstCover
      intro a
      simpa only [hf] using (final_covers (f a) (hsub (hall a))).1
    · apply smallOrbit_of_cover finalSecondCover
      intro a
      simpa only [hf] using (final_covers (f a) (hsub (hall a))).2

private theorem action_conj (g a : S) (v : C) :
    coreRepresentation (Fin 8) (MulAut.conj g a) (coreRepresentation (Fin 8) g v) =
      coreRepresentation (Fin 8) g (coreRepresentation (Fin 8) a v) := by
  have h : MulAut.conj g a * g = g * a := by simp [MulAut.conj_apply,mul_assoc]
  simpa only [map_mul,Module.End.mul_apply] using
    congrArg (fun p => coreRepresentation (Fin 8) p v) h

private theorem smallOrbit_conj (g : S) (A : Subgroup S) (v : C) :
    SmallOrbit (A.map (MulAut.conj g).toMonoidHom) (coreRepresentation (Fin 8) g v) ↔
      SmallOrbit A v := by
  let f := coreRepresentation (Fin 8) g
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (coreRepresentation (Fin 8) g⁻¹) h
    change coreRepresentation (Fin 8) g⁻¹ (coreRepresentation (Fin 8) g x) =
      coreRepresentation (Fin 8) g⁻¹ (coreRepresentation (Fin 8) g y) at hh
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using hh
  have he : (Set.range fun a : A.map (MulAut.conj g).toMonoidHom =>
      coreRepresentation (Fin 8) a.val (f v)) =
      f '' (Set.range fun a : A => coreRepresentation (Fin 8) a.val v) := by
    ext w
    constructor
    · rintro ⟨⟨_,a,ha,rfl⟩,rfl⟩
      exact ⟨_,⟨⟨a,ha⟩,rfl⟩,(action_conj g a v).symm⟩
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨⟨_,mem_map_of_mem _ a.property⟩,action_conj g a v⟩
  unfold SmallOrbit
  rw [he,Nat.card_image_of_injective hf]

/-- Every elementary eight-point actor of order at least eight moves two
vectors with orbits of size at most four to total weight two or eight.
The same actor occurs in both displacements. -/
theorem large_actor_witness (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hcard : 8 ≤ Nat.card A) :
    ∃ a ∈ A, ∃ v w : C, SmallOrbit A v ∧ SmallOrbit A w ∧
      (let d := coreRepresentation (Fin 8) a v + v +
        (coreRepresentation (Fin 8) a w + w)
       hammingNorm d.val = 2 ∨ hammingNorm d.val = 8) := by
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S P treeSylow
  let e := MulAut.conj g
  let B := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hP : (P : Subgroup S).map e.toMonoidHom = treeGroup := by
    change ((g • P : Sylow 2 S) : Subgroup S) = treeGroup
    rw [hg,treeSylow_coe]
  have hB : B ≤ treeGroup := hP ▸ map_mono hAP
  have hb : 8 ≤ Nat.card B := by rw [card_map_of_injective e.injective]; exact hcard
  obtain ⟨a,⟨a,ha,rfl⟩,v,w,hv,hw,hd⟩ := large_tree_witness B hB hb
  let v' := coreRepresentation (Fin 8) g⁻¹ v
  let w' := coreRepresentation (Fin 8) g⁻¹ w
  have hv' : coreRepresentation (Fin 8) g v' = v := by
    simp only [v',←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  have hw' : coreRepresentation (Fin 8) g w' = w := by
    simp only [w',←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  refine ⟨a,ha,v',w',?_,?_,?_⟩
  · exact (smallOrbit_conj g A v').mp (hv'.symm ▸ hv)
  · exact (smallOrbit_conj g A w').mp (hw'.symm ▸ hw)
  have he : coreRepresentation (Fin 8) (e a) v + v +
      (coreRepresentation (Fin 8) (e a) w + w) =
      coreRepresentation (Fin 8) g
        (coreRepresentation (Fin 8) a v' + v' + (coreRepresentation (Fin 8) a w' + w')) := by
    rw [map_add,map_add,map_add,←action_conj g a v',←action_conj g a w',hv',hw']
  change hammingNorm (coreRepresentation (Fin 8) (e a) v + v +
    (coreRepresentation (Fin 8) (e a) w + w)).val = 2 ∨
    hammingNorm (coreRepresentation (Fin 8) (e a) v + v +
    (coreRepresentation (Fin 8) (e a) w + w)).val = 8 at hd
  rw [he] at hd
  simpa only [show ∀ u : C, hammingNorm (coreRepresentation (Fin 8) g u).val =
    hammingNorm u.val from fun u => wordWeight_permute g u.val] using hd

private theorem weight_conj {a b : S} (hab : IsConj a b)
    (hb : ∃ v : C, hammingNorm (coreRepresentation (Fin 8) b v + v).val = 2 ∨
      hammingNorm (coreRepresentation (Fin 8) b v + v).val = 8) :
    ∃ v : C, hammingNorm (coreRepresentation (Fin 8) a v + v).val = 2 ∨
      hammingNorm (coreRepresentation (Fin 8) a v + v).val = 8 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hab.symm
  obtain ⟨v,hv⟩ := hb
  refine ⟨coreRepresentation (Fin 8) g v,?_⟩
  have he : coreRepresentation (Fin 8) a (coreRepresentation (Fin 8) g v) +
      coreRepresentation (Fin 8) g v =
      coreRepresentation (Fin 8) g (coreRepresentation (Fin 8) b v + v) := by
    rw [map_add,←action_conj g b v]
    exact congrArg (fun t => coreRepresentation (Fin 8) t (coreRepresentation (Fin 8) g v) +
      coreRepresentation (Fin 8) g v) hg.symm
  rw [he]
  simpa only [show ∀ u : C, hammingNorm (coreRepresentation (Fin 8) g u).val =
    hammingNorm u.val from fun u => wordWeight_permute g u.val] using hv

/-- Every nonidentity involution has a displacement of weight two or eight
on the full augmentation core, retaining the constant line. -/
theorem involution_displacement (a : S) (ha : a^2 = 1) (hne : a ≠ 1) :
    ∃ v : C, hammingNorm (coreRepresentation (Fin 8) a v + v).val = 2 ∨
      hammingNorm (coreRepresentation (Fin 8) a v + v).val = 8 := by
  have ho : orderOf a = 2 := orderOf_eq_prime ha hne
  rcases Theory.SpecificGroups.SymmetricEight.Involutions.involution_conjugacy ho with
    h | h | h | h
  · exact weight_conj h ⟨pair 0 2,Or.inl (by decide +kernel)⟩
  · exact weight_conj h ⟨pair 0 4,Or.inl (by decide +kernel)⟩
  · exact weight_conj h ⟨pair 0 6,Or.inl (by decide +kernel)⟩
  · exact weight_conj h ⟨pair 0 2 + pair 4 6,Or.inr (by decide +kernel)⟩

end BinaryPermutation.EightSmallOrbits
