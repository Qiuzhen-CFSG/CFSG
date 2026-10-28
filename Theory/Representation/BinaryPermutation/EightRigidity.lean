module
public import Theory.Representation.BinaryPermutation.EightRigidityCertificate
public import Theory.ElementaryAbelian.Basic

/-!
# Corank-two moved-vector detection on the natural S8 module

Every nontrivial elementary actor moves a vector in an orbit of size at
most four. The small tree-word certificates give this in a Sylow subgroup;
Sylow conjugacy transports the same actor and vector. The displacement is
checked before and after quotienting by the constant line.

The vector stabilizer therefore has corank at most two and a fixed space
strictly larger than that of the whole actor. This is the intrinsic input
to Aschbacher--Smith 12.6.28(1), printed p.834; the original group pullback
is supplied in Chapter12.Section06.NaturalSource.WeakClosureZero.
-/

public section
open Subgroup BinaryPermutation BinaryPermutation.EightNonsingular
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace BinaryPermutation.EightRigidity
abbrev S := Equiv.Perm (Fin 8)
abbrev N := natural (Fin 8)

/-- The actual vector orbit for the natural six-dimensional action. -/
@[expose] def SmallOrbit (A : Subgroup S) (v : N) : Prop :=
  Nat.card (Set.range fun a : A => naturalRepresentation (Fin 8) a.val v) ≤ 4

private theorem smallOrbit_of_cover {A : Subgroup S} {v : N} (c : Fin 4 → N)
    (hc : ∀ a : A, ∃ i, naturalRepresentation (Fin 8) a.val v = c i) : SmallOrbit A v := by
  classical
  let X := Set.range fun a : A => naturalRepresentation (Fin 8) a.val v
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

private theorem projected_moved (a : S) (v : core (Fin 8))
    (hzero : (coreRepresentation (Fin 8) a v - v).val ≠ 0)
    (hone : (coreRepresentation (Fin 8) a v - v).val ≠ allOne (Fin 8)) :
    naturalRepresentation (Fin 8) a (coreToNatural (Fin 8) v) ≠ coreToNatural (Fin 8) v := by
  intro he
  have hz : coreToNatural (Fin 8) (coreRepresentation (Fin 8) a v - v) = 0 := by
    rw [map_sub,coreToNatural_equivariant,he,sub_self]
  exact ((EightGeometry.coreToNatural_eq_zero _).mp hz).elim hzero hone

private theorem tree_witness (A : Subgroup S) [IsElementaryAbelian 2 A]
    (hle : A ≤ treeGroup) (hne : A ≠ ⊥) :
    ∃ a ∈ A, ∃ v : N, SmallOrbit A v ∧ naturalRepresentation (Fin 8) a v ≠ v := by
  classical
  have hi (a : A) : ∃ i, treeWord i = a.val := (mem_treeGroup _).mp (hle a.property)
  by_cases hgood : ∃ j : Fin 42, treeWord (EightRigidityCertificate.actors j) ∈ A
  · obtain ⟨j,hj⟩ := hgood
    have hr := EightRigidityCertificate.rows j
    refine ⟨_,hj,coreToNatural (Fin 8) (EightRigidityCertificate.vector j),?_,
      projected_moved _ _ hr.2.1 hr.2.2⟩
    apply smallOrbit_of_cover (fun k => coreToNatural (Fin 8) (EightRigidityCertificate.cover j k))
    intro a
    obtain ⟨i,he⟩ := hi a
    have hp : (treeWord i)^2 = 1 := he.symm ▸ elemPow_eq_one_of_isElementaryAbelian _ a.property
    have hc : treeWord i * treeWord (EightRigidityCertificate.actors j) =
        treeWord (EightRigidityCertificate.actors j) * treeWord i := by
      rw [he]
      exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm a ⟨_,hj⟩)
    obtain ⟨k,hk⟩ := hr.1 i hp hc
    refine ⟨k,?_⟩
    rw [←he,←coreToNatural_equivariant,hk]
  · have hall (a : A) : ∃ i : Fin 128, treeWord i = a.val ∧ (i = 0 ∨ i = 15) := by
      obtain ⟨i,he⟩ := hi a
      refine ⟨i,he,?_⟩
      rcases EightRigidityCertificate.involution_cover i
        (he.symm ▸ elemPow_eq_one_of_isElementaryAbelian _ a.property) with h | h | ⟨j,hj⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact (hgood ⟨j,hj.symm ▸ he.symm ▸ a.property⟩).elim
    obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
    obtain ⟨i,he,hh⟩ := hall ⟨a,ha⟩
    have hm : treeWord 15 ∈ A := by
      rcases hh with rfl | rfl
      · exact (ha1 he.symm).elim
      · exact he.symm ▸ ha
    refine ⟨_,hm,coreToNatural (Fin 8) (pair 0 2),?_,projected_moved _ _
      EightRigidityCertificate.central_moved.1 EightRigidityCertificate.central_moved.2⟩
    apply smallOrbit_of_cover (fun k => coreToNatural (Fin 8)
      ((![pair 0 2,pair 1 3,pair 0 2,pair 1 3] : Fin 4 → core (Fin 8)) k))
    intro a
    obtain ⟨i,he,hh⟩ := hall a
    obtain ⟨k,hk⟩ := EightRigidityCertificate.central_cover i hh
    refine ⟨k,?_⟩
    rw [←he,←coreToNatural_equivariant,hk]

private theorem action_conj (g a : S) (v : N) :
    naturalRepresentation (Fin 8) (MulAut.conj g a) (naturalRepresentation (Fin 8) g v) =
      naturalRepresentation (Fin 8) g (naturalRepresentation (Fin 8) a v) := by
  have h : MulAut.conj g a * g = g * a := by simp [MulAut.conj_apply,mul_assoc]
  simpa only [map_mul,Module.End.mul_apply] using
    congrArg (fun p => naturalRepresentation (Fin 8) p v) h

private theorem smallOrbit_conj (g : S) (A : Subgroup S) (v : N) :
    SmallOrbit (A.map (MulAut.conj g).toMonoidHom) (naturalRepresentation (Fin 8) g v) ↔
      SmallOrbit A v := by
  let f := naturalRepresentation (Fin 8) g
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (naturalRepresentation (Fin 8) g⁻¹) h
    change naturalRepresentation (Fin 8) g⁻¹ (naturalRepresentation (Fin 8) g x) =
      naturalRepresentation (Fin 8) g⁻¹ (naturalRepresentation (Fin 8) g y) at hh
    simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using hh
  have he : (Set.range fun a : A.map (MulAut.conj g).toMonoidHom =>
      naturalRepresentation (Fin 8) a.val (f v)) =
      f '' (Set.range fun a : A => naturalRepresentation (Fin 8) a.val v) := by
    ext w
    constructor
    · rintro ⟨⟨_,a,ha,rfl⟩,rfl⟩
      exact ⟨_,⟨⟨a,ha⟩,rfl⟩,(action_conj g a v).symm⟩
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      exact ⟨⟨_,mem_map_of_mem _ a.property⟩,action_conj g a v⟩
  unfold SmallOrbit
  rw [he,Nat.card_image_of_injective hf]

/-- Every nontrivial elementary S8 actor moves a vector whose actual orbit has
at most four elements. The displacement survives the full constant-line quotient. -/
theorem moved_small_orbit (A : Subgroup S) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    ∃ a ∈ A, ∃ v : N, SmallOrbit A v ∧ naturalRepresentation (Fin 8) a v ≠ v := by
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S P treeSylow
  let e := MulAut.conj g
  let B := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hP : (P : Subgroup S).map e.toMonoidHom = treeGroup := by
    change ((g • P : Sylow 2 S) : Subgroup S) = treeGroup
    rw [hg,treeSylow_coe]
  have hB : B ≤ treeGroup := hP ▸ map_mono hAP
  have hb : B ≠ ⊥ := by
    intro h
    exact hne ((map_eq_bot_iff_of_injective A (f := e.toMonoidHom) e.injective).mp h)
  obtain ⟨_,⟨a,ha,rfl⟩,v,hv,hd⟩ := tree_witness B hB hb
  let v' := naturalRepresentation (Fin 8) g⁻¹ v
  have hv' : naturalRepresentation (Fin 8) g v' = v := by
    simp only [v',←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  refine ⟨a,ha,v',?_,?_⟩
  · exact (smallOrbit_conj g A v').mp (hv'.symm ▸ hv)
  · intro he
    apply hd
    change naturalRepresentation (Fin 8) (MulAut.conj g a) v = v
    rw [←hv',action_conj,he]
end BinaryPermutation.EightRigidity
