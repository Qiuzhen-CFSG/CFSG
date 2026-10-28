module
public import Theory.GroupTheory.CubicResidualJoin
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Lifting an invariant cubic action subgroup

An invariant subgroup C of order three in the image of X lifts to the
two-residual of X intersected with its preimage. Only the kernel on X
must be a two-group. If that kernel lies in a two-subgroup R and R moves C,
the lift is fully moved by R and its join with R has two-core quotient S₃.
The action kernel on the lift is exactly its intrinsic two-core.

Source application: Aschbacher--Smith 15.2.6, printed p.1109, the
order-nine Omega residual. No normality in the ambient group is assumed.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

omit [Finite G] [Finite D] in
/-- A cubic image with a two-group kernel identifies the intrinsic two-core. -/
theorem cubic_image_kernel_eq_core (A : Subgroup G) (f : G →* D)
    (hc : Nat.card (A.map f) = 3) (hk : IsPGroup 2 (A ⊓ f.ker : Subgroup G)) :
    A ⊓ f.ker = A.pCoreIn 2 := by
  let a := f.comp A.subtype
  have ha : a.range = A.map f := by rw [MonoidHom.range_comp,range_subtype]
  have hak : IsPGroup 2 a.ker := by
    have he : a.ker = (A ⊓ f.ker).subgroupOf A := by
      ext y
      exact (and_iff_right y.property).symm
    rw [he]
    exact hk.comap_subtype
  have hi : a.ker.index = 3 := by rw [index_ker,ha]; exact hc
  let P : Sylow 2 A := hak.toSylow (by rw [hi]; decide)
  have he : pCore 2 A = a.ker := le_antisymm
    (pCore_isPGroup.le_sylow_of_normal P) (le_sSup ⟨inferInstance,hak⟩)
  change A ⊓ f.ker = (pCore 2 A).map A.subtype
  rw [he]
  ext x
  exact ⟨fun hx => ⟨⟨x,hx.1⟩,hx.2,rfl⟩,fun ⟨y,hy,hey⟩ => hey ▸ ⟨y.property,hy⟩⟩

/-- The residual of the literal invariant preimage supplies a moved cubic lift. -/
theorem exists_cubic_residual_of_invariant_image
    (X R S : Subgroup G) (f : G →* D)
    (hSX : S ≤ normalizer (X : Set G)) (hRS : R ≤ S) (hR : IsPGroup 2 R)
    (hk : IsPGroup 2 (X ⊓ f.ker : Subgroup G)) (hkr : X ⊓ f.ker ≤ R)
    (C : Subgroup D) (hCX : C ≤ X.map f) (hc : Nat.card C = 3)
    (hn : S.map f ≤ normalizer (C : Set D))
    (hm : ¬ R.map f ≤ centralizer (C : Set D)) :
    ∃ A : Subgroup G, A ≤ X ∧ IsPPerfect 2 A ∧
      S ≤ normalizer (A : Set G) ∧ A.map f = C ∧
      ⁅A,R⁆ = A ∧ A ≠ ⊥ ∧ A ⊓ f.ker = A.pCoreIn 2 ∧
      Nonempty (((A ⊔ R : Subgroup G) ⧸ pCore 2 (A ⊔ R : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)) := by
  let B := X ⊓ C.comap f
  let A := (pResidual 2 B).map B.subtype
  have hAX : A ≤ X := (map_subtype_le _).trans inf_le_left
  have hSB : S ≤ normalizer (B : Set G) :=
    (le_inf hSX ((map_le_iff_le_comap.mp hn).trans (C.le_normalizer_comap f))).trans
      inf_normalizer_le_normalizer_inf
  have hSA : S ≤ normalizer (A : Set G) :=
    hSB.trans (normalizer_le_normalizer_characteristic_image B (pResidual 2 B))
  have hBC : B.map f = C := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro c hcc
      obtain ⟨x,hx,he⟩ := hCX hcc
      exact ⟨x,⟨hx,show f x ∈ C from he.symm ▸ hcc⟩,he⟩
  have hcp : pResidual 2 C = ⊤ := by
    apply top_unique
    intro c _
    exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (hc ▸ _root_.orderOf_dvd_natCard c))
  have hAC : A.map f = C := by
    rw [map_embedded_pResidual,hBC,hcp,←MonoidHom.range_eq_map,range_subtype]
  have hp := isPPerfect_embedded_pResidual 2 B
  have ha : Nat.card (A.map f) = 3 := by rw [hAC,hc]
  have hak := hk.to_le (inf_le_inf_right f.ker hAX)
  obtain ⟨hmove,hne,hquot⟩ := cubic_join_of_moving_prime_image A R f hp hR
    (hRS.trans hSA) ha hak ((inf_le_inf_right f.ker hAX).trans hkr) (hAC ▸ hm)
  exact ⟨A,hAX,hp,hSA,hAC,hmove,hne,cubic_image_kernel_eq_core A f ha hak,hquot⟩
end Subgroup
