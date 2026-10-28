module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.PlaneAction
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.Representation.BinaryFlagPlaneAction.FlagKernel

/-!
# The actual two-core of the binary minimal parabolic

A plane fixer in P preserves the entire original flag. Its image on V is
therefore a two-group; the source identity C_LT(V)=O₂(LT) gives the same
property for its action kernel. Surjectivity on the Klein four-plane then
identifies C_P(V₂) with O₂(P), which in particular lies in H.

Source: Aschbacher–Smith, 12.8.9(1), printed pp.852–853. The source kernel
identity is supplied by 12.8.3 and stays explicit here.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

theorem binarySeedAction_ker (F : InvariantFlag T V n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G)) :
    (F.binarySeedAction L hL).ker =
      (centralizer (V : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
  ext x
  change F.binarySeedAction L hL x = 1 ↔ (x : G) ∈ centralizer (V : Set G)
  rw [mem_centralizer_iff]
  constructor
  · intro hx v hv
    have he := congrArg (fun a : MulAut V => (a ⟨v, hv⟩ : G)) hx
    change (x : G) * v * (x : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    ext v
    change (x : G) * (v : G) * (x : G)⁻¹ = v
    rw [← hx v v.property, mul_inv_cancel_right]

theorem binarySeedAction_ker_isPGroup (F : InvariantFlag T V n) [Finite G]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2) : IsPGroup 2 (F.binarySeedAction L hL).ker := by
  let K := (F.binarySeedAction L hL).ker
  have he : K.map (L ⊔ (T : Subgroup G)).subtype = (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [show K = _ from F.binarySeedAction_ker L hL, subgroupOf_map_subtype, inf_comm, hcore]
  have hp : IsPGroup 2 (K.map (L ⊔ (T : Subgroup G)).subtype) := by
    rw [he]
    exact pCore_isPGroup.map _
  exact hp.of_equiv (K.equivMapOfInjective _ (L ⊔ (T : Subgroup G)).subtype_injective).symm

theorem binaryPlaneAction_ker (F : InvariantFlag T V n) (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G)) :
    (F.binaryPlaneAction hn L hL).ker =
      (centralizer (F.Vi 2 : Set G)).subgroupOf (F.P L) := by
  ext x
  change F.binaryPlaneAction hn L hL x = 1 ↔ (x : G) ∈ centralizer (F.Vi 2 : Set G)
  rw [mem_centralizer_iff]
  constructor
  · intro hx v hv
    have he := congrArg (fun a : MulAut (F.Vi 2) => (a ⟨v, hv⟩ : G)) hx
    change (x : G) * v * (x : G)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    ext v
    change (x : G) * (v : G) * (x : G)⁻¹ = v
    rw [← hx v v.property, mul_inv_cancel_right]


def binaryFullFlag (F : InvariantFlag T V n) : Subgroup (MulAut V) where
  carrier := {a | ∀ i v, (a v : G) ∈ F.Vi i ↔ (v : G) ∈ F.Vi i}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := by
    intro a b ha hb i v
    exact (ha i (b v)).trans (hb i v)
  inv_mem' := by
    intro a ha i v
    simpa using (ha i (a⁻¹ v)).symm

theorem binaryFullFlag_isPGroup (F : InvariantFlag T V n) [IsElementaryAbelian 2 V] :
    IsPGroup 2 F.binaryFullFlag := by
  apply BinaryFlagPlaneAction.fullFlag_isPGroup (fun i => (F.Vi i).subgroupOf V)
    (fun i j hij x hx => F.monotone hij hx) n
  · intro i hi
    exact (Nat.card_congr (subgroupOfEquivOfLe (F.le_seed i)).toEquiv).trans (F.card i hi)
  · rw [F.last, subgroupOf_self]
  · exact fun a ha => ha

theorem binaryPlaneAction_ker_isPGroup (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    IsPGroup 2 (F.binaryPlaneAction hn L hL).ker := by
  let j := inclusion (show F.P L ≤ L ⊔ (T : Subgroup G) from inf_le_left)
  have hp := (F.binaryFullFlag_isPGroup.comap_of_ker_isPGroup
    (F.binarySeedAction L hL) (F.binarySeedAction_ker_isPGroup L hL hcore)).comap_of_injective
      j (inclusion_injective _)
  apply hp.to_le
  intro x hx
  change ∀ i (v : V), (F.binarySeedAction L hL (j x) v : G) ∈ F.Vi i ↔ (v : G) ∈ F.Vi i
  have hxC : (x : G) ∈ centralizer (F.Vi 2 : Set G) := by
    rw [F.binaryPlaneAction_ker hn L hL] at hx
    exact hx
  intro i v
  have hxi : (x : G) ∈ F.Gi i := by
    by_cases hi : i < n
    · by_cases hi2 : 2 ≤ i
      · exact mem_iInf.mp (mem_iInf.mp x.property.2 i) ⟨hi2,hi⟩
      · exact centralizer_le_normalizer _ (centralizer_le (F.monotone (by omega)) hxC)
    · have he : F.Vi i = V := le_antisymm (F.le_seed i) (F.last.ge.trans (F.monotone (by omega)))
      change (x : G) ∈ normalizer (F.Vi i : Set G)
      rw [he]
      exact F.P_le_seed_normalizer L hL x.property
  exact (mem_normalizer_iff.mp hxi (v : G)).symm


theorem binaryPlane_elementary (F : InvariantFlag T V n) [IsElementaryAbelian 2 V] :
    IsElementaryAbelian 2 (F.Vi 2) where
  toIsMulCommutative := IsMulCommutative.of_setLike_mul_comm fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x,F.le_seed 2 hx⟩ : V) ⟨y,F.le_seed 2 hy⟩)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x =>
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x.val (F.le_seed 2 x.property))

theorem binaryPlane_kleinFour (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
    (hn : 2 ≤ n) : IsKleinFour (F.Vi 2) := by
  let := F.binaryPlane_elementary
  let : Finite (F.Vi 2) := Nat.finite_of_card_ne_zero (by rw [F.card 2 hn]; decide)
  have hne : F.Vi 2 ≠ ⊥ := by
    intro he
    have hc := F.card 2 hn
    rw [he, Subgroup.card_bot] at hc
    norm_num at hc
  let : Nontrivial (F.Vi 2) := (Subgroup.nontrivial_iff_ne_bot (F.Vi 2)).mpr hne
  exact ⟨F.card 2 hn, IsElementaryAbelian.exponent_eq_prime⟩

theorem binaryPlaneAction_ker_eq_twoCore (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (F.binaryPlaneAction hn L hL).ker = pCore 2 (F.P L) := by
  let := F.binaryPlane_kleinFour hn
  let e := IsKleinFour.autEquivPermThree (F.Vi 2)
  have he : (e.toMonoidHom.comp (F.binaryPlaneAction hn L hL)).ker =
      (F.binaryPlaneAction hn L hL).ker :=
    MonoidHom.ker_comp_of_injective _ _ e.injective
  have h := ker_eq_twoCore_of_surjective_perm_three
    (e.toMonoidHom.comp (F.binaryPlaneAction hn L hL))
    (e.surjective.comp (F.binaryPlaneAction_surjective hn L hL hfull))
    (he ▸ F.binaryPlaneAction_ker_isPGroup hn L hL hcore)
  exact he.symm.trans h

theorem binary_parabolic_core (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hcore : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    F.P L ⊓ centralizer (F.Vi 2 : Set G) = (F.P L).pCoreIn 2 ∧
      (F.P L).pCoreIn 2 ≤ F.H := by
  have he := congrArg (fun A : Subgroup (F.P L) => A.map (F.P L).subtype)
    (F.binaryPlaneAction_ker_eq_twoCore hn L hL hfull hcore)
  rw [F.binaryPlaneAction_ker hn L hL, subgroupOf_map_subtype, inf_comm] at he
  change F.P L ⊓ centralizer (F.Vi 2 : Set G) = (F.P L).pCoreIn 2 at he
  refine ⟨he, ?_⟩
  rw [← he]
  exact inf_le_right.trans ((centralizer_le (F.monotone (by omega))).trans
    (centralizer_le_normalizer _))


/-- Label the three nonidentity elements of the original plane. -/
noncomputable def binaryPlaneLabel (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
    (hn : 2 ≤ n) : MulAut (F.Vi 2) ≃* Equiv.Perm (Fin 3) :=
  let := F.binaryPlane_kleinFour hn
  IsKleinFour.autEquivPermThree (F.Vi 2)

/-- The actual P-action on the three points of V₂. -/
noncomputable def binaryPermutationAction (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G)) :
    F.P L →* Equiv.Perm (Fin 3) :=
  (F.binaryPlaneLabel hn).toMonoidHom.comp (F.binaryPlaneAction hn L hL)

theorem binaryPermutationAction_surjective (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL)) :
    Function.Surjective (F.binaryPermutationAction hn L hL) :=
  (F.binaryPlaneLabel hn).surjective.comp (F.binaryPlaneAction_surjective hn L hL hfull)

theorem binaryPermutationAction_ker (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G)) :
    (F.binaryPermutationAction hn L hL).ker = (F.binaryPlaneAction hn L hL).ker :=
  MonoidHom.ker_comp_of_injective _ _ (F.binaryPlaneLabel hn).injective

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
