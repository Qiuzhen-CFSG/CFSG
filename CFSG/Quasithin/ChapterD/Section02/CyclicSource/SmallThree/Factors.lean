module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.Canonical
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.Defs
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The marked cubic support product

The canonical D.2.12 family generates an elementary abelian three-subgroup
inside O₃. Its independent factors and independent moved planes are reindexed
by their actual cardinality, giving the literal multiplication and addition
bijections required by `SupportFactors`. This supplies the product, dimension
and cardinality inputs in the small-three branch of D.2.25, printed p.190.
The full-support premise is supplied by the fixed-complement separation step.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem canonical_le_threeCore :
    let := BinaryGroupAction.action ρ
    smallSupportGroup G (Multiplicative V) 1 ≤ pCore 3 G := by
  let := BinaryGroupAction.action ρ
  apply sSup_le
  intro X hX
  rw [← x1_eq_canonical ρ] at hX
  exact hX.1

theorem canonical_elementary (hf : Function.Injective ρ) :
    let := BinaryGroupAction.action ρ
    IsElementaryAbelian 3 (smallSupportGroup G (Multiplicative V) 1) := by
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.elementary (V := V)
  let := BinaryGroupAction.faithful ρ hf
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let Y := smallSupportGroup G (Multiplicative V) 1
  have hc : Y ≤ centralizer (Y : Set G) :=
    Subgroup.IsCommutingFamily.join_le_centralizer
      (smallSupportFactors_commutingFamily (G := G) (V := Multiplicative V)
        (k := 1) (Or.inl rfl))
  have hcomm (x y : G) (hx : x ∈ Y) (hy : y ∈ Y) : Commute x y :=
    (hc hy x hx)
  have habel : IsMulCommutative Y := ⟨⟨fun x y =>
    Subtype.ext (hcomm x y x.property y.property)⟩⟩
  refine { toIsMulCommutative := habel, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro y
  apply Subtype.ext
  have hy : (y : G) ∈ ⨆ X : smallSupportFactors G (Multiplicative V) 1, X.val := by
    rw [← smallSupportGroup_eq_iSup]
    exact y.property
  apply Subgroup.iSup_induction' (C := fun x _ => x ^ 3 = 1) _ _ _ _ hy
  · intro X x hx
    have hh : (⟨x,hx⟩ : X.val) ^ Nat.card X.val = 1 := pow_card_eq_one'
    rw [show Nat.card X.val = 3 from X.property.2.1] at hh
    exact congrArg Subtype.val hh
  · simp
  · intro x z hx hz hp hq
    have hx' : x ∈ Y := by simpa only [Y,smallSupportGroup_eq_iSup] using hx
    have hz' : z ∈ Y := by simpa only [Y,smallSupportGroup_eq_iSup] using hz
    rw [(hcomm x z hx' hz').mul_pow,hp,hq,one_mul]

private theorem product_bijective {H I : Type*} [CommGroup H] [Fintype I]
    (F : I → Subgroup H) (hi : iSupIndep F) (hg : ⨆ i, F i = ⊤) :
    Function.Bijective (fun x : (i : I) → F i => ∏ i, (x i : H)) := by
  have hc : Pairwise (fun i j : I => ∀ x y : H, x ∈ F i → y ∈ F j → Commute x y) :=
    fun _ _ _ x y _ _ => Commute.all x y
  have he : (fun x : (i : I) → F i => ∏ i, (x i : H)) = Subgroup.noncommPiCoprod hc := by
    funext x
    rw [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
  rw [he]
  refine ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep hi, ?_⟩
  apply MonoidHom.range_eq_top.mp
  rw [Subgroup.noncommPiCoprod_range, hg]

private theorem sum_bijective {W I : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Fintype I] (U : I → Submodule (ZMod 2) W)
    (hi : iSupIndep U) (hg : ⨆ i, U i = ⊤) :
    Function.Bijective (fun v : (i : I) → U i => ∑ i, (v i : W)) := by
  classical
  let f : ((i : I) → U i) →ₗ[ZMod 2] W :=
    { toFun := fun v => ∑ i, (v i : W)
      map_add' := by intros; simp [Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum] }
  constructor
  · intro v w he
    funext i
    apply Subtype.ext
    exact (iSupIndep_iff_finsetSum_eq_imp_eq U).mp hi Finset.univ
      (fun j => (v j : W)) (fun j => (w j : W))
      (fun j _ => ⟨(v j).property, (w j).property⟩) he i (Finset.mem_univ i)
  · change Function.Surjective f
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← hg]
    apply iSup_le
    intro i v hv
    refine ⟨Pi.single i ⟨v, hv⟩, ?_⟩
    change ∑ j, ((Pi.single i (⟨v, hv⟩ : U i) : (j : I) → U j) j : W) = v
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp

/-- The literal canonical factors, reindexed by their actual finite cardinality,
form the marked internal product and support sum used by the cyclic endpoint. -/
theorem canonical_supportFactors (hf : Function.Injective ρ)
    (hm : let := BinaryGroupAction.action ρ
      subspaceCommutator ρ ⊤ (smallSupportGroup G (Multiplicative V) 1) = ⊤) :
    let := BinaryGroupAction.action ρ
    let Y := smallSupportGroup G (Multiplicative V) 1
    let s := Nat.card (smallSupportFactors G (Multiplicative V) 1)
    ∃ d : FittingConfigurations.SupportFactors ρ Y s,
      (∀ i, d.ambient i ∈ smallSupportFactors G (Multiplicative V) 1) ∧
      Nat.card Y = 3 ^ s := by
  classical
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.elementary (V := V)
  let := BinaryGroupAction.faithful ρ hf
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let Y := smallSupportGroup G (Multiplicative V) 1
  let I := smallSupportFactors G (Multiplicative V) 1
  let : Fintype I := Fintype.ofFinite I
  let : IsElementaryAbelian 3 Y := canonical_elementary ρ hf
  let : CommGroup Y := IsMulCommutative.instCommGroup
  let F : I → Subgroup Y := fun X => X.val.subgroupOf Y
  have hXY (X : I) : X.val ≤ Y := le_sSup X.property
  have hmap (X : I) : (F X).map Y.subtype = X.val := map_subgroupOf_eq_of_le (hXY X)
  have hcard (X : I) : Nat.card (F X) = 3 := by
    rw [← Subgroup.card_map_of_injective Y.subtype_injective,hmap]
    exact X.property.2.1
  have hd := smallSupport_decomposition (G := G) (V := Multiplicative V)
    (k := 1) (Or.inl rfl)
  have hi : iSupIndep F := by
    rw [iSupIndep_def]
    intro X
    apply Subgroup.disjoint_def.mpr
    intro x hx hrest
    apply Subtype.ext
    apply Subgroup.disjoint_def.mp (hd.1 X) hx
    have hh := Subgroup.mem_map_of_mem Y.subtype hrest
    rw [Subgroup.map_iSup] at hh
    simp only [Subgroup.map_iSup,hmap] at hh
    exact hh
  have hg : (⨆ X, F X) = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_iSup]
    simp only [hmap,← MonoidHom.range_eq_map,Y.range_subtype]
    exact (smallSupportGroup_eq_iSup 1).symm
  have hb := product_bijective F hi hg
  have hcY : Nat.card Y = 3 ^ Nat.card I := by
    calc
      Nat.card Y = Nat.card ((X : I) → F X) :=
        (Nat.card_congr (Equiv.ofBijective _ hb)).symm
      _ = 3 ^ Nat.card I := by simp [Nat.card_pi,hcard,Nat.card_eq_fintype_card]
  let e : Fin (Nat.card I) ≃ I :=
    (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm)).symm
  let factor : Fin (Nat.card I) → Subgroup Y := F ∘ e
  have hif : iSupIndep factor := hi.comp e.injective
  have hgf : (⨆ i, factor i) = ⊤ := by
    simpa only [factor,Function.comp_def,e.surjective.iSup_comp] using hg
  have hmf (i : Fin (Nat.card I)) : (factor i).map Y.subtype = (e i).val := hmap (e i)
  have hv : iSupIndep (fun X : I => subspaceCommutator ρ ⊤ X.val) := by
    have hh := hd.2.2.1.map_orderIso (BinaryGroupAction.submoduleEquivSubgroup (V := V)).symm
    simpa only [Function.comp_def,BinaryGroupAction.commutator_eq,OrderIso.symm_apply_apply] using hh
  have hvs : iSupIndep (fun i : Fin (Nat.card I) =>
      subspaceCommutator ρ ⊤ ((factor i).map Y.subtype)) := by
    simp only [hmf]
    exact hv.comp e.injective
  have hvg : (⨆ i : Fin (Nat.card I),
      subspaceCommutator ρ ⊤ ((factor i).map Y.subtype)) = ⊤ := by
    simp only [hmf]
    rw [e.surjective.iSup_comp (fun X : I => subspaceCommutator ρ ⊤ X.val)]
    rw [← BinaryGroupAction.moved_iSup,← smallSupportGroup_eq_iSup]
    exact hm
  refine ⟨{
    factor := factor
    card_factor := fun i => hcard (e i)
    multiply_bijective := ?_
    support_dim := ?_
    add_bijective := sum_bijective _ hvs hvg },?_,hcY⟩
  · change Function.Bijective (fun x : (i : Fin (Nat.card I)) → factor i =>
      (List.ofFn fun i => (x i : Y)).prod)
    simpa only [Fin.prod_ofFn] using product_bijective factor hif hgf
  · intro i
    rw [hmf]
    exact ((show (e i).val ∈ {X : Subgroup G | X ≤ pCore 3 G ∧ Nat.card X = 3 ∧
        Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 2} from
      (x1_eq_canonical ρ).symm ▸ (e i).property)).2.2
  · intro i
    change (factor i).map Y.subtype ∈ _
    rw [hmf]
    exact (e i).property

end CFSG.Quasithin.ChapterD.CyclicSource