module

public import Theory.SpecificGroups.BinaryLinear.AffineFourMarking
public import Theory.LinearAlgebra.BinaryFourPointStabilizer
public import Theory.GroupTheory.Gaschutz
public import Theory.ElementaryAbelian.VectorSpace

/-!
A split self-centralizing elementary sixteen in a point centralizer of
order 21504 supplies the whole marked affine centralizer. The embedding
uses the complement's actual conjugation action and retains every element
of the elementary subgroup. Equal orders then give surjectivity.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace BinaryLinear.Affine

private def linearAut (d : ℕ) :
    ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)) ≃*
      MulAut (Multiplicative (Fin d → ZMod 2)) where
  toFun f := f.toAddEquiv.toMultiplicative
  invFun f := { AddEquiv.toMultiplicative.symm f with
    map_smul' := ZMod.map_smul (AddEquiv.toMultiplicative.symm f) }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

private def actionEquiv (d : ℕ) :
    Matrix.SpecialLinearGroup (Fin d) (ZMod 2) ≃*
      MulAut (Multiplicative (Fin d → ZMod 2)) :=
  (OuterCyclic.slEquivLinear d).trans (linearAut d)

private theorem actionEquiv_eq (d : ℕ) (g : Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) :
    actionEquiv d g = action d g := by
  ext v
  rfl

private theorem exists_embedding_of_split {H : Type*} [Group H]
    (A L : Subgroup H) [A.Normal] (hL : A.IsComplement' L)
    (hself : centralizer (A : Set H) ≤ A)
    (d : ℕ) (c : A ≃* Multiplicative (Fin d → ZMod 2)) :
    ∃ f : H →* Model d, Function.Injective f ∧
      ∀ a : A, f a = SemidirectProduct.inl (c a) := by
  let γ := A.normalizerMonoidHom.comp (inclusion (A.normalizer_eq_top ▸ le_top) : L →* _)
  let ρ := (MulAut.congr c).toMonoidHom.comp γ
  let j := (actionEquiv d).symm.toMonoidHom.comp ρ
  have hjact (g : L) : action d (j g) = MulAut.congr c (γ g) := by
    rw [← actionEquiv_eq]
    exact (actionEquiv d).apply_symm_apply (ρ g)
  have hj : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff j).mp
    apply bot_unique
    intro g hg
    have hρ : ρ g = 1 := (actionEquiv d).symm.injective
      (hg.trans (actionEquiv d).symm.map_one.symm)
    have hγ : γ g = 1 := (MulAut.congr c).injective
      (hρ.trans (MulAut.congr c).map_one.symm)
    have hc : (g : H) ∈ centralizer (A : Set H) := by
      intro a ha
      have he := congrArg (fun b : MulAut A => (b ⟨a, ha⟩ : H)) hγ
      change (g : H) * a * (g : H)⁻¹ = a at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    exact Subtype.ext (disjoint_def.mp hL.disjoint (hself hc) g.property)
  have hcompat (g : L) : c.toMonoidHom.comp (γ g).toMonoidHom =
      (action d (j g)).toMonoidHom.comp c.toMonoidHom := by
    apply MonoidHom.ext
    intro a
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hjact]
    change c (γ g a) = c (γ g (c.symm (c a)))
    rw [c.symm_apply_apply]
  let m := SemidirectProduct.mulEquivSubgroup hL
  let f := (SemidirectProduct.map c.toMonoidHom j hcompat).comp m.symm.toMonoidHom
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    apply m.symm.injective
    apply SemidirectProduct.ext
    · exact c.injective (congrArg SemidirectProduct.left hxy)
    · exact hj (congrArg SemidirectProduct.right hxy)
  · intro a
    have hm : m (SemidirectProduct.inl a) = (a : H) := by
      change (a : H) * 1 = a
      exact mul_one _
    rw [← hm]
    change SemidirectProduct.map c.toMonoidHom j hcompat
      (m.symm (m (SemidirectProduct.inl a))) = _
    rw [m.symm_apply_apply, SemidirectProduct.map_inl]
    rfl

private theorem translationCentralizer_card
    (v : Multiplicative (Fin 4 → ZMod 2)) (hv : v ≠ 1) :
    Nat.card (Theory.GroupTheory.TranslationCentralizer.centralizer (action 4) v) = 21504 := by
  let e := OuterCyclic.slEquivLinear 4
  let S := Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer v.toAdd
  let C := Theory.GroupTheory.TranslationCentralizer.centralizer (action 4) v
  let c : C ≃ (Multiplicative (Fin 4 → ZMod 2)) × S := {
    toFun := fun x => (x.val.left, ⟨e x.val.right, by
      have hx := (Theory.GroupTheory.TranslationCentralizer.mem_iff (action 4) v x.val).mp x.property
      exact hx⟩)
    invFun := fun x => ⟨⟨x.1, e.symm x.2.val⟩, by
      apply (Theory.GroupTheory.TranslationCentralizer.mem_iff (action 4) v _).mpr
      change e (e.symm x.2.val) v.toAdd = v.toAdd
      rw [e.apply_symm_apply]
      exact x.2.property⟩
    left_inv := fun x => by
      apply Subtype.ext
      apply SemidirectProduct.ext
      · rfl
      · exact e.symm_apply_apply x.val.right
    right_inv := fun x => by
      apply Prod.ext
      · rfl
      · exact Subtype.ext (e.apply_symm_apply x.2.val) }
  rw [Nat.card_congr c, Nat.card_prod,
    Theory.LinearAlgebra.BinaryFourPointStabilizer.card_stabilizer v.toAdd hv (by simp)]
  norm_num [Nat.card_congr (Multiplicative.toAdd :
    Multiplicative (Fin 4 → ZMod 2) ≃ (Fin 4 → ZMod 2))]

variable {G : Type*} [Group G] [Finite G]

/-- A split self-centralizing elementary sixteen, with its actual fixed
point, reconstructs the full affine point centralizer. -/
theorem exists_pointMarking_of_split_sixteen
    (z : G) (hz : z ≠ 1) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hzA : z ∈ A) (hA : Nat.card A = 16)
    (hAC : A ≤ centralizer ({z} : Set G))
    (hCA : centralizer ({z} : Set G) ≤ normalizer (A : Set G))
    (hself : centralizer ({z} : Set G) ⊓ centralizer (A : Set G) ≤ A)
    (hC : Nat.card (centralizer ({z} : Set G)) = 21504)
    (hsplit : ∃ L : Subgroup (centralizer ({z} : Set G)),
      (A.subgroupOf (centralizer ({z} : Set G))).IsComplement' L) :
    Nonempty (PointMarking 4 z A) := by
  let C := centralizer ({z} : Set G)
  let A₀ := A.subgroupOf C
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer hCA
  have hdim : Module.finrank (ZMod 2) (Additive A) = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    change Nat.card A = _ at hh
    rw [hA, Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) hh.symm
  let c : A ≃* Multiplicative (Fin 4 → ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) (Additive A) hdim).equivFun.toAddEquiv.toMultiplicativeRight
  let c₀ := (subgroupOfEquivOfLe hAC).trans c
  have hc : centralizer (A₀ : Set C) ≤ A₀ := by
    intro x hx
    apply hself
    refine ⟨x.property, ?_⟩
    intro a ha
    exact congrArg Subtype.val (hx ⟨a, hAC ha⟩ ha)
  obtain ⟨L, hL⟩ := hsplit
  obtain ⟨f, hf, hfa⟩ := exists_embedding_of_split A₀ L hL hc 4 c₀
  let zC : C := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩
  let v := c ⟨z, hzA⟩
  have hfv : f zC = SemidirectProduct.inl v := hfa ⟨zC, hzA⟩
  have hmem (x : C) : f x ∈ Theory.GroupTheory.TranslationCentralizer.centralizer (action 4) v := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hfv, ← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (mem_centralizer_singleton_iff.mp x.property))
  let j := f.codRestrict _ hmem
  have hj : Function.Injective j := fun x y he => hf (congrArg Subtype.val he)
  have hv : v ≠ 1 := fun he => hz (congrArg Subtype.val (c.map_eq_one_iff.mp he))
  let : Finite (Model 4) := Finite.of_equiv
    ((Multiplicative (Fin 4 → ZMod 2)) × Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    SemidirectProduct.equivProd.symm
  have hbij : Function.Bijective j := (Nat.bijective_iff_injective_and_card j).mpr
    ⟨hj, hC.trans (translationCentralizer_card v hv).symm⟩
  refine ⟨{ point_mem := hzA
            seed_le := hAC
            vectorEquiv := c
            centralizerEquiv := MulEquiv.ofBijective j hbij
            on_seed := ?_ }⟩
  intro u
  exact hfa ⟨⟨u, hAC u.property⟩, u.property⟩

/-- Splitting inside the actual Sylow subgroup suffices: Gaschütz
constructs a complement in the entire original point centralizer. -/
theorem exists_pointMarking_of_sylow_split_sixteen
    (z : G) (hz : z ≠ 1) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hzA : z ∈ A) (hA : Nat.card A = 16)
    (hAC : A ≤ centralizer ({z} : Set G))
    (hCA : centralizer ({z} : Set G) ≤ normalizer (A : Set G))
    (hself : centralizer ({z} : Set G) ⊓ centralizer (A : Set G) ≤ A)
    (hC : Nat.card (centralizer ({z} : Set G)) = 21504)
    (S : Sylow 2 (centralizer ({z} : Set G)))
    (hsplit : ∃ L : Subgroup S,
      ((A.subgroupOf (centralizer ({z} : Set G))).subgroupOf S).IsComplement' L) :
    Nonempty (PointMarking 4 z A) := by
  let C := centralizer ({z} : Set G)
  let A₀ := A.subgroupOf C
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer hCA
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hAC
  exact exists_pointMarking_of_split_sixteen z hz A hzA hA hAC hCA hself hC
    ((exists_complement_iff_sylow A₀ (IsElementaryAbelian.isPGroup 2 A₀) S).mpr hsplit)

end BinaryLinear.Affine
