module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.QuinticResidual
public import Theory.GroupTheory.PResidual.PrimeToNilpotent
public import Theory.GroupAction.FaithfulSixteen

/-!
# The canonical quintic actor on the original moving support

For the decomposable prime-five marking, O^{5′}(C_M(Z₁)) has exactly the
opposite original order-five kernel as its action image. This holds even
when the full two-residual image has order fifteen: in that cyclic normal
residual, the five-core is the original five-kernel. Surjective residual
transport identifies the same order-five group in C_M(Z₁)/C_M(V).

The actor fixes the first support and moves the second; both have order
sixteen. It is normalized by the original C_T(Z₁), equals its own prime-to-five
residual, and lies in the original two-residual. Restriction to the moving
support has the same kernel as the action on V. Orbit counting then proves
that every subgroup of that support normalized by the actor is trivial or
full. In particular [V₂,Y] = V₂ for the same actor Y. The parent
Decomposable module applies the construction to the actual
eight-dimensional source action, retaining the same marking and prime.

This supplies the quintic action used in the argument of 15.1.23. It does not
identify O^{5′}(C_M(Z₁)) with the full two-residual or assert it is a five-group.
The order-fifteen exclusion and prime-five component marker remain required.
Source: Aschbacher--Smith 15.1.16(a)--18 and 15.1.23, pp.1092--1093,1100.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
variable {G : Type*} [Group G] [Finite G]

/-- The prime-to-five residual has exactly the original opposite five-kernel as image. -/
theorem ThompsonPair.full_image_quintic_residual
    {T : Sylow 2 G}
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5) :
    let ρ := imageRepresentation M V hn
    let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    let K := subspaceKernel ρ W ⊤
    (primeToResidual 5 K).map K.subtype =
      (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap := by
  intro ρ W K
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P := (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap
  let R := pResidual 2 K
  obtain ⟨hPR,hKP,_,_⟩ := s.full_image_residual hTM hn c d hJ
  have hPK : P ≤ K := hPR.trans (map_subtype_le _)
  let Pk := P.subgroupOf K
  let : Pk.Normal := normal_subgroupOf_of_le_normalizer hKP
  have hP : Nat.card Pk = 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv,s.kernel_card,hfive]
  obtain ⟨hcyc,hcard⟩ := s.full_image_residual_of_prime_five hTM hn c d π hp hs hJ hfive
  let : IsCyclic R := hcyc
  have hcop : Nat.Coprime 5 R.index := by
    rw [index_eq_card]
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := K) 2).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have he : primeToResidual 5 K = pCore 5 K :=
    primeToResidual_eq_pCore_of_nilpotent_normal R inferInstance hcop
  have hlo : Pk ≤ pCore 5 K := le_sSup ⟨inferInstance,IsPGroup.of_card (p := 5) (n := 1) hP⟩
  have hhi : pCore 5 K ≤ R := he ▸ primeToResidual_le R hcop
  have hdiv : Nat.card (pCore 5 K) ∣ 15 := (card_dvd_of_le hhi).trans (by
    rcases hcard with h | h
    · exact h.symm ▸ (by decide : 5 ∣ 15)
    · exact h.symm ▸ (dvd_refl 15))
  have hc : Nat.card (pCore 5 K) ≤ 5 := by
    have hh := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
    rw [show Nat.divisors 15 = {1,3,5,15} by decide] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 5) (G := K)).exists_card_eq
    have hthree : Nat.Coprime 3 (Nat.card (pCore 5 K)) := hn ▸ (by decide : Nat.Coprime 3 5).pow_right n
    rcases hh with hh | hh | hh | hh
    · rw [hh]; decide
    · exact False.elim ((by decide : ¬ Nat.Coprime 3 3) (hh ▸ hthree))
    · rw [hh]
    · exact False.elim ((by decide : ¬ Nat.Coprime 3 15) (hh ▸ hthree))
  have heq : pCore 5 K = Pk := (eq_of_le_of_card_ge hlo (by rw [hP]; exact hc)).symm
  rw [he,heq,map_subgroupOf_eq_of_le hPK]

private theorem quintic_action_image
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (W : Submodule (ZMod 2) (Additive V)) :
    let K := subspaceKernel (imageRepresentation M V hn) W ⊤
    let C := M ⊓ centralizer (plane V W : Set G)
    let Y := (primeToResidual 5 C).map C.subtype
    (Y.subgroupOf M).map (actionHom M V hn).rangeRestrict =
      (primeToResidual 5 K).map K.subtype := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro K C Y
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let hYM : Y ≤ M := (map_subtype_le _).trans inf_le_left
  let a := f.comp (inclusion hYM)
  obtain ⟨q,hq,_,hcoord⟩ := ExtraspecialMarker.stabilizer_projection M V hn W
  have he := map_primeToResidual_of_surjective 5 q hq
  change (Y.subgroupOf M).map f = _
  rw [←inclusion_range hYM,←MonoidHom.range_comp]
  change a.range = _
  rw [←he,map_map]
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    obtain ⟨z,hz,hzy⟩ := y.property
    refine ⟨z,hz,?_⟩
    change (q z : internalActionImage M V hn) = f (inclusion hYM y)
    exact (hcoord z).trans (congrArg f (Subtype.ext hzy))
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,mem_map_of_mem C.subtype hz⟩,(hcoord z).symm⟩

omit [Finite G] in
private theorem actor_spaces
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (Y : Subgroup G) (hYM : Y ≤ M) :
    let P : Subgroup (internalActionImage M V hn) :=
      (Y.subgroupOf M).map (actionHom M V hn).rangeRestrict
    (V ⊓ centralizer (Y : Set G)).subgroupOf V =
      binarySubgroup (fixedSpace (imageRepresentation M V hn) P) ∧
      ⁅V,Y⁆.subgroupOf V = binarySubgroup
        (subspaceCommutator (imageRepresentation M V hn) ⊤ P) := by
  intro P
  let a : Y →* internalActionImage M V hn :=
    (actionHom M V hn).rangeRestrict.comp (inclusion hYM)
  have he : a.range = P := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨⟨y,hYM y.property⟩,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  constructor
  · rw [←he]
    ext w
    constructor
    · intro hw
      rintro ⟨x,⟨y,rfl⟩⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      change (y : G) * (w : G) * (y : G)⁻¹ = w
      have hc : (y : G) * (w : G) = (w : G) * y := hw.2 y y.property
      rw [hc,mul_inv_cancel_right]
    · intro hw
      refine ⟨w.property,?_⟩
      intro y hy
      have hh := hw ⟨a ⟨y,hy⟩,⟨⟨y,hy⟩,rfl⟩⟩
      have hh' := congrArg (fun u : Additive V => (u.toMul : G)) hh
      change y * (w : G) * y⁻¹ = w at hh'
      exact mul_inv_eq_iff_eq_mul.mp hh'
  · have hh := commutator_image_eq (imageRepresentation M V hn) V V Y
      (hYM.trans hn) le_rfl a (MonoidHom.id V) (fun _ _ => rfl) ⊤ (by
        ext x
        simp [binarySubgroup])
    simpa only [map_id,he] using hh

private theorem moving_support_irreducible
    (M V Y A B : Subgroup G) (hn : M ≤ normalizer (V : Set G))
    (hYM : Y ≤ M) (hBV : B ≤ V) (hYB : Y ≤ normalizer (B : Set G))
    (hfix : A ≤ centralizer (Y : Set G)) (hjoin : A ⊔ B = V)
    (hcard : Nat.card B = 16)
    (himage : Nat.card ((Y.subgroupOf M).map
      (show M →* internalActionImage M V hn from (actionHom M V hn).rangeRestrict)) = 5) :
    Nat.card (internalActionImage Y B hYB) = 5 ∧
      ∀ D : Subgroup G, D ≤ B → Y ≤ normalizer (D : Set G) → D = ⊥ ∨ D = B := by
  have hk : (centralizer (V : Set G)).subgroupOf Y =
      (centralizer (B : Set G)).subgroupOf Y := by
    apply le_antisymm (subgroupOf_mono Y (centralizer_le hBV))
    intro y hy
    have hA : A ≤ centralizer ({(y : G)} : Set G) := by
      intro a ha
      exact mem_centralizer_singleton_iff.mpr ((hfix ha y y.property).symm)
    have hB : B ≤ centralizer ({(y : G)} : Set G) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr (hy b hb)
    have hall : V ≤ centralizer ({(y : G)} : Set G) := hjoin ▸ sup_le hA hB
    intro v hv
    exact mem_centralizer_singleton_iff.mp (hall hv)
  have hci : (centralizer (B : Set G)).relIndex Y = 5 := by
    have hi : Nat.card ((Y.subgroupOf M).map (actionHom M V hn).rangeRestrict) =
        (centralizer (V : Set G)).relIndex Y := by
      rw [←relIndex_ker,MonoidHom.ker_rangeRestrict,actionHom_ker,relIndex_subgroupOf hYM]
    have hh := hi.symm.trans himage
    change ((centralizer (B : Set G)).subgroupOf Y).index = 5
    rw [←hk]
    exact hh
  have hc : Nat.card (internalActionImage Y B hYB) = 5 := by
    change Nat.card (actionHom Y B hYB).range = 5
    rw [MonoidHom.range_eq_map,←relIndex_ker,relIndex_top_right,actionHom_ker]
    exact hci
  refine ⟨hc,?_⟩
  intro D hDB hYD
  have h := Theory.GroupAction.invariant_eq_bot_or_top_of_image_five
    (actionHom Y B hYB) (by change 5 ∣ Nat.card (internalActionImage Y B hYB); rw [hc])
    hcard (D.subgroupOf B) (by
      intro y b
      exact mem_normalizer_iff.mp (hYD y.property) (b : G))
  rcases h with hb | ht
  · left
    rw [←map_subgroupOf_eq_of_le hDB,hb,Subgroup.map_bot]
  · right
    rw [←map_subgroupOf_eq_of_le hDB,ht,←MonoidHom.range_eq_map,range_subtype]

/-- Fixed and moved supports, normalization and residual containment for the canonical actor. -/
theorem ThompsonPair.quintic_actor_geometry
    {T : Sylow 2 G}
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    let Y := (primeToResidual 5 C).map C.subtype
    (Y.subgroupOf M).map (actionHom M V hn).rangeRestrict =
        (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap ∧
      V ⊓ centralizer (Y : Set G) = plane V (c.ambientFactor d s.first).space ∧
      ⁅V,Y⁆ = plane V (c.ambientFactor d s.second).space ∧
      Nat.card (V ⊓ centralizer (Y : Set G) : Subgroup G) = 16 ∧
      Nat.card (⁅V,Y⁆ : Subgroup G) = 16 ∧
      ((T : Subgroup G) ⊓ centralizer (Z : Set G)) ≤ normalizer (Y : Set G) ∧
      (primeToResidual 5 Y).map Y.subtype = Y ∧
      Y ≤ (pResidual 2 C).map C.subtype := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro Z C Y
  let ρ := imageRepresentation M V hn
  let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict)
  have hW : plane V W = Z := plane_thompson_intersection hTM hn _
  have him : (Y.subgroupOf M).map (actionHom M V hn).rangeRestrict =
      (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap := by
    have hh := quintic_action_image M V hn W
    rw [hW] at hh
    exact hh.trans (s.full_image_quintic_residual hTM hn c d π hp hs hJ hfive)
  have hYM : Y ≤ M := (map_subtype_le _).trans inf_le_left
  have hspaces := actor_spaces M V hn Y hYM
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  change (Y.subgroupOf M).map f = _ at him
  change (V ⊓ centralizer (Y : Set G)).subgroupOf V =
      binarySubgroup (fixedSpace (imageRepresentation M V hn) ((Y.subgroupOf M).map f)) ∧
      ⁅V,Y⁆.subgroupOf V = binarySubgroup
        (subspaceCommutator (imageRepresentation M V hn) ⊤ ((Y.subgroupOf M).map f)) at hspaces
  rw [him,s.kernel_fixed s.second s.first s.distinct.symm,s.kernel_moved s.second] at hspaces
  have hfix : V ⊓ centralizer (Y : Set G) = plane V (c.ambientFactor d s.first).space := by
    rw [←map_subgroupOf_eq_of_le (show V ⊓ centralizer (Y : Set G) ≤ V from inf_le_left),hspaces.1]
    rfl
  have hmove : ⁅V,Y⁆ = plane V (c.ambientFactor d s.second).space := by
    rw [←map_subgroupOf_eq_of_le (le_normalizer_iff_commutator_le_left.mp (hYM.trans hn)),hspaces.2]
    rfl
  refine ⟨him,hfix,hmove,?_,?_,?_,?_,?_⟩
  · rw [hfix]; exact s.support_card s.first
  · rw [hmove]; exact s.support_card s.second
  · exact (inf_le_inf_right _ hTM).trans
      (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (primeToResidual 5 C)))
  · change (primeToResidual 5 ((primeToResidual 5 C).map C.subtype)).map _ = _
    rw [←map_embedded_primeToResidual_of_hom 5 (primeToResidual 5 C) C.subtype,
      embedded_primeToResidual_eq_of_normal 5 (primeToResidual 5 C) le_rfl]
  · apply map_mono
    apply primeToResidual_le
    rw [index_eq_card]
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := C) 2).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n

/-- The same quintic actor has no proper nontrivial invariant subgroup in its moving support. -/
theorem ThompsonPair.quintic_actor_irreducible
    {T : Sylow 2 G}
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    let Y := (primeToResidual 5 C).map C.subtype
    let B := plane V (c.ambientFactor d s.second).space
    ∀ D : Subgroup G, D ≤ B → Y ≤ normalizer (D : Set G) → D = ⊥ ∨ D = B := by
  intro Z C Y B
  obtain ⟨him,hfix,hmove,_,_,_,_,_⟩ :=
    s.quintic_actor_geometry hTM hn c d π hp hs hJ hfive
  have hYM : Y ≤ M := (map_subtype_le _).trans inf_le_left
  have hYB : Y ≤ normalizer (B : Set G) := by
    change Y ≤ normalizer (plane V (c.ambientFactor d s.second).space : Set G)
    rw [←hmove]
    exact normalizer_commutator_ge_right V Y
  apply (moving_support_irreducible M V Y
    (plane V (c.ambientFactor d s.first).space) B hn hYM (plane_le _) hYB
    (hfix.symm.le.trans inf_le_right) s.complement (s.support_card s.second) ?_).2
  exact (congrArg (fun K : Subgroup (internalActionImage M V hn) => Nat.card K) him).trans
    ((s.kernel_card s.second).trans hfive)

/-- The literal module-centralizer quotient has prime-to-five residual of order five. -/
theorem ThompsonPair.full_quotient_quintic_residual
    {T : Sylow 2 G}
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    letI := caseI_module_centralizer_normal (Z1 := Z) hn
    let Q := primeToResidual 5 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)
    Nat.card Q = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let ρ := imageRepresentation M V hn
  let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict)
  let K := subspaceKernel ρ W ⊤
  let qdata (A : Subgroup G) : Prop :=
    let C := M ⊓ centralizer (A : Set G)
    letI := caseI_module_centralizer_normal (Z1 := A) hn
    Nat.card (primeToResidual 5 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5
  have hW : plane V W = thompsonPlane T V (c.ambientFactor d s.first).space :=
    plane_thompson_intersection hTM hn _
  have hh : qdata (plane V W) := by
    let := caseI_module_centralizer_normal (Z1 := (binarySubgroup W).map V.subtype) hn
    obtain ⟨q,hq,hker,_⟩ := ExtraspecialMarker.stabilizer_projection M V hn W
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    have he := map_primeToResidual_of_surjective 5 e.toMonoidHom e.surjective
    let er := ((primeToResidual 5 _).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr he)
    have hi := s.full_image_quintic_residual hTM hn c d π hp hs hJ hfive
    have hc : Nat.card (primeToResidual 5 K) = 5 := by
      rw [←card_map_of_injective (K := primeToResidual 5 K) K.subtype_injective,hi,
        s.kernel_card,hfive]
    exact (Nat.card_congr er.toEquiv).trans hc
  change qdata (thompsonPlane T V (c.ambientFactor d s.first).space)
  rwa [hW] at hh

/-- The canonical quintic actor moves its original sixteen-element support onto itself,
as required in the source exclusion. -/
theorem ThompsonPair.quintic_actor_moves_support
    {T : Sylow 2 G}
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hJ : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (hfive : s.prime = 5) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    let Y := (primeToResidual 5 C).map C.subtype
    let B := plane V (c.ambientFactor d s.second).space
    ⁅B,Y⁆ = B := by
  intro Z C Y B
  obtain ⟨_,hfix,hmove,_,_,_,_,_⟩ := s.quintic_actor_geometry hTM hn c d π hp hs hJ hfive
  have hYB : Y ≤ normalizer (B : Set G) := by
    change Y ≤ normalizer (plane V (c.ambientFactor d s.second).space : Set G)
    rw [←hmove]
    exact normalizer_commutator_ge_right V Y
  have hirr := s.quintic_actor_irreducible hTM hn c d π hp hs hJ hfive
    ⁅B,Y⁆ (le_normalizer_iff_commutator_le_left.mp hYB)
    (normalizer_commutator_ge_right B Y)
  rcases hirr with hz | he
  · have hBA : B ≤ plane V (c.ambientFactor d s.first).space :=
      (le_inf (plane_le _) (commutator_eq_bot_iff_le_centralizer.mp hz)).trans hfix.le
    have hb : B = ⊥ := bot_unique ((le_inf hBA le_rfl).trans s.disjoint.le)
    have hc : Nat.card B = 16 := s.support_card s.second
    rw [hb,card_bot] at hc
    omega
  · exact he

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
