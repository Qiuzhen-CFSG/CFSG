module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.ResidualGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.Controls
public import Theory.GroupTheory.PResidual.NormalSup
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.Representation.BinarySymmetricThreeNormalizer
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer
public import Theory.Representation.BinaryOffender.FaithfulInvariantSection

/-!
# The exact cubic residual of the decomposable marking

The full marked-centralizer residual fixes the first original support, so
restriction to the second is faithful. Its binary symmetric-three normalizer
embedding gives exponent three. On the first support, the residual centralizes
the faithful factor. The section-centralizer theorem, applied to the literal
preimage in M, makes this three-group cyclic. The original opposite cubic
kernel already lies in it, so the two subgroups are equal.

Transport through the original action identifies the residual order in
C_M(Z₁)/C_M(V). The same rank argument controls the centralizer of the first
factor inside the support normalizer. Its residual is the opposite cubic
kernel, so the full action residual lies in the original factor product.
A Sylow supplement and the original exchange then prove
M = ⟨C_M(Z₁), T⟩. Rank is always bounded on the original cover.

The parent Decomposable module applies this calculation and the resulting
marker to the actual eight-dimensional source, retaining the same prime-five
alternative. The prime-five calculation remains a separate obligation.

Source: Aschbacher--Smith 15.1.10 and 15.1.16(a)--18, printed pp.1089,
1092--1093, using A.1.31(1), printed pp.27--28.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition Stellmacher ChapterA.Section05To06

private theorem cyclic_of_centralizes_normal_three
    {A D : Type*} [Group A] [Finite A] [Group D] [Finite D]
    (f : A →* D) (hf : Function.Surjective f) (hr : primeRank 3 A ≤ 2)
    (H : Subgroup D) [H.Normal] (e : H ≃* Equiv.Perm (Fin 3))
    (R : Subgroup D) (hR : IsPGroup 3 R) (hc : R ≤ centralizer (H : Set D)) :
    IsCyclic R := by
  let P := (pResidual 2 H).map H.subtype
  have hP : IsPGroup 3 P := by
    apply IsPGroup.map
    exact pResidual_threeGroup_of_injective_permThree_product
      (MonoidHom.pi fun _ : Unit => e.toMonoidHom)
      (fun x y h => e.injective (congrFun h ()))
  let a : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let b : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  let t : D := e.symm a
  have ha : orderOf a = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hb : orderOf b = 3 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have ht : orderOf t = 2 := by
    rw [show orderOf t = orderOf (e.symm a) from orderOf_injective H.subtype H.subtype_injective _]
    rw [e.symm.orderOf_eq,ha]
  have hbP : (e.symm b : D) ∈ P := mem_map_of_mem H.subtype
    (mem_pResidual_of_orderOf_coprime (by rw [e.symm.orderOf_eq,hb]; decide))
  have htP : t ∉ centralizer (P : Set D) := by
    intro htP
    have he := congrArg e (Subtype.ext (htP (e.symm b) hbP) :
      e.symm b * e.symm a = e.symm a * e.symm b)
    simp only [map_mul,e.apply_symm_apply] at he
    exact (by decide +kernel : b * a ≠ a * b) he
  apply cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
    (by decide : Odd 3) f hf hr P hP t ht htP R hR
  intro r hr x hx
  have hxt : x = t := hx
  subst x
  exact hc hr t (e.symm a).property

private theorem pow_three_of_twoPerfect_pair
    {D : Type*} [Group D] (hD : IsPPerfect 2 D)
    (f : D →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (hf : Function.Injective f) : ∀ x : D, x ^ 3 = 1 := by
  have hres : pResidual 2 (Equiv.Perm (Fin 3)) ≤ alternatingGroup (Fin 3) := by
    apply sInf_le
    refine ⟨inferInstance,IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 3)).index = 2 ^ 1
    simp
  have he : pResidual 2 D = ⊤ := (pResidual_eq_top_iff 2 D).mpr hD
  have hcoord (q : D →* Equiv.Perm (Fin 3)) (x : D) : q x ^ 3 = 1 := by
    have hx : q x ∈ alternatingGroup (Fin 3) := hres
      (map_pResidual_le 2 q (mem_map_of_mem q (he ▸ mem_top x)))
    have hh := pow_card_eq_one' (x := (⟨q x,hx⟩ : alternatingGroup (Fin 3)))
    have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup,Nat.card_fin]; rfl
    rw [hc] at hh
    exact congrArg Subtype.val hh
  intro x
  apply hf
  rw [map_pow,map_one]
  exact Prod.ext (hcoord ((MonoidHom.fst _ _).comp f) x)
    (hcoord ((MonoidHom.snd _ _).comp f) x)

variable {G : Type*} [Group G] [Finite G]

/-- The full marked centralizer's literal residual has exactly the original
opposite cubic kernel. The three-rank bound is kept on the actual local cover. -/
theorem ThompsonPair.full_image_residual_eq_of_prime_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M) (hn : M ≤ normalizer (V : Set G))
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
    (hthree : s.prime = 3) :
    let ρ := imageRepresentation M V hn
    let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
      (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict)
    let K := subspaceKernel ρ W ⊤
    (pResidual 2 K).map K.subtype =
      (s.marking s.second).kernel.map (c.ambientFactor d s.second).embedding.groupMap ∧
      Nat.card (pResidual 2 K) = s.prime := by
  intro ρ W K
  let D := internalActionImage M V hn
  let F := c.ambientFactor d s.first
  let B := c.ambientFactor d s.second
  let R := (pResidual 2 K).map K.subtype
  let P := (s.marking s.second).kernel.map B.embedding.groupMap
  have hfix : F.space ≤ fixedSpace ρ R :=
    s.full_residual_fixes_first hM.1.2 hn c d π hp hs hJ
  have hKP : K ≤ normalizer (P : Set D) :=
    (s.full_image_residual hM.1.2 hn c d hJ).2.1
  have hKB : K ≤ subspaceStabilizer ρ B.space := by
    rw [←s.kernel_moved s.second]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hKP
  have hRF : R ≤ subspaceStabilizer ρ F.space := by
    apply le_subspaceStabilizer
    intro r hr w hw
    have hrw : ρ r w = w := hfix hw ⟨r,hr⟩
    rwa [hrw]
  have hcompl : IsCompl F.space B.space := by
    have hodd : Odd (Nat.card P) := by rw [s.kernel_card,hthree]; decide
    rw [←s.kernel_fixed s.second s.first s.distinct.symm,←s.kernel_moved s.second]
    simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd)
  let q := (subgroupActionHom ρ B.space K hKB).comp (pResidual 2 K).subtype
  have hq : Function.Injective q := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    apply imageRepresentation_injective M V hn
    have hA : F.space ≤ LinearMap.eqLocus (ρ (x : K)) (ρ (y : K)) := by
      intro w hw
      exact (hfix hw ⟨x,mem_map_of_mem K.subtype x.property⟩).trans
        (hfix hw ⟨y,mem_map_of_mem K.subtype y.property⟩).symm
    have hB : B.space ≤ LinearMap.eqLocus (ρ (x : K)) (ρ (y : K)) := by
      intro w hw
      exact congrArg (fun a => (subspaceImageRepresentation ρ B.space a ⟨w,hw⟩ : Additive V)) he
    have hall : (⊤ : Submodule (ZMod 2) (Additive V)) ≤
        LinearMap.eqLocus (ρ (x : K)) (ρ (y : K)) :=
      hcompl.sup_eq_top ▸ sup_le hA hB
    apply LinearMap.ext
    intro w
    exact hall (Submodule.mem_top)
  obtain ⟨k,J,hk,_,_,hnk,hfull⟩ := B.faithful_normal_support_image_data
    (c.support_stabilizer_normalizes_actor d π hp hs s.second)
  let : k.range.Normal := hnk
  let : FiniteDimensional (ZMod 2) B.space := Module.Finite.of_surjective J.toLinearMap J.surjective
  have hmark := (s.dihedral s.second).dihedral
  rw [hthree] at hmark
  let e := (MonoidHom.ofInjective hk).symm.trans
    (hmark.some.trans nonempty_dihedralThreeEquivPerm.some)
  let σ := subspaceImageRepresentation ρ B.space
  let τ := σ.comp (k.range.subtype.comp e.symm.toMonoidHom)
  have hτ : subspaceCommutator τ ⊤ ⊤ = ⊤ := by
    change subspaceCommutator ((σ.comp k.range.subtype).comp e.symm.toMonoidHom) ⊤ ⊤ = ⊤
    rw [subspaceCommutator_comp_map,map_top_of_surjective _ e.symm.surjective,
      subspaceCommutator_comp_map,←MonoidHom.range_eq_map,k.range.range_subtype]
    exact hfull
  obtain ⟨a,ha,_⟩ := Representation.BinarySymmetricThreeNormalizer.exists_pair_embedding σ
    (subspaceImageRepresentation_injective ρ B.space)
    (J.finrank_eq.symm.trans (s.dihedral s.second).dimension) k.range e
    (Representation.BinarySymmetricThreeNormalizer.fixedFree_of_full τ hτ)
  have hpow : ∀ r : pResidual 2 K, r ^ 3 = 1 :=
    pow_three_of_twoPerfect_pair (isPPerfect_pResidual 2) (a.comp q) (ha.comp hq)
  have hRthree : IsPGroup 3 R :=
    (show IsPGroup 3 (pResidual 2 K) from fun r => ⟨1,hpow r⟩).map K.subtype
  let N := subspaceStabilizer ρ F.space
  have hFN : F.actor ≤ N := by
    apply le_subspaceStabilizer
    rintro g ⟨b,rfl⟩ w ⟨v,rfl⟩
    exact ⟨F.action b v,F.embedding.equivariant b v⟩
  have hNF : N ≤ normalizer (F.actor : Set D) :=
    c.support_stabilizer_normalizes_actor d π hp hs s.first
  have hfaith : ∀ g ∈ F.actor, (∀ w ∈ F.space, ρ g w = w) → g = 1 := by
    rintro g ⟨b,rfl⟩ hb
    have he : F.action b = 1 := by
      ext v
      apply F.embedding.space_injective
      exact (F.embedding.equivariant b v).trans (hb _ ⟨v,rfl⟩)
    have hb1 : b = 1 := F.faithful (he.trans F.action.map_one.symm)
    rw [hb1,map_one]
  have hRC : R ≤ centralizer (F.actor : Set D) := by
    intro r hr
    exact centralizes_of_fixes_faithful_section ρ F.actor F.space hFN hfaith
      (hNF (hRF hr)) (fun w hw => hfix hw ⟨r,hr⟩)
  let H := F.actor.subgroupOf N
  let : H.Normal := normal_subgroupOf_of_le_normalizer hNF
  have hfirst := (s.dihedral s.first).dihedral
  rw [hthree] at hfirst
  let eH : H ≃* Equiv.Perm (Fin 3) := (subgroupOfEquivOfLe hFN).trans
    ((MonoidHom.ofInjective F.embedding.group_injective).symm.trans
      (hfirst.some.trans nonempty_dihedralThreeEquivPerm.some))
  let f := (actionHom M V hn).rangeRestrict
  have hRN : R ≤ N := hRF
  let Rn := R.subgroupOf N
  have hRn : IsPGroup 3 Rn := hRthree.of_equiv (subgroupOfEquivOfLe hRN).symm
  have hRnC : Rn ≤ centralizer (H : Set N) := by
    intro r hr z hz
    exact Subtype.ext (hRC hr z hz)
  have hcyc : IsCyclic Rn := cyclic_of_centralizes_normal_three (A := N.comap f) (D := N)
    (f.subgroupComap N) (f.subgroupComap_surjective_of_surjective N
      (actionHom M V hn).rangeRestrict_surjective)
    ((primeRank_subgroup_le 3 (N.comap f)).trans
      ((hG.twoLocal_sqtk hM.1.1.1).stronglyQuasithin 3 (by decide) (by decide)))
    H eH Rn hRn hRnC
  let er : pResidual 2 K ≃* Rn :=
    (equivMapOfInjective (pResidual 2 K) K.subtype K.subtype_injective).trans
      (subgroupOfEquivOfLe hRN).symm
  let : IsCyclic (pResidual 2 K) := er.isCyclic.mpr hcyc
  have hcard : Nat.card (pResidual 2 K) = s.prime := by
    have hd : Nat.card (pResidual 2 K) ∣ 3 := by
      rw [←IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow
    have hlo := (s.full_image_residual hM.1.2 hn c d hJ).2.2.2
    rw [hthree] at hlo ⊢
    exact Nat.dvd_antisymm hd hlo
  refine ⟨?_,hcard⟩
  apply (eq_of_le_of_card_ge (s.full_image_residual hM.1.2 hn c d hJ).1 ?_).symm
  rw [card_map_of_injective K.subtype_injective,hcard,s.kernel_card]


/-- The prime-three residual calculation descends through the literal
C_M(Z₁)/C_M(V), with the original action kernel. -/
theorem ThompsonPair.full_quotient_residual_card_of_prime_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M) (hn : M ≤ normalizer (V : Set G))
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
    (hthree : s.prime = 3) :
    let Z := thompsonPlane T V (c.ambientFactor d s.first).space
    let C := M ⊓ centralizer (Z : Set G)
    letI := caseI_module_centralizer_normal (Z1 := Z) hn
    Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C)) = s.prime := by
  let ρ := imageRepresentation M V hn
  let W := (c.ambientFactor d s.first).space ⊓ fixedSpace ρ
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict)
  let K := subspaceKernel ρ W ⊤
  let qcard (A : Subgroup G) : ℕ :=
    let C := M ⊓ centralizer (A : Set G)
    letI := caseI_module_centralizer_normal (Z1 := A) hn
    Nat.card (pResidual 2 (C ⧸ (M ⊓ centralizer (V : Set G)).subgroupOf C))
  have hW : plane V W = thompsonPlane T V (c.ambientFactor d s.first).space :=
    plane_thompson_intersection hM.1.2 hn _
  have he : qcard (plane V W) = Nat.card (pResidual 2 K) :=
    ExtraspecialMarker.residual_card M V hn W
  change qcard (thompsonPlane T V (c.ambientFactor d s.first).space) = s.prime
  rw [←congrArg qcard hW,he]
  exact (s.full_image_residual_eq_of_prime_three hG T hM hn c d π hp hs hJ hthree).2


/-- The original action's two-residual lies in the two original cubic
factors. The support-normalizer centralizer is controlled on its literal
preimage in M, so no quotient-rank monotonicity is required. -/
theorem ThompsonPair.image_residual_le_core_of_prime_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hthree : s.prime = 3) :
    pResidual 2 (internalActionImage M V hn) ≤ Jhat (imageRepresentation M V hn) := by
  classical
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let F := c.ambientFactor d s.first
  let B := c.ambientFactor d s.second
  let N := subspaceStabilizer ρ F.space
  have hnπ (g : D) (hg : g ∈ N) : π g = 1 := by
    have hi := c.support_stabilizer_fixes_index d π hs s.first hg
    have hj : π g s.second = s.second := by
      rcases s.covers (π g s.second) with hh | hh
      · exact False.elim (s.distinct ((π g).injective (hi.trans hh.symm)))
      · exact hh
    ext k
    rcases s.covers k with rfl | rfl
    · exact hi
    · exact hj
  have hstab (k : d.Index) : N ≤ subspaceStabilizer ρ (c.ambientFactor d k).space := by
    apply le_subspaceStabilizer
    intro g hg w hw
    have he := hs g k
    rw [hnπ g hg] at he
    exact he ▸ Submodule.mem_map_of_mem hw
  have hFN : F.actor ≤ N := by
    apply le_subspaceStabilizer
    rintro g ⟨a,rfl⟩ w ⟨v,rfl⟩
    exact ⟨F.action a v,F.embedding.equivariant a v⟩
  have hcom : ∀ f ∈ F.actor, ∀ b ∈ B.actor, Commute f b := by
    intro f hf b hb
    simp only [F,B,FactorData.ambientFactor,Factor.map_actor,FactorData.embedding] at hf hb
    obtain ⟨f,hf,rfl⟩ := hf
    obtain ⟨b,hb,rfl⟩ := hb
    exact congrArg (Jhat ρ).subtype (d.actors_commute c.faithful s.distinct hf hb).eq
  have hgen : F.actor ⊔ B.actor = Jhat ρ := by
    rw [←c.ambient_actors_generate d]
    apply le_antisymm
    · exact sup_le (le_iSup (fun k => (c.ambientFactor d k).actor) s.first)
        (le_iSup (fun k => (c.ambientFactor d k).actor) s.second)
    · exact iSup_le fun k => by
        rcases s.covers k with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
  let H := F.actor.subgroupOf N
  let : H.Normal := normal_subgroupOf_of_le_normalizer
    (c.support_stabilizer_normalizes_actor d π hp hs s.first)
  have hfirst := (s.dihedral s.first).dihedral
  rw [hthree] at hfirst
  let eH : H ≃* Equiv.Perm (Fin 3) := (subgroupOfEquivOfLe hFN).trans
    ((MonoidHom.ofInjective F.embedding.group_injective).symm.trans
      (hfirst.some.trans nonempty_dihedralThreeEquivPerm.some))
  let C := centralizer (H : Set N)
  let R := (pResidual 2 C).map C.subtype
  have hcoordinate (k : d.Index) :
      ∀ x : pResidual 2 N,
        (subgroupActionHom ρ (c.ambientFactor d k).space N (hstab k) (x : N)) ^ 3 = 1 := by
    let A := c.ambientFactor d k
    obtain ⟨a,J,ha,_,_,hna,hfull⟩ := A.faithful_normal_support_image_data
      (c.support_stabilizer_normalizes_actor d π hp hs k)
    let : a.range.Normal := hna
    let : FiniteDimensional (ZMod 2) A.space := Module.Finite.of_surjective J.toLinearMap J.surjective
    have hmark := (s.dihedral k).dihedral
    rw [hthree] at hmark
    let e := (MonoidHom.ofInjective ha).symm.trans
      (hmark.some.trans nonempty_dihedralThreeEquivPerm.some)
    let σ := subspaceImageRepresentation ρ A.space
    let τ := σ.comp (a.range.subtype.comp e.symm.toMonoidHom)
    have hτ : subspaceCommutator τ ⊤ ⊤ = ⊤ := by
      change subspaceCommutator ((σ.comp a.range.subtype).comp e.symm.toMonoidHom) ⊤ ⊤ = ⊤
      rw [subspaceCommutator_comp_map,map_top_of_surjective _ e.symm.surjective,
        subspaceCommutator_comp_map,←MonoidHom.range_eq_map,a.range.range_subtype]
      exact hfull
    obtain ⟨b,hb,_⟩ := Representation.BinarySymmetricThreeNormalizer.exists_pair_embedding σ
      (subspaceImageRepresentation_injective ρ A.space)
      (J.finrank_eq.symm.trans (s.dihedral k).dimension) a.range e
      (Representation.BinarySymmetricThreeNormalizer.fixedFree_of_full τ hτ)
    let Q := pResidual 2 (subspaceActionImage ρ A.space)
    have he := pow_three_of_twoPerfect_pair (isPPerfect_pResidual 2)
      (b.comp Q.subtype) (hb.comp Q.subtype_injective)
    intro x
    let q := subgroupActionHom ρ A.space N (hstab k)
    exact congrArg Subtype.val (he ⟨q x,map_pResidual_le 2 q (mem_map_of_mem q x.property)⟩)
  have hpowN : ∀ x : pResidual 2 N, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    apply imageRepresentation_injective M V hn
    have hfix (k : d.Index) : (c.ambientFactor d k).space ≤
        LinearMap.eqLocus (ρ (((x : N) : D) ^ 3)) (ρ 1) := by
      intro w hw
      let q := subgroupActionHom ρ (c.ambientFactor d k).space N (hstab k)
      have he : q ((x : N)^3) = q 1 := by
        simpa only [map_pow,map_one] using hcoordinate k x
      have he' := congrArg (fun a => (subspaceImageRepresentation ρ
        (c.ambientFactor d k).space a ⟨w,hw⟩ : Additive V)) he
      exact he'
    have hspan : F.space ⊔ B.space = ⊤ := by
      have hodd : Odd (Nat.card ((s.marking s.second).kernel.map B.embedding.groupMap)) := by
        rw [s.kernel_card,hthree]; decide
      have hcompl : IsCompl F.space B.space := by
        rw [←s.kernel_fixed s.second s.first s.distinct.symm,←s.kernel_moved s.second]
        simpa only [RegularCyclicNormalClosure.displacementSpan,subspaceCommutator,eq_comm] using
          (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) hodd)
      exact hcompl.sup_eq_top
    have hall : (⊤ : Submodule (ZMod 2) (Additive V)) ≤
        LinearMap.eqLocus (ρ (((x : N) : D) ^ 3)) (ρ 1) :=
      hspan ▸ sup_le (hfix s.first) (hfix s.second)
    change ρ (((x : N) : D)^3) = ρ 1
    apply LinearMap.ext
    intro w
    exact hall (Submodule.mem_top)
  have hpowC : ∀ x : pResidual 2 C, x ^ 3 = 1 := by
    intro x
    have he := hpowN ⟨C.subtype x,map_pResidual_le 2 C.subtype
      (mem_map_of_mem C.subtype x.property)⟩
    exact Subtype.ext (Subtype.ext (congrArg (fun y : pResidual 2 N => (y : N)) he))
  have hRthree : IsPGroup 3 R :=
    (show IsPGroup 3 (pResidual 2 C) from fun r => ⟨1,hpowC r⟩).map C.subtype
  let f := (actionHom M V hn).rangeRestrict
  have hcyc : IsCyclic R := cyclic_of_centralizes_normal_three (A := N.comap f) (D := N)
    (f.subgroupComap N) (f.subgroupComap_surjective_of_surjective N
      (actionHom M V hn).rangeRestrict_surjective)
    ((primeRank_subgroup_le 3 (N.comap f)).trans
      ((hG.twoLocal_sqtk hM.1.1.1).stronglyQuasithin 3 (by decide) (by decide)))
    H eH R hRthree (map_subtype_le _)
  let er : pResidual 2 C ≃* R := equivMapOfInjective _ C.subtype C.subtype_injective
  let : IsCyclic (pResidual 2 C) := er.isCyclic.mpr hcyc
  have hcard : Nat.card R ∣ 3 := by
    rw [card_map_of_injective C.subtype_injective,←IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpowC
  let P := (s.marking s.second).kernel.map B.embedding.groupMap
  have hPN : P ≤ N := by
    apply le_subspaceStabilizer
    intro g hg w hw
    have hw' : w ∈ fixedSpace ρ P :=
      (s.kernel_fixed s.second s.first s.distinct.symm).symm ▸ hw
    have he : ρ g w = w := hw' ⟨g,hg⟩
    rwa [he]
  let Pn := P.subgroupOf N
  have hPnC : Pn ≤ C := by
    intro b hb a ha
    exact Subtype.ext (hcom a ha b (map_le_range _ _ hb)).eq
  have hPR : Pn ≤ R := by
    intro p hp
    let x : C := ⟨p,hPnC hp⟩
    have hc : Nat.Coprime (orderOf x) 2 := by
      have he : orderOf x = orderOf (⟨p,hp⟩ : Pn) := by
        rw [←orderOf_injective C.subtype C.subtype_injective x,
          ←orderOf_injective Pn.subtype Pn.subtype_injective ⟨p,hp⟩]
        rfl
      rw [he]
      apply Nat.Coprime.of_dvd_left (orderOf_dvd_natCard _)
      rw [Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv,s.kernel_card,hthree]
      decide
    exact mem_map_of_mem C.subtype (mem_pResidual_of_orderOf_coprime hc.symm)
  have hRP : R = Pn := by
    apply (eq_of_le_of_card_ge hPR ?_).symm
    rw [Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv,s.kernel_card,hthree]
    exact Nat.le_of_dvd (by decide) hcard
  have hRN : (pResidual 2 N).map N.subtype ≤ Jhat ρ := by
    rw [←embedded_pResidual_sup_eq_of_normal_sup_top 2 H C
      (NormalSymmetricThree.sup_centralizer_eq_top H eH),Subgroup.map_sup]
    apply sup_le
    · exact (map_mono (map_subtype_le _)).trans
        ((map_subgroupOf_eq_of_le hFN).le.trans (hgen ▸ le_sup_left))
    · change R.map N.subtype ≤ Jhat ρ
      rw [hRP,map_subgroupOf_eq_of_le hPN]
      exact (map_le_range _ _).trans (hgen ▸ le_sup_right)
  have hI : Nat.card d.Index = 2 := by
    refine Nat.card_eq_two_iff.mpr ⟨s.first,s.second,s.distinct,?_⟩
    exact Set.eq_univ_iff_forall.mpr (fun k => by simpa using s.covers k)
  have hπ : IsPGroup 2 (Equiv.Perm d.Index) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_perm,hI]; rfl)
  have hDN : pResidual 2 D ≤ N := by
    apply le_subspaceStabilizer
    intro g hg w hw
    have he := hs g s.first
    rw [show π g = 1 from pResidual_le_ker_of_isPGroup 2 π hπ hg] at he
    exact he ▸ Submodule.mem_map_of_mem hw
  intro x hx
  apply hRN
  let j := inclusion hDN
  have ht : pResidual 2 (pResidual 2 D) = ⊤ :=
    (pResidual_eq_top_iff 2 _).mpr (isPPerfect_pResidual 2)
  exact mem_map_of_mem N.subtype (map_pResidual_le 2 j
    (mem_map_of_mem j (ht ▸ mem_top (⟨x,hx⟩ : pResidual 2 D))))

/-- The original marked centralizer and the original Sylow subgroup generate
M in the prime-three branch. The factor exchange supplies both factors,
and the residual calculation supplies their Sylow supplement. -/
theorem ThompsonPair.generation_of_prime_three
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hthree : s.prime = 3) :
    M = (M ⊓ centralizer
      (thompsonPlane T V (c.ambientFactor d s.first).space : Set G)) ⊔ (T : Subgroup G) := by
  classical
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f := (actionHom M V hn).rangeRestrict
  let F := c.ambientFactor d s.first
  let B := c.ambientFactor d s.second
  let W := F.space ⊓ fixedSpace ρ
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f)
  let K := subspaceKernel ρ W ⊤
  let S := ((T : Subgroup G).subgroupOf M).map f
  let L := K ⊔ S
  have hBK : B.actor ≤ K := by
    intro b hb
    refine ⟨mem_top b,fun w hw => ?_⟩
    exact c.ambient_cross d s.distinct hw.1 ⟨b,hb⟩
  obtain ⟨t,ht,htn⟩ : ∃ t ∈ (T : Subgroup G),
      t ∉ normalizer (plane V F.space : Set G) := by
    by_contra! he
    have hi := s.stabilizer_index
    rw [inf_eq_left.mpr he,relIndex_self] at hi
    norm_num at hi
  let tM : M := ⟨t,hM.1.2 ht⟩
  have hts : f tM ∈ S := mem_map_of_mem f ht
  have hswap : π (f tM) s.second = s.first := by
    apply c.ambient_spaces_injective d
    apply plane_injective V
    have hmap := plane_conjugate hn B.space tM
    have he := (s.exchanges t ht htn).2
    exact (congrArg (plane V) (hs (f tM) s.second)).symm.trans (hmap.symm.trans he)
  have hFL : F.actor ≤ L := by
    have he := hp (f tM) s.second
    rw [hswap] at he
    rw [←he]
    rintro x ⟨b,hb,rfl⟩
    exact L.mul_mem (L.mul_mem ((show S ≤ L from le_sup_right) hts)
      ((show K ≤ L from le_sup_left) (hBK hb)))
      (L.inv_mem ((show S ≤ L from le_sup_right) hts))
  have hJL : Jhat ρ ≤ L := by
    rw [←c.ambient_actors_generate d]
    apply iSup_le
    intro k
    rcases s.covers k with rfl | rfl
    · exact hFL
    · exact hBK.trans le_sup_left
  let Q : Sylow 2 D := (T.subtype hM.1.2).mapSurjective
    (actionHom M V hn).rangeRestrict_surjective
  have htop : L = ⊤ := by
    apply top_unique
    rw [←pResidual_sup_sylow_eq_top Q]
    exact sup_le ((s.image_residual_le_core_of_prime_three hG T hM hn c d π hp hs hthree).trans hJL)
      (show (Q : Subgroup D) ≤ L from le_sup_right)
  have hW : plane V W = thompsonPlane T V F.space :=
    plane_thompson_intersection hM.1.2 hn F.space
  have he := (ExtraspecialMarker.fixed_and_generation T hM.1.2 hn W inf_le_right htop).2
  change M = (M ⊓ centralizer (plane V W : Set G)) ⊔ (T : Subgroup G) at he
  rwa [hW] at he

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
